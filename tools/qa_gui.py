#!/usr/bin/env python3
"""Local review UI for typo and math findings.

Usage:
    python3 tools/qa_gui.py --findings qa/findings.json --decisions qa/decisions.json

The server binds to 127.0.0.1 by default. Findings are never modified; only
qa/decisions.json is written. Press F to accept and J to reject.
"""
from __future__ import annotations

import argparse
import difflib
import html
import json
import os
import subprocess
import sys
import threading
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.parse import parse_qs, urlparse

ROOT = Path(__file__).resolve().parent.parent
LOCK = threading.Lock()
FINDINGS_PATH = ROOT / "qa" / "findings.json"
DECISIONS_PATH = ROOT / "qa" / "decisions.json"
RENDER_DIR = ROOT / "qa" / "renders"


def load_findings() -> list[dict]:
    raw = json.loads(FINDINGS_PATH.read_text(encoding="utf-8"))
    items = raw.get("findings", raw) if isinstance(raw, dict) else raw
    if not isinstance(items, list):
        raise SystemExit("findings.json must contain a list or {'findings': [...]}")
    normalized = []
    for i, item in enumerate(items, 1):
        item = dict(item)
        item.setdefault("id", f"finding-{i}")
        item.setdefault("file", "(unknown)")
        item.setdefault("line_start", 0)
        item.setdefault("line_end", item["line_start"])
        item.setdefault("severity", "unknown")
        item.setdefault("category", "uncategorized")
        item.setdefault("pass", "unknown")
        item.setdefault("old", "")
        item.setdefault("new", "")
        item.setdefault("reason", "")
        normalized.append(item)
    return normalized


def load_decisions() -> dict:
    if not DECISIONS_PATH.exists():
        return {}
    try:
        return json.loads(DECISIONS_PATH.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return {}


def save_decisions(data: dict) -> None:
    DECISIONS_PATH.parent.mkdir(parents=True, exist_ok=True)
    tmp = DECISIONS_PATH.with_suffix(".json.tmp")
    tmp.write_text(json.dumps(data, ensure_ascii=False, indent=2), encoding="utf-8")
    os.replace(tmp, DECISIONS_PATH)


def diff_parts(old: str, new: str) -> tuple[list, list]:
    sm = difflib.SequenceMatcher(None, old, new, autojunk=False)
    left, right = [], []
    for tag, i1, i2, j1, j2 in sm.get_opcodes():
        if tag == "equal":
            left.append((old[i1:i2], None))
            right.append((new[j1:j2], None))
        else:
            left.append((old[i1:i2], "del"))
            right.append((new[j1:j2], "ins"))
    return left, right


def diff_html(old: str, new: str) -> tuple[str, str]:
    def render(parts):
        return "".join(f"<{tag}>{html.escape(text)}</{tag}>" if tag else html.escape(text)
                       for text, tag in parts if text)
    left, right = diff_parts(old, new)
    return render(left), render(right)


def numbered_source_html(parts: list, first_line: int) -> tuple[str, int]:
    rows: list[list[str]] = [[]]
    changed = [False]
    ends_with_newline = False
    for text, tag in parts:
        if text:
            ends_with_newline = text.endswith("\n")
        chunks = text.split("\n")
        for i, chunk in enumerate(chunks):
            if tag and (chunk or i < len(chunks) - 1 or not text):
                changed[-1] = True
            if chunk:
                escaped = html.escape(chunk)
                rows[-1].append(f"<{tag}>{escaped}</{tag}>" if tag else escaped)
            if i < len(chunks) - 1:
                rows.append([])
                changed.append(False)
    if ends_with_newline and len(rows) > 1 and not rows[-1] and not changed[-1]:
        rows.pop()
        changed.pop()
    result = []
    for i, row in enumerate(rows):
        number = first_line + i
        css = "source-line changed" if changed[i] else "source-line"
        result.append(f'<div class="{css}" data-line="{number}">'
                      f'<span class="line-number" aria-hidden="true">{number}</span>'
                      f'<span class="line-code">{"".join(row) or "<br>"}</span></div>')
    return "".join(result), first_line + len(rows) - 1


def source_context(item: dict, source: str, context_lines: int | None = 5) -> dict:
    """Patch the exact recorded occurrence, retaining unchanged surrounding text."""
    lines = source.splitlines(keepends=True)
    start, end = int(item["line_start"]) - 1, int(item["line_end"])
    if not 0 <= start < end <= len(lines):
        raise ValueError("Recorded lines are outside the current file. Showing the original quote.")
    old = item.get("old", "")
    scope = "".join(lines[start:end])
    if not old or scope.count(old) != 1:
        raise ValueError("The quote no longer matches uniquely at its recorded lines. Showing the original quote.")
    before = 0 if context_lines is None else max(0, start - context_lines)
    after = len(lines) if context_lines is None else min(len(lines), end + context_lines)
    offset = scope.index(old)
    prefix = "".join(lines[before:start]) + scope[:offset]
    suffix = scope[offset + len(old):] + "".join(lines[end:after])
    left, right = diff_parts(old, item.get("new", ""))
    left_html, old_end = numbered_source_html([(prefix, None), *left, (suffix, None)], before + 1)
    right_html, new_end = numbered_source_html([(prefix, None), *right, (suffix, None)], before + 1)
    return {"old_html": left_html, "new_html": right_html, "line_start": before + 1,
            "old_line_end": old_end, "new_line_end": new_end, "total_lines": len(lines)}


def load_source_context(item: dict, context_lines: int | None = 5) -> dict:
    path = (ROOT / item["file"]).resolve()
    if ROOT not in path.parents or path.suffix != ".typ":
        raise ValueError("Source context is available only for tracked Typst files in this repository.")
    tracked = subprocess.run(["git", "ls-files", "--error-unmatch", "--", str(path.relative_to(ROOT))],
                             cwd=ROOT, capture_output=True)
    if tracked.returncode:
        raise ValueError("This source file is no longer Git-tracked. Showing the original quote.")
    return source_context(item, path.read_text(encoding="utf-8"), context_lines)


def item_for_client(item: dict, decisions: dict) -> dict:
    out = dict(item)
    dec = decisions.get(item["id"], {})
    out["decision"] = dec.get("decision", "pending")
    out["comment"] = dec.get("comment", "")
    out["old_html"], out["new_html"] = diff_html(item.get("old", ""), item.get("new", ""))
    return out


HTML = r"""<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Typo review</title>
<style>
:root { --bg:#f5f6f8; --card:#fff; --ink:#1f2328; --muted:#69707a; --line:#e3e6e9;
        --red:#b42318; --redbg:#fef3f2; --green:#067647; --greenbg:#ecfdf3; --blue:#175cd3; }
* { box-sizing:border-box; }
body { margin:0; background:var(--bg); color:var(--ink);
       font:15px/1.55 -apple-system,BlinkMacSystemFont,"Segoe UI","Noto Sans",sans-serif; }
header { position:sticky; top:0; z-index:5; background:rgba(255,255,255,.97);
         border-bottom:1px solid var(--line); padding:12px 18px; display:flex; gap:14px;
         align-items:center; flex-wrap:wrap; }
h1 { font-size:17px; margin:0; }
.progress { color:var(--muted); font-variant-numeric:tabular-nums; }
.pill { border-radius:999px; padding:2px 8px; font-size:12px; background:#eef4ff; color:var(--blue); }
main { max-width:1180px; margin:16px auto 88px; padding:0 16px; }
.card { background:var(--card); border:1px solid var(--line); border-radius:10px; padding:14px 16px; margin-bottom:12px; }
.meta { display:flex; gap:10px; flex-wrap:wrap; color:var(--muted); font-size:13px; margin-bottom:8px; }
.meta b { color:var(--ink); }
.grid { display:grid; grid-template-columns:1fr 1fr; gap:10px; }
.grid > div { min-width:0; }
.label { font-size:12px; color:var(--muted); margin:6px 0 4px; }
.text { white-space:pre-wrap; overflow-wrap:anywhere; border-radius:7px; padding:9px 10px;
        font-family:"SFMono-Regular",Consolas,"Liberation Mono",monospace; font-size:13.5px; }
.old { background:var(--redbg); border:1px solid #fecdca; }
.new { background:var(--greenbg); border:1px solid #abefc6; }
del { background:#fda29b; color:#7a271a; text-decoration:line-through; }
ins { background:#75e0a7; color:#054f31; text-decoration:none; }
.source-toolbar { display:flex; align-items:center; gap:10px; flex-wrap:wrap; margin:8px 0; }
.source-context { padding:0; white-space:normal; background:#fff; max-height:36rem; overflow:auto; }
.source-line { display:grid; grid-template-columns:3.5em minmax(0,1fr); }
.line-number { color:var(--muted); user-select:none; text-align:right; padding:0 8px;
               border-right:1px solid var(--line); font-variant-numeric:tabular-nums; }
.line-code { display:block; white-space:pre-wrap; overflow-wrap:anywhere; padding:0 8px; }
.old .source-line.changed { background:var(--redbg); }
.new .source-line.changed { background:var(--greenbg); }
.source-line.changed .line-number { color:var(--ink); }
.reason { white-space:pre-wrap; color:#344054; }
textarea { width:100%; min-height:72px; resize:vertical; padding:9px 10px; border:1px solid var(--line);
           border-radius:7px; font:14px/1.5 inherit; }
.actions { position:fixed; left:0; right:0; bottom:0; background:rgba(255,255,255,.97);
           border-top:1px solid var(--line); padding:10px 16px; display:flex; gap:9px;
           justify-content:center; flex-wrap:wrap; }
button, select { border:1px solid var(--line); border-radius:7px; padding:9px 14px; background:#fff;
                 font:14px inherit; cursor:pointer; }
button.accept { background:#079455; color:#fff; border-color:#079455; }
button.reject { background:#d92d20; color:#fff; border-color:#d92d20; }
button:disabled { opacity:.45; cursor:not-allowed; }
.hint { color:var(--muted); font-size:12px; }
.done { text-align:center; padding:36px 12px; }
.done h2 { margin:0 0 8px; }
img.render { max-width:100%; border:1px solid var(--line); border-radius:6px; background:#fff; }
</style>
</head>
<body>
<header>
  <h1>Typo review</h1>
  <span class="progress" id="progress">loading…</span>
  <span class="pill" id="counts"></span>
  <span class="hint" id="review-status"></span>
  <span class="hint">F accept · J reject · ←/→ navigate</span>
</header>
<main>
  <div class="card" style="display:flex;gap:10px;flex-wrap:wrap">
    <select id="filter-pass"><option value="">all passes</option></select>
    <select id="filter-severity"><option value="">all severities</option></select>
    <select id="filter-file"><option value="">all files</option></select>
    <select id="sort">
      <option value="surface">surface first</option>
      <option value="severity">severity first</option>
      <option value="file">file / line</option>
    </select>
  </div>
  <div id="app"></div>
</main>
<div class="actions" id="actions" style="display:none">
  <button class="reject" id="reject">Reject (J)</button>
  <button class="accept" id="accept">Accept (F)</button>
  <button id="prev">Previous (←)</button>
  <button id="save">Save comment</button>
  <button id="next">Next (→)</button>
</div>
<script>
let items = [], view = [], idx = 0, reviewStatus = null;
let contextLines = '5', contextRequest = 0;
const app = document.getElementById('app');
const actions = document.getElementById('actions');
const rank = {typo:0, grammar:1, 'minor-math':2, 'serious-math':3, unknown:9};

function esc(s) { return String(s ?? '').replace(/[&<>"']/g, c => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c])); }
function counts() {
  const a = items.filter(x=>x.decision==='accepted').length;
  const r = items.filter(x=>x.decision==='rejected').length;
  const p = items.length-a-r;
  document.getElementById('counts').textContent = `accepted ${a} · rejected ${r} · pending ${p}`;
}
function filtered() {
  const pass = document.getElementById('filter-pass').value;
  const sev = document.getElementById('filter-severity').value;
  const file = document.getElementById('filter-file').value;
  const sort = document.getElementById('sort').value;
  let out = items.filter(x => (!pass || x.pass===pass) && (!sev || x.severity===sev) && (!file || x.file===file));
  if (sort === 'surface') out.sort((a,b)=>(rank[a.severity]??9)-(rank[b.severity]??9) || a.file.localeCompare(b.file) || a.line_start-b.line_start);
  if (sort === 'severity') out.sort((a,b)=>(rank[a.severity]??9)-(rank[b.severity]??9) || a.file.localeCompare(b.file));
  if (sort === 'file') out.sort((a,b)=>a.file.localeCompare(b.file) || a.line_start-b.line_start);
  return out;
}
function refreshView(keepId) {
  const oldId = keepId ?? view[idx]?.id;
  view = filtered();
  if (oldId) { const n = view.findIndex(x=>x.id===oldId); idx = n >= 0 ? n : 0; }
  else { idx = Math.min(idx, Math.max(0, view.length-1)); }
  if (view.length && view[idx]?.decision !== 'pending') {
    const n = view.findIndex((x,i)=>i>idx && x.decision==='pending');
    if (n >= 0) idx = n;
    else { const any = view.findIndex(x=>x.decision==='pending'); if (any >= 0) idx = any; }
  }
}
function render() {
  contextRequest++;
  counts();
  const reviewRunning = reviewStatus && reviewStatus.files_reviewed < reviewStatus.total_files;
  document.getElementById('review-status').textContent = reviewRunning
    ? `Review in progress: ${reviewStatus.files_reviewed} / ${reviewStatus.total_files} files verified. Refresh for new findings.` : '';
  const pending = items.filter(x=>x.decision==='pending').length;
  document.getElementById('progress').textContent = `${items.length - pending} / ${items.length} reviewed`;
  if (!items.length) {
    app.innerHTML = `<div class="card">${reviewRunning ? 'Review is running. Refresh for new findings.' : 'No findings.'}</div>`;
    return;
  }
  if (!view.length) { actions.style.display='none'; app.innerHTML = '<div class="card done"><h2>No findings in this filter</h2></div>'; return; }
  if (!pending) {
    actions.style.display='none';
    app.innerHTML = `<div class="card done"><h2>${reviewRunning ? 'Current findings reviewed' : 'Review complete'}</h2>
      <p>${items.length} findings reviewed. ${reviewRunning ? 'The review is still running; refresh for new findings.' : 'Run the apply agent next.'}</p></div>`;
    return;
  }
  if (idx < 0) idx = 0;
  if (idx >= view.length) idx = view.length - 1;
  const it = view[idx];
  const renderBlock = (it.render && (it.render.old || it.render.new))
    ? `<div class="label">Rendered</div><div class="grid">
         <div>${it.render.old ? `<img class="render" src="/api/render?path=${encodeURIComponent(it.render.old)}">` : ''}</div>
         <div>${it.render.new ? `<img class="render" src="/api/render?path=${encodeURIComponent(it.render.new)}">` : ''}</div>
       </div>` : (it.render_error
         ? `<p class="hint">${it.render_error.includes('commented-out')
             ? 'This finding is in commented-out source; review the source diff.'
             : 'Rendered preview unavailable; review the source diff.'}</p>` : '');
  app.innerHTML = `
    <div class="card">
      <div class="meta">
        <span><b>${esc(it.file)}</b> · ${it.line_start}${it.line_end && it.line_end!==it.line_start ? '–'+it.line_end : ''}</span>
        <span class="pill">${esc(it.pass)}</span>
        <span class="pill">${esc(it.severity)}</span>
        <span>${esc(it.category)}</span>
        <span>${esc(it.confidence || '')}</span>
        <span>${idx+1} / ${view.length}</span>
        <span>${esc(it.decision)}</span>
      </div>
      <div class="source-toolbar">
        <label for="context-lines">Source context</label>
        <select id="context-lines">
          <option value="5">5 lines each side</option>
          <option value="10">10 lines each side</option>
          <option value="20">20 lines each side</option>
          <option value="all">Whole file</option>
        </select>
        <span class="hint" id="context-note" role="status">Loading surrounding source…</span>
      </div>
      <div class="grid">
        <div><div class="label" id="source-old-label">Source · old</div><div class="text old" id="source-old">${it.old_html}</div></div>
        <div><div class="label" id="source-new-label">Source · new${it.new ? '' : ' · no direct replacement'}</div><div class="text new" id="source-new">${it.new_html || '<i>(no direct replacement)</i>'}</div></div>
      </div>
      <div class="label">Reason</div><div class="reason">${esc(it.reason)}</div>
      ${renderBlock}
      <div class="label">Comment (used by the apply agent)</div>
      <textarea id="comment" placeholder="Optional: describe the exact change you want.">${esc(it.comment || '')}</textarea>
    </div>`;
  actions.style.display='flex';
  const contextSelect = document.getElementById('context-lines');
  contextSelect.value = contextLines;
  contextSelect.onchange = ()=>{ contextLines = contextSelect.value; loadSourceContext(it); };
  loadSourceContext(it);
}

async function loadSourceContext(it) {
  const request = ++contextRequest;
  document.getElementById('context-note').textContent = 'Loading surrounding source…';
  try {
    const params = new URLSearchParams({id:it.id, lines:contextLines});
    const response = await fetch('/api/context?' + params, {cache:'no-store'});
    const data = await response.json();
    if (request !== contextRequest || selected()?.id !== it.id) return;
    if (!response.ok) throw new Error(data.error || 'Source context unavailable. Showing the original quote.');
    for (const side of ['old', 'new']) {
      const panel = document.getElementById('source-' + side);
      panel.classList.add('source-context');
      panel.innerHTML = data[side + '_html'];
      document.getElementById('source-' + side + '-label').textContent =
        `Source · ${side} · lines ${data.line_start}–${data[side + '_line_end']}`
        + (side === 'new' && !it.new ? ' · no direct replacement' : '');
      const change = panel.querySelector('.changed');
      if (change) panel.scrollTop += change.getBoundingClientRect().top - panel.getBoundingClientRect().top - panel.clientHeight / 3;
    }
    document.getElementById('context-note').textContent = `Showing original lines ${data.line_start}–${data.old_line_end} of ${data.total_lines}.`;
  } catch (error) {
    if (request !== contextRequest || selected()?.id !== it.id) return;
    for (const side of ['old', 'new']) {
      const panel = document.getElementById('source-' + side);
      panel.classList.remove('source-context');
      panel.innerHTML = it[side + '_html'] || '<i>(no direct replacement)</i>';
      document.getElementById('source-' + side + '-label').textContent = `Source · ${side}`;
    }
    document.getElementById('context-note').textContent = error.message;
  }
}
async function load() {
  const r = await fetch('/api/findings', {cache:'no-store'});
  const raw = await r.json();
  items = raw.findings;
  reviewStatus = raw.review_status ?? null;
  for (const key of ['filter-pass','filter-severity','filter-file']) {
    const sel = document.getElementById(key);
    const field = key.replace('filter-','');
    const values = [...new Set(items.map(x=>x[field]))].filter(Boolean).sort();
    for (const v of values) { const o=document.createElement('option'); o.value=v; o.textContent=v; sel.appendChild(o); }
  }
  refreshView();
  render();
}
function selected() { return view[idx]; }
async function decide(decision) {
  const it = selected(); if (!it) return;
  const comment = document.getElementById('comment').value;
  const r = await fetch('/api/decision', {method:'POST', headers:{'Content-Type':'application/json'},
    body: JSON.stringify({id:it.id, decision, comment})});
  if (!r.ok) { alert(await r.text()); return; }
  it.decision = decision; it.comment = comment;
  const next = view.findIndex((x,i)=>i>idx && x.decision==='pending');
  if (next >= 0) idx = next;
  else { const any = items.findIndex(x=>x.decision==='pending'); if (any >= 0) { view = filtered(); idx = view.findIndex(x=>x.id===items[any].id); } }
  render();
}
async function saveComment() {
  const it = selected(); if (!it) return;
  const comment = document.getElementById('comment').value;
  await fetch('/api/comment', {method:'POST', headers:{'Content-Type':'application/json'},
    body: JSON.stringify({id:it.id, comment})});
  it.comment = comment;
  document.getElementById('save').textContent = 'Saved';
  setTimeout(()=>document.getElementById('save').textContent='Save comment', 800);
}
document.getElementById('accept').onclick = ()=>decide('accepted');
document.getElementById('reject').onclick = ()=>decide('rejected');
document.getElementById('save').onclick = saveComment;
document.getElementById('prev').onclick = ()=>{ if(idx>0){idx--; render();} };
document.getElementById('next').onclick = ()=>{ if(idx<view.length-1){idx++; render();} };
for (const id of ['filter-pass','filter-severity','filter-file','sort']) {
  document.getElementById(id).onchange = ()=>{ refreshView(); render(); };
}
document.addEventListener('keydown', e=>{
  if (e.target && ['TEXTAREA','INPUT','SELECT'].includes(e.target.tagName)) return;
  if (e.key==='f'||e.key==='F') { e.preventDefault(); decide('accepted'); }
  if (e.key==='j'||e.key==='J') { e.preventDefault(); decide('rejected'); }
  if (e.key==='ArrowLeft') { e.preventDefault(); if(idx>0){idx--; render();} }
  if (e.key==='ArrowRight') { e.preventDefault(); if(idx<view.length-1){idx++; render();} }
});
load();
</script>
</body>
</html>"""


class Handler(BaseHTTPRequestHandler):
    def _send(self, code: int, body: str | bytes, ctype: str = "application/json; charset=utf-8") -> None:
        data = body.encode("utf-8") if isinstance(body, str) else body
        self.send_response(code)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(data)))
        self.send_header("Cache-Control", "no-store")
        self.end_headers()
        self.wfile.write(data)

    def _payload(self) -> dict:
        n = int(self.headers.get("Content-Length", "0"))
        return json.loads(self.rfile.read(n) or b"{}")

    def do_GET(self) -> None:
        parsed = urlparse(self.path)
        if parsed.path == "/":
            self._send(200, HTML, "text/html; charset=utf-8")
        elif parsed.path == "/api/findings":
            decisions = load_decisions()
            items = [item_for_client(x, decisions) for x in load_findings()]
            result = {"findings": items}
            progress_path = FINDINGS_PATH.parent / "raw" / "progress.json"
            if progress_path.exists():
                try:
                    progress = json.loads(progress_path.read_text(encoding="utf-8"))
                    result["review_status"] = {"files_reviewed": len(progress["complete"]),
                                               "total_files": progress["total"]}
                except (OSError, ValueError, KeyError, TypeError):
                    pass
            self._send(200, json.dumps(result, ensure_ascii=False))
        elif parsed.path == "/api/context":
            params = parse_qs(parsed.query)
            item_id = params.get("id", [""])[0]
            item = next((x for x in load_findings() if x["id"] == item_id), None)
            if item is None:
                self._send(404, json.dumps({"error": "Finding not found."}))
                return
            try:
                requested = params.get("lines", ["5"])[0]
                context_lines = None if requested == "all" else int(requested)
                if context_lines is not None and not 0 <= context_lines <= 100:
                    raise ValueError("Choose between 0 and 100 context lines, or the whole file.")
                context = load_source_context(item, context_lines)
            except (OSError, ValueError, TypeError) as exc:
                self._send(409, json.dumps({"error": str(exc)}))
                return
            self._send(200, json.dumps(context, ensure_ascii=False))
        elif parsed.path == "/api/render":
            rel = parse_qs(parsed.query).get("path", [""])[0]
            path = (RENDER_DIR / rel).resolve()
            if RENDER_DIR.resolve() not in path.parents or not path.is_file():
                self._send(404, "not found", "text/plain; charset=utf-8")
                return
            data = path.read_bytes()
            ctype = "image/png" if path.suffix.lower() == ".png" else "application/octet-stream"
            self._send(200, data, ctype)
        else:
            self._send(404, "not found", "text/plain; charset=utf-8")

    def do_POST(self) -> None:
        path = urlparse(self.path).path
        try:
            payload = self._payload()
        except (ValueError, json.JSONDecodeError):
            self._send(400, "bad json", "text/plain; charset=utf-8")
            return
        with LOCK:
            decisions = load_decisions()
            item_id = payload.get("id")
            if not item_id:
                self._send(400, "missing id", "text/plain; charset=utf-8")
                return
            old = decisions.get(item_id, {})
            if path == "/api/decision":
                decision = payload.get("decision")
                if decision not in ("accepted", "rejected", "pending"):
                    self._send(400, "bad decision", "text/plain; charset=utf-8")
                    return
                old["decision"] = decision
                old["comment"] = payload.get("comment", "")
            elif path == "/api/comment":
                old["comment"] = payload.get("comment", "")
                old.setdefault("decision", "pending")
            else:
                self._send(404, "not found", "text/plain; charset=utf-8")
                return
            decisions[item_id] = old
            save_decisions(decisions)
        self._send(200, json.dumps({"ok": True}))

    def log_message(self, fmt: str, *args) -> None:
        pass


def main() -> None:
    global FINDINGS_PATH, DECISIONS_PATH, RENDER_DIR
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--findings", default=str(FINDINGS_PATH))
    parser.add_argument("--decisions", default=str(DECISIONS_PATH))
    parser.add_argument("--render-dir", default=str(RENDER_DIR))
    parser.add_argument("--host", default="127.0.0.1")
    parser.add_argument("--port", type=int, default=8769)
    args = parser.parse_args()
    FINDINGS_PATH = Path(args.findings).expanduser().resolve()
    DECISIONS_PATH = Path(args.decisions).expanduser().resolve()
    RENDER_DIR = Path(args.render_dir).expanduser().resolve()
    if not FINDINGS_PATH.is_file():
        raise SystemExit(f"missing findings file: {FINDINGS_PATH}")
    print(f"Typo review: http://{args.host}:{args.port}/", flush=True)
    ThreadingHTTPServer((args.host, args.port), Handler).serve_forever()


if __name__ == "__main__":
    main()
