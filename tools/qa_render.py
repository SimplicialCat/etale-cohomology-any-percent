#!/usr/bin/env python3
"""Render before/after Typst crops for QA findings.

The renderer compiles a single-section preview twice (original and patched),
uses Typst metadata + locate() to find the target page and position, then
crops that page with pdftoppm. Results are written next to findings as
qa/renders/<id>-old.png and qa/renders/<id>-new.png.
"""
from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
QA = ROOT / "qa"
FINDINGS = QA / "findings.json"
RENDERS = QA / "renders"
TMP = QA / ".render-tmp"


def run(cmd: list[str], cwd: Path = ROOT) -> subprocess.CompletedProcess:
    return subprocess.run(cmd, cwd=cwd, text=True, capture_output=True, check=False)


def load_findings() -> list[dict]:
    raw = json.loads(FINDINGS.read_text(encoding="utf-8"))
    return raw.get("findings", raw) if isinstance(raw, dict) else raw


def in_comment(text: str, offset: int) -> bool:
    """Recognize nested comments while ignoring strings and raw text."""
    depth, i = 0, 0
    while i < offset:
        pair = text[i:i + 2]
        if depth:
            if pair == "/*":
                depth += 1
                i += 2
            elif pair == "*/":
                depth -= 1
                i += 2
            else:
                i += 1
        elif pair == "//":
            end = text.find("\n", i)
            if end < 0 or end >= offset:
                return True
            i = end + 1
        elif pair == "/*":
            depth = 1
            i += 2
        elif text[i] == '"':
            i += 1
            while i < offset:
                if text[i] == "\\":
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
        elif text[i] == "`":
            end = i
            while end < len(text) and text[end] == "`":
                end += 1
            close = text.find(text[i:end], end)
            i = close + (end - i) if close >= 0 else offset
        elif text[i] == "\\":
            i += 2
        else:
            i += 1
    return depth > 0


def make_tree(dest: Path) -> None:
    dest.mkdir(parents=True, exist_ok=True)
    for item in ROOT.iterdir():
        if item.name in {".git", ".build", "qa", "old_sources", "extract"}:
            continue
        if item.name.startswith(".qa-"):
            continue
        target = dest / item.name
        if target.exists() or target.is_symlink():
            continue
        os.symlink(item, target)


def safe_id(value: str) -> str:
    return re.sub(r"[^A-Za-z0-9_-]", "-", value)


def marker(kind: str, finding_id: str) -> str:
    safe = safe_id(finding_id)
    # Embed markup so labels are also parsed correctly inside math mode.
    return f'#[#metadata(("{safe}", "{kind}")) <qa-{safe}>] '


def add_markers(text: str, finding: dict, side: str) -> tuple[str, list[str]]:
    lines = text.splitlines()
    start = max(1, int(finding.get("line_start") or 1))
    end = max(start, int(finding.get("line_end") or start))
    if start > len(lines):
        raise RuntimeError("line range outside file")
    if lines[start - 1].lstrip().startswith("//"):
        raise RuntimeError("target is commented-out source; review the source diff")
    if re.match(r"\s*(?:node|edge)\d*\s*\(", lines[start - 1]):
        # Diagram arguments are code, where a markup marker is not legal.
        # Locate the enclosing diagram instead and show its larger crop.
        for candidate in range(start - 2, -1, -1):
            if re.search(r"#.*\b(?:diagram|commute)\b", lines[candidate]) and not lines[candidate].lstrip().startswith("//"):
                start = candidate + 1
                break
    start_id = safe_id(f"{finding['id']}-{side}-start")
    line = lines[start - 1]
    indent = len(line) - len(line.lstrip())
    needle = finding.get("old" if side == "old" else "new", "")
    needle_column = line.find(needle.splitlines()[0]) if needle else -1
    if needle_column >= 0:
        comment_end = line.rfind("*/", 0, needle_column)
        if comment_end >= 0:
            indent = max(indent, comment_end + 2)
    # Preserve list and heading syntax when the reported line begins a block.
    prefix = re.match(r"(?:[-+/]|\d+\.|=+)\s+", line[indent:])
    if prefix:
        indent += prefix.end()
    lines[start - 1] = line[:indent] + marker("start", start_id) + line[indent:]
    # Only the start location is queried. An end marker can be swallowed by a
    # line comment or change the meaning of a trailing math line-break escape.
    return "\n".join(lines) + "\n", [start_id]


def patch_text(text: str, finding: dict) -> str:
    old, new = finding.get("old", ""), finding.get("new", "")
    if not old:
        raise RuntimeError("empty old text")
    lines = text.splitlines(keepends=True)
    start = int(finding["line_start"]) - 1
    end = int(finding.get("line_end") or start + 1)
    if not 0 <= start < end <= len(lines):
        raise RuntimeError("line range outside file")
    scope = "".join(lines[start:end])
    if old not in scope:
        raise RuntimeError("old text not found in reported lines")
    return "".join(lines[:start]) + scope.replace(old, new, 1) + "".join(lines[end:])


def wrapper(section: str, markers: list[str]) -> str:
    ctx = "\n".join(
        f'''#context {{
  let loc = locate(<qa-{m}>)
  let pos = loc.position()
  let value = (page: counter(page).at(loc).first(), pos: (x: pos.x / 1pt, y: pos.y / 1pt))
  [#metadata(value) <qa-loc-{m}>]
  pdf.attach("qa-loc-{m}.json", bytes(json.encode(value)), mime-type: "application/json")
}}'''
        for m in markers
    )
    return f'''#import "void-import.typ": *
#show: void-style
#bibliography("references.bib", style: "void-custom-cite.csl")
#include "{section}"

{ctx}
'''


def query_location(wrapper_path: Path, marker_id: str, pdf: Path | None = None) -> dict:
    # The location is attached by the same compilation that produced the PDF.
    # Reading it avoids recompiling the whole section just to run a query.
    if pdf is not None and shutil.which("pdfdetach"):
        location_file = wrapper_path.parent / f"qa-loc-{marker_id}.json"
        p = run(["pdfdetach", "-savefile", location_file.name, "-o", str(location_file), str(pdf)])
        if p.returncode == 0 and location_file.exists():
            return json.loads(location_file.read_text(encoding="utf-8"))
    p = run(["typst", "query", str(wrapper_path), f"<qa-loc-{marker_id}>", "--field", "value"])
    if p.returncode:
        raise RuntimeError(f"typst query failed: {p.stderr.strip()[:500]}")
    data = json.loads(p.stdout)
    if not data:
        raise RuntimeError("no location result")
    value = data[0]
    if isinstance(value, dict) and "value" in value:
        value = value["value"]
    return value


def number(value) -> float:
    if isinstance(value, (int, float)):
        return float(value)
    return float(re.sub(r"[^0-9.+-]", "", str(value)))


def crop(pdf: Path, page: int, y_pt: float, out: Path, height: int = 300) -> None:
    scale = 2.0  # 144 dpi
    y = max(0, int((number(y_pt) - 55) * scale))
    cmd = [
        "pdftoppm", "-f", str(page), "-l", str(page), "-r", "144",
        "-x", "0", "-y", str(y), "-W", "1400", "-H", str(height),
        "-png", "-singlefile", str(pdf), str(out.with_suffix("")),
    ]
    p = run(cmd)
    if p.returncode or not out.exists():
        # Fall back to a full-page screenshot.
        p = run(["pdftoppm", "-f", str(page), "-l", str(page), "-r", "144",
                 "-png", "-singlefile", str(pdf), str(out.with_suffix(""))])
        if p.returncode:
            raise RuntimeError(f"pdftoppm failed: {p.stderr.strip()[:500]}")


def render_one(finding: dict, force: bool = False) -> Path | None:
    fid = finding.get("id")
    section = finding.get("file")
    if not fid or not section:
        return None
    if not section.endswith(".typ") or run(["git", "ls-files", "--error-unmatch", "--", section]).returncode:
        raise RuntimeError("source must be a Git-tracked Typst file")
    source = (ROOT / section).read_text(encoding="utf-8")
    lines = source.splitlines(keepends=True)
    start = int(finding["line_start"]) - 1
    end = int(finding.get("line_end") or start + 1)
    scope = "".join(lines[start:end])
    offset_in_scope = scope.find(finding.get("old", ""))
    if offset_in_scope >= 0:
        offset = sum(len(line) for line in lines[:start]) + offset_in_scope
        if in_comment(source, offset) or source[offset:offset + 2] in ("//", "/*"):
            raise RuntimeError("target is commented-out source; review the source diff")
    old_out = RENDERS / f"{fid}-old.png"
    new_out = RENDERS / f"{fid}-new.png"
    if not force and old_out.exists() and new_out.exists():
        finding.setdefault("render", {"old": old_out.name, "new": new_out.name})
        return old_out
    TMP.mkdir(parents=True, exist_ok=True)
    work = Path(tempfile.mkdtemp(prefix=safe_id(fid) + "-", dir=TMP))
    make_tree(work)
    try:
        original, ids = add_markers(source, finding, "old")
        target = work / section
        if target.is_symlink():
            target.unlink()
        target.write_text(original, encoding="utf-8")
        old_wrapper = work / ".qa-old.typ"
        old_wrapper.write_text(wrapper(section, ids), encoding="utf-8")
        old_pdf = work / "old.pdf"
        p = run(["typst", "compile", "--root", str(work), str(old_wrapper), str(old_pdf)], cwd=work)
        if p.returncode:
            raise RuntimeError(f"old compile failed: {p.stderr.strip()[:500]}")
        old_loc = query_location(old_wrapper, ids[0], old_pdf)
        new_finding = dict(finding)
        new_finding["line_end"] = max(
            int(finding["line_start"]),
            int(finding.get("line_end") or finding["line_start"])
            + finding.get("new", "").count("\n") - finding.get("old", "").count("\n"),
        )
        patched_source = patch_text(source, finding)
        # Removing a final passage can remove its target line entirely. Keep
        # a blank preview-only anchor at the deletion position in that case.
        while len(patched_source.splitlines()) < int(new_finding["line_start"]):
            patched_source += "\n"
        patched, new_ids = add_markers(patched_source, new_finding, "new")
        target = work / section
        if target.is_symlink():
            target.unlink()
        target.write_text(patched, encoding="utf-8")
        new_wrapper = work / ".qa-new.typ"
        new_wrapper.write_text(wrapper(section, new_ids), encoding="utf-8")
        new_pdf = work / "new.pdf"
        p = run(["typst", "compile", "--root", str(work), str(new_wrapper), str(new_pdf)], cwd=work)
        if p.returncode:
            raise RuntimeError(f"new compile failed: {p.stderr.strip()[:500]}")
        new_loc = query_location(new_wrapper, new_ids[0], new_pdf)
        RENDERS.mkdir(parents=True, exist_ok=True)
        target_line = source.splitlines()[int(finding["line_start"]) - 1]
        height = 600 if re.match(r"\s*(?:node|edge)\d*\s*\(", target_line) else 300
        old_png, new_png = work / "old.png", work / "new.png"
        crop(old_pdf, int(old_loc["page"]), number(old_loc["pos"]["y"]), old_png, height)
        crop(new_pdf, int(new_loc["page"]), number(new_loc["pos"]["y"]), new_png, height)
        old_png.replace(old_out)
        new_png.replace(new_out)
        finding["render"] = {"old": old_out.name, "new": new_out.name,
                             "old_page": old_loc["page"], "new_page": new_loc["page"]}
        return old_out
    finally:
        shutil.rmtree(work, ignore_errors=True)


def main() -> None:
    global FINDINGS, RENDERS
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--findings", default=str(FINDINGS))
    parser.add_argument("--out", default=str(RENDERS))
    parser.add_argument("--only", help="render one finding id")
    parser.add_argument("--force", action="store_true")
    args = parser.parse_args()
    FINDINGS = Path(args.findings).expanduser().resolve()
    RENDERS = Path(args.out).expanduser().resolve()
    findings = load_findings()
    if args.only:
        findings = [f for f in findings if f.get("id") == args.only]
    ok = 0
    for f in findings:
        try:
            if render_one(f, args.force):
                f.pop("render_error", None)
                ok += 1
                print(f"rendered {f['id']}", flush=True)
        except Exception as exc:
            f.pop("render", None)
            f["render_error"] = str(exc)
            print(f"skip {f.get('id')}: {exc}", file=sys.stderr, flush=True)
    # Write updated render fields back.
    all_findings = load_findings()
    by_id = {f.get("id"): f for f in all_findings}
    for f in findings:
        if f.get("render"):
            by_id[f["id"]].update(render=f["render"])
            by_id[f["id"]].pop("render_error", None)
        elif f.get("render_error"):
            by_id[f["id"]].pop("render", None)
            by_id[f["id"]]["render_error"] = f["render_error"]
    save = FINDINGS
    tmp = save.with_suffix(save.suffix + ".tmp")
    tmp.write_text(json.dumps({"findings": list(by_id.values())}, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    os.replace(tmp, save)
    print(f"done: {ok} rendered", flush=True)


if __name__ == "__main__":
    main()
