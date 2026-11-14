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
    return f'#metadata(("{safe}", "{kind}")) <qa-{safe}>'


def add_markers(text: str, finding: dict, side: str) -> tuple[str, list[str]]:
    lines = text.splitlines()
    start = max(1, int(finding.get("line_start") or 1))
    end = max(start, int(finding.get("line_end") or start))
    if start > len(lines):
        raise RuntimeError("line range outside file")
    start_id = safe_id(f"{finding['id']}-{side}-start")
    end_id = safe_id(f"{finding['id']}-{side}-end")
    lines[start - 1] = marker("start", start_id) + lines[start - 1]
    lines[min(end, len(lines)) - 1] = lines[min(end, len(lines)) - 1] + marker("end", end_id)
    return "\n".join(lines) + "\n", [start_id, end_id]


def patch_text(text: str, finding: dict) -> str:
    old, new = finding.get("old", ""), finding.get("new", "")
    if not old:
        raise RuntimeError("empty old text")
    if old not in text:
        raise RuntimeError("old text not found")
    return text.replace(old, new, 1)


def wrapper(section: str, markers: list[str]) -> str:
    ctx = "\n".join(
        f'''#context {{
  let loc = locate(<qa-{m}>)
  [#metadata((page: counter(page).at(loc).first(), pos: loc.position())) <qa-loc-{m}>]
}}'''
        for m in markers
    )
    return f'''#import "void-import.typ": *
#show: void-style
#bibliography("references.bib", style: "void-custom-cite.csl")
#include "{section}"

{ctx}
'''


def query_location(wrapper_path: Path, marker_id: str) -> dict:
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


def crop(pdf: Path, page: int, y_pt: float, out: Path) -> None:
    scale = 2.0  # 144 dpi
    y = max(0, int((number(y_pt) - 55) * scale))
    cmd = [
        "pdftoppm", "-f", str(page), "-l", str(page), "-r", "144",
        "-x", "0", "-y", str(y), "-W", "1400", "-H", "300",
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
    old_out = RENDERS / f"{fid}-old.png"
    new_out = RENDERS / f"{fid}-new.png"
    if not force and old_out.exists() and new_out.exists():
        return old_out
    work = TMP / re.sub(r"[^A-Za-z0-9_.-]", "_", fid)
    if work.exists():
        shutil.rmtree(work)
    make_tree(work)
    source = (ROOT / section).read_text(encoding="utf-8")
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
        old_loc = query_location(old_wrapper, ids[0])
        patched, new_ids = add_markers(patch_text(source, finding), finding, "new")
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
        new_loc = query_location(new_wrapper, new_ids[0])
        RENDERS.mkdir(parents=True, exist_ok=True)
        crop(old_pdf, int(old_loc["page"]), number(old_loc["pos"]["y"]), old_out)
        crop(new_pdf, int(new_loc["page"]), number(new_loc["pos"]["y"]), new_out)
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
                ok += 1
                print(f"rendered {f['id']}", flush=True)
        except Exception as exc:
            print(f"skip {f.get('id')}: {exc}", file=sys.stderr, flush=True)
    # Write updated render fields back.
    all_findings = load_findings()
    by_id = {f.get("id"): f for f in all_findings}
    for f in findings:
        if f.get("render"):
            by_id[f["id"]].update(render=f["render"])
    save = FINDINGS
    save.write_text(json.dumps({"findings": list(by_id.values())}, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"done: {ok} rendered", flush=True)


if __name__ == "__main__":
    main()
