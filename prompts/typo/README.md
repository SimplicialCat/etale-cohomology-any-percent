# Typo review prompts

This directory contains the review protocol for the English source. The goal is to find typos, English errors, and mathematical errors without editing the source during review.

## Files

- `allocate.md` — partition a file into logical review ranges.
- `surface.md` — spelling, grammar, punctuation.
- `math.md` — mathematical errors, both minor and serious.
- `verify-math.md` — independent check of math findings; may veto false positives.
- `apply.md` — apply reviewed decisions after the author has seen every finding.

## Models

Use Codex with ChatGPT models:

- `allocate`, `math`, `verify-math`: **6.1 Sol (Extra high)**
- `surface`: **6.1 Sol (High)**
- `apply`: High for surface-only changes; Extra high if any math is involved

## Review flow

1. `allocate` reads the whole file and returns logical line ranges.
2. `surface` and `math` each read the **whole file**, but report only inside their assigned range.
3. `verify-math` reads the whole file, confirms or vetoes each math candidate.
4. The author reviews every surviving finding in the GUI.
5. `apply` applies accepted changes and comments.

## Review UI

```bash
python3 tools/qa_gui.py --findings qa/findings.json --decisions qa/decisions.json
```

`F` accepts, `J` rejects. Findings can be filtered and sorted by pass or severity. Optional `render.old` / `render.new` images are served from `qa/renders/`.

Do not edit source files during steps 1–4. Do not run a separate mechanical spellcheck pass; these prompts are the review.

## Finding format

```json
{
  "id": "c2s5-017",
  "pass": "math",
  "file": "etale-c2s5.typ",
  "range_id": "c2s5-02",
  "line_start": 322,
  "line_end": 324,
  "severity": "serious-math",
  "category": "wrong-object",
  "old": "Pick a primitive element $L = k(alpha)$",
  "new": "Pick a primitive element $alpha$ so that $L = k(alpha)$",
  "reason": "The primitive element is alpha, not the field L.",
  "confidence": "high",
  "model": "6.1 Sol",
  "effort": "extra-high"
}
```

`old` must occur verbatim in the file. Every finding needs a concise reason.
