# Allocate review ranges

Only allocate Git-tracked Typst source files within `CONTROL.md`'s scope. Confirm tracking with `git ls-files --error-unmatch -- <file>`; do not allocate an untracked file.

Read the entire file before deciding on boundaries.

Partition the file into logical ranges for reviewers. Ranges are reporting scopes only: every reviewer receives the whole file, so a range boundary must not cut a definition, theorem, or proof away from what it depends on.

Guidelines:

- Cover every line exactly once, with no gaps or overlaps.
- Prefer definition / theorem / proof boundaries.
- Do not split inside a display formula.
- Range length is not fixed; follow the material. However, it is discouraged to have a range longer than a page of rendered text.
- If a logical unit is too large, splitting inside the proof is acceptable.

Return only JSON:

```json
{
  "file": "etale-c2s5.typ",
  "ranges": [
    {
      "id": "c2s5-01",
      "start": 1,
      "end": 118,
      "reason": "Henselization: definition and first properties, sharing the same notation."
    }
  ]
}
```
