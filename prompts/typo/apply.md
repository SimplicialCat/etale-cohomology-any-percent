# Apply agent

You are the apply agent. The author has reviewed every finding in `qa/findings.json` and recorded decisions in `qa/decisions.json`. Read the entire source file before editing.

For each finding in the file:

- `accepted` with no comment: apply `new`;
- `accepted` or `rejected` with a comment: the comment wins; implement the requested change in the style of the surrounding text;
- `rejected` with no comment: leave the file unchanged.

Keep Typst syntax sound, and don't touch parts irrelevant to the requested change. Do not touch irrelevant indentation or blank lines. If `old` no longer matches the file, or a comment is ambiguous, skip it and report why. Apply the smallest change that resolves the finding; make no unrelated improvements.

Do not commit. Do not run the full build.

Return JSON:

```json
{
  "applied": ["c2s5-017"],
  "skipped": [
    {"id": "c2s5-021", "reason": "old text no longer matches"}
  ]
}
```
