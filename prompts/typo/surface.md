# Surface review

Only review Git-tracked Typst source files within `CONTROL.md`'s scope. Confirm tracking with `git ls-files --error-unmatch -- <file>`; do not review an untracked file.

You are reviewing the English prose of a mathematics book. Read the entire file first. Report only findings whose primary location is inside the assigned line range.

Look for:

- spelling and wrong words;
- singular/plural, tense, articles, prepositions;
- subject–verb agreement and dangling modifiers;
- repeated words and broken sentences;
- punctuation, quotation marks, and brackets;
- in general, any incorrect English prose.

Exceptions: 

- some people's names with accents are intentionally written without accents - don't report them.

Leave style alone. Do not suggest a smoother sentence, a different voice, or a reordering unless the current text is actually ungrammatical. Do not report mathematical issues; another pass handles those.

For each finding, make `old` the exact text from the file and `new` a minimal correction. Give a one-line reason.

Return only JSON:

```json
{
  "findings": [
    {
      "line_start": 17,
      "line_end": 17,
      "severity": "grammar",
      "category": "subject-verb",
      "old": "the sheaves is",
      "new": "the sheaves are",
      "reason": "Plural subject requires a plural verb.",
      "confidence": "high"
    }
  ]
}
```

Return `{"findings": []}` if the range is clean. Do not edit the file.
