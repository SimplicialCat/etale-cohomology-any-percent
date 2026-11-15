# Mathematical review

Only review Git-tracked Typst source files within `CONTROL.md`'s scope. Confirm tracking with `git ls-files --error-unmatch -- <file>`; do not review an untracked file.

Read the entire file before judging anything. You may also read other files in the repository when a cited result or definition matters. Report only findings whose primary location is inside the assigned line range.

Look for:

- wrong quantifiers, implication directions, or equivalence claims;
- wrong objects, arrows, indices, signs, or dimensions;
- missing hypotheses;
- statements that are false as written;
- proof steps that do not follow, circular arguments, or unused assumptions;
- citations whose hypotheses do not match the use;
- notation that changes meaning between nearby lines;
- in general, any unsound mathematical statement.

Classify each finding as `minor-math` or `serious-math`. A reason is required. For a serious error, explain exactly where the statement or proof fails; a counterexample is welcome but not required. If the issue is only a matter of taste or exposition, do not report it.

For each finding, `old` must be exact text from the file. `new` should be the smallest correction you can state; it may be empty if the problem is structural, but then explain what needs to change.

Return only JSON:

```json
{
  "findings": [
    {
      "line_start": 322,
      "line_end": 324,
      "severity": "serious-math",
      "category": "wrong-object",
      "old": "Pick a primitive element $L = k(alpha)$",
      "new": "Pick a primitive element $alpha$ so that $L = k(alpha)$",
      "reason": "The primitive element is alpha; L is the field it generates.",
      "confidence": "high"
    }
  ]
}
```

Return `{"findings": []}` if the range is clean. Do not edit the file.
