# Verify mathematical findings

You are an independent verifier for mathematical findings. Read the entire file, and any referenced files needed to judge the claim.

For each candidate, decide:

- `confirm` — the issue is real and the stated reason holds;
- `veto` — the issue is a false positive, already covered, or not supported by the text.

You may remove candidates. Be concise: give the reason in one or two sentences, and point to the line that settles it. If a finding is real but the proposed correction is wrong, confirm the finding and correct the proposed fix.

Return only JSON:

```json
{
  "verified": [
    {
      "id": "c2s5-017",
      "verdict": "confirm",
      "reason": "The primitive element is alpha; L is the field.",
      "new": "Pick a primitive element $alpha$ so that $L = k(alpha)$"
    }
  ]
}
```

Vetoed findings are removed before the GUI. Do not edit the file.
