# Typo review control

You are the orchestrator for a typo review. Read `README.md`, then follow this file. Do not edit source files before the apply step.

## Scope

Review only **Git-tracked Typst chapter sources**. Build the review list from the Git index, not a filesystem glob:

```bash
git ls-files -z -- 'etale-c*.typ'
```

Exclude every untracked file, including ignored historical copies such as `*-defunct*.typ`. Git tracking determines eligibility; a matching filename or an existing file is not sufficient. Review the current working-tree contents of the eligible files.

Before resuming a review, remove out-of-scope entries from findings, checked versions, vetoes, and their associated decisions, raw results, and renders. Preserve in-scope decisions and do not delete source files. Recheck eligibility before dispatching, merging, rendering, or applying findings.

## State

Maintain `qa/checked_versions.json`:

```json
{
  "etale-c1s0.typ": {
    "blob": "<git hash-object output>",
    "checked_commit": "<commit checked>",
    "checked_at": "2026-11-15T12:00:00"
  }
}
```

For each tracked `etale-c*.typ` file selected above:

- if the current blob matches the stored blob, skip it;
- if there is no entry, review the whole file;
- otherwise use `git diff <checked_commit> -- <file>` to get the changed line spans and review only those;
- update the entry after the file is fully reviewed.

## Review one file

1. Read the whole file before doing anything else.
2. Dispatch `allocate.md` to a subagent:
   - **6.2 Sol, Extra high**;
   - give it the whole file and the changed line spans;
   - require logical ranges that cover every changed line;
   - if its output is invalid, use one range covering the changed spans.
3. For each range, dispatch:
   - `surface.md` — **6.2 Sol, High**;
   - `math.md` — **6.2 Sol, Extra high**.

   Give each subagent the **whole file**, not only the range, and tell it to report only inside its range. Run the two passes in parallel. Save raw output under `qa/raw/`.
4. Validate each finding: its file must still be Git-tracked and in scope; `old` must occur verbatim in the file and its line must be in the range. Drop invalid entries.
5. Dispatch `verify-math.md` to a separate **6.2 Sol, Extra high** subagent:
   - give it the whole file and all math findings for that file;
   - keep `confirm`, remove `veto`;
   - write vetoed entries to `qa/vetoed/vetoed.json`.
6. Merge the surviving surface and math findings into `qa/findings.json` and update `checked_versions.json`.

## Render

After writing findings:

```bash
python3 tools/qa_render.py --findings qa/findings.json
```

This compiles original and patched section previews, locates the target with Typst `locate()`, and writes `qa/renders/<id>-old.png` / `-new.png`.

## Review

Start the GUI:

```bash
python3 tools/qa_gui.py --findings qa/findings.json --decisions qa/decisions.json
```

Report the URL to the author. Do not accept or reject findings on the author's behalf. The author uses **F** to accept and **J** to reject, and may leave comments.

The source diff shows complete affected lines with five surrounding lines on each side and line numbers. The author can expand the context to 10 or 20 lines per side, or the whole file.

## Apply

After every finding has a decision, dispatch `apply.md` per file:

- Extra high for files containing math findings, High for surface-only files;
- comments override `new`;
- rejected findings are untouched;
- skip conflicts and report them.

Do not commit or push.

## Rules

- No source edits during discovery.
- Every range must produce a result, including `{"findings": []}`.
- Do not invent line numbers or quotes.
- Math reviewers must give a reason.
