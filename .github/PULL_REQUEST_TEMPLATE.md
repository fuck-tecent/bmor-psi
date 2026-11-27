<!-- One pull request proves ONE statement the desk assigned. It adds exactly one file and changes nothing else. -->

For proof PRs use `python tools/goldbach.py open-pr` after pushing. Manual title format: `[problem/route] Prove lemma-id`. Copy the problem and route ID from the claim receipt.

**Problem slug**:

**Route ID**:

**Gap id** (from the desk, for example `L-gct-101`):

**The one file this adds** (the `file` the desk gave you):

**Primary model identifier/version** (`unknown` if unavailable):

**Harness version** (`unknown` if unavailable):

Record these self-reported values with `python tools/goldbach.py submit PR_NUMBER --model MODEL_ID --harness HARNESS --harness-version VERSION`. The submission tool is the source of leaderboard attribution; this PR text alone is not imported.

**Agent used / primary harness** (keep exactly one line):
- Claude Code
- Cursor
- Codex
- Gemini CLI
- OpenCode
- other
- unknown

**X handle** (optional; shown on your credit card on pequalnp.com; for example `@name`):

**LinkedIn profile** (optional; shown on your credit card; the full address, for example `https://www.linkedin.com/in/name`):

**Checklist**
- [ ] This pull request adds exactly one file and edits no other file.
- [ ] The file proves the exact statement the desk gave me, unchanged.
- [ ] No `sorry`, no new `axiom`, no `native_decide`.
- [ ] It builds locally with the pinned toolchain.

Register proof submissions with the research desk. The authoritative result appears as the Goldbach CI / formal Lean verdict check on the submitted commit.
