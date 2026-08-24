# Arena benchmark ledger

This is the corpus: every model-brief-PR-verdict row this program has
produced. The table IS the deliverable — "see what new models can do" shows
up here, accumulating over time.

Verdict discipline:
- Only CI-graded verdicts count. A row is `PENDING` until the harness says
  GREEN/RED. No human "looks good".
- A brief whose proof-assumption is prose-only is RED, by definition of the
  grader (see ARENA_BRIEF_001).
- Separate *incident* (harness broke, runner lost) from *verdict* (the model's
  approach failed the grader). A RED verdict is a research result, not a bug.

| # | brief | model | PR | verdict |
|---|-------|-------|----|---------|
| 1 | ARENA_BRIEF_001 (T1+T2, Lean lane) | — | — | pending |

## Note on brief archival

Per the Arena-brief convention, in-flight briefs start untracked and land as
historical snapshots after their PR merges. In this public benchmark repo the
briefs catalog *is* the product, so they are committed in-repo up front (the
ask + acceptance bar is publicly inspectable); the ledger row and the docs
carry the live outcome. If a brief is later corrected, the correction is
co-metadata here — never silent rewrite of the ask.