# Ledger

Every PR landed against a brief gets a row here. The deliverable is the
verified theorem stack; this table is the record of how it was reached —
including the approaches that failed the grader.

Verdict discipline:
- Only CI-graded verdicts count. A row is `PENDING` until the harness says
  GREEN/RED. No human "looks good".
- A brief whose proof is asserted but not checker-backed (a stray `sorry`)
  is RED, by definition of the grader (see BRIEF_001).
- Separate *incident* (harness broke, runner lost) from *verdict* (the
  approach failed the grader). A RED verdict is a result, not a bug report.

| # | brief | contributor | PR | verdict |
|---|-------|-------------|----|---------|
| 1 | BRIEF_001 (T1+T2, Lean lane) | — | — | pending |

## Note on brief archival

Briefs are committed in-repo up front: the ask and the acceptance bar are
publicly inspectable before any PR exists, and the ledger carries the live
outcome. If a brief is later corrected, the correction is co-recorded here —
never a silent rewrite of the ask.
