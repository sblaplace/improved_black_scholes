/-!
# ImprovedBS

Root module of the `ImprovedBS` library. Modules imported here are built by
`lake build`.

* `ImprovedBS.Core` — the BSM closed form and the theorem stack T1..T6.

## Why the module is not called `Lean.*`

The formalization previously lived at `Lean/core/bsm_theorems.lean`. With the
library root at the repository root, that makes the module name
`Lean.core.bsm_theorems` — which squats the `Lean` namespace that the
elaborator, the `Lean.Elab` machinery and every tactic implementation live in.
Importing such a module into a file that also uses tactics is a source of
elaboration-order surprises that have nothing to do with the mathematics.
`scripts/lean_lint.py` fails CI if a `.lean` file reappears under a top-level
`Lean/` directory.
-/

import ImprovedBS.Core
