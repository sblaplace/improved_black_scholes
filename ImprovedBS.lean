import ImprovedBS.Core

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

## Note on this file's shape

The `import` must come first. A module doc-comment — the bang form of Lean's
block comment — is a *command*, not a comment, so placing it above the `import`
produces

    error: invalid 'import' command, it must be used in the beginning of the file

which is exactly what the first CI run of this repository reported. Ordinary
block comments and line comments are fine before imports; doc-comments are not,
and neither is this file's previous shape.

(No literal comment delimiters are written in this docstring on purpose: Lean
block comments nest, and an unbalanced pair inside prose would close the
comment early and turn the rest of the file into syntax errors.)
-/
