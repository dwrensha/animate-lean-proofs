import Lake
open Lake DSL

package «animate» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

@[default_target]
lean_lib Annotations

@[default_target]
lean_lib Input

@[default_target]
lean_lib StringMatching

@[default_target]
lean_lib HighlightSyntax

@[default_target]
lean_lib Chess

@[default_target]
lean_exe «Animate» where
  -- Enables the use of the Lean interpreter by the executable (e.g.,
  -- `runFrontend`) at the expense of increased binary size on Linux.
  -- Remove this line if you do not need such functionality.
  supportInterpreter := true

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.10.0"
