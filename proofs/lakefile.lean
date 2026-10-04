import Lake
open Lake DSL

package «kala-azar-7d-proofs» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.16.0"

@[default_target]
lean_lib «KalaAzarModelDoubleLatency» where
  srcDir := "."
