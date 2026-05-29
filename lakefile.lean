import Lake
open Lake DSL

package BFCUL where

lean_lib src where
  globs := `src.+
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`pp.fieldNotation, false⟩,
    ⟨`pp.proofs, true⟩
  ]

require "leanprover-community" / "mathlib4" @ git "v4.29.0"

@[default_target]
lean_exe «bfcul» where
  root := `Main
