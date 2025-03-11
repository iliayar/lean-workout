import Lake
open Lake DSL

package "workout" where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

require "leanprover-community" / "mathlib"

require batteries from git "https://github.com/leanprover/batteries" @ "main"

@[default_target]
lean_lib «Workout» where
  -- add any library configuration options here
