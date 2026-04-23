import Lake
open Lake DSL

package "SCPRG" where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  --moreLeanArgs := #["--Wno-unused"]
  -- add any additional package configuration options here

require "leanprover-community" / "mathlib"


@[default_target]
lean_lib «SymbolicGarbledCircuitsInLean» where
  -- add any library configuration options here

lean_lib «PRGExtension» where
  -- add any library configuration options here
