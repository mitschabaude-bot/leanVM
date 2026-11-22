/-
  The input of `scripts/decoder-tables --salted`, from the built modules: the line `entries: …`
  (`--entries`). Run from lean_vm after `lake build`: `lake env lean
  scripts/decoder-tables-inputs-salted.lean`.
-/
import LeanVM.SaltedGuest.Glob
open LeanVM.SaltedGuest
#eval IO.println s!"entries: {(List.range nFns).map fun j ↦ (fnOf j).entryPc}"
