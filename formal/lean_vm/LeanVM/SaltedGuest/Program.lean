/-
  LeanVM.SaltedGuest.Program

  The salted aggregation guest's leanISA program, assembled from its generated data.
-/

module

public import LeanVM.SaltedGuest.Data.Bytecode

/-!
# The salted guest program

`guestProgram` is the salted `rec_aggregation::unified_guest()`'s bytecode: the compiled functions
of `LeanVM.SaltedGuest.Data.functions` (generated from leanVM's sources by `scripts/guest-export`,
whose `--check` fails when they are stale), laid out from pc `0` and padded with `SET fp[0] = 0`
to `2^19` instructions, as `LeanVM.Guest.guestProgram` is the deployed guest's.
-/

namespace LeanVM.SaltedGuest

@[expose] public section

/-- **The salted leanISA guest program**, assembled from `LeanVM/SaltedGuest/Data/`. -/
def guestProgram : LeanVM.Semantics.LeanIsaProgram :=
  LeanVM.Guest.assemble Data.functions 19 (by decide)

end
end LeanVM.SaltedGuest
