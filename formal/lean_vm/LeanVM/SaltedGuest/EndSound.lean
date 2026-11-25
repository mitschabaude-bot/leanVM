/-
  LeanVM.SaltedGuest.EndSound

  B2 for the salted bytecode, from its certificates (`Sound.lean`) and B1's obligations at the
  checked windows' cuts, and the salted guest's knowledge soundness from the open per-function
  obligations.
-/

module

public import LeanVM.SaltedGuest.EndKnow
public import LeanVM.SaltedGuest.Sound

/-!
# B2, and the salted guest's soundness from its open obligations

* `b2SoundL_of`: B2 (`B2SoundL`, checker K's `b2_step` and `b2_mainL` over the kernel-checked
  certificates of the salted bytecode, `Checked.all_ok`), from the four facts about the core IR
  that the checked windows' cuts take: `ExpTablesSound` (`exponent_tables`' returns are the
  exponent tables), `VsDimsKnown` and `VsKnown` (`verify_sub`'s `dims_g[g^0]` and `kappa_base`
  bounds, its first `560` and `1635` statements), `WalkKnown` (the windowed Merkle walks and the
  GKR layer loop).
* `Obligations dec`: those four and `main`'s (`MainSound dec`): **the per-function obligations
  still open**, each a statement about the salted core IR (`coreProgram.Rel`) alone.
* `knowledgeSound`: from the open obligations and the decoder program's (`DecoderComputes`), the
  salted guest `⟨guestProgram, decoder, sizeBound, budget⟩` is knowledge sound
  (`Recursion.Salted.SaltedGuest.KnowledgeSound`).
-/

namespace LeanVM.SaltedGuest.End

open LeanVM.Guest
open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Node Recursion.Salted

@[expose] public section

/-- **B2 for the salted bytecode**, from B1's facts at the checked windows' cuts. -/
theorem b2SoundL_of (hexp : ExpTablesSound) (hvd : VsDimsKnown) (hvs : VsKnown)
    (hwalk : WalkKnown) : B2SoundL :=
  ⟨b2_step fun _ h2 hj ↦ cutsKnown_of hvd hvs hwalk h2 hj, b2_mainL hexp⟩

/-- **The salted guest's open per-function obligations**, for `main`'s decoding `dec`: each a
statement about the salted core IR alone (B1). -/
structure Obligations (dec : Val → Reader → FrameMap → SaltedDecoding) : Prop where
  /-- `exponent_tables`' returned pointer holds the exponent table. -/
  expTables : ExpTablesSound
  /-- `verify_sub`'s first `560` statements bound entry `0` of `dims_g` below `g^34`. -/
  vsDims : VsDimsKnown
  /-- `verify_sub`'s first `1635` statements bound the `8` entries of `kappa_base`. -/
  vs : VsKnown
  /-- The walks' cut obligations: the windowed Merkle walks and the GKR layer loop. -/
  walks : WalkKnown
  /-- `main`'s meaning: the decoding explains the public input under its second digest. -/
  main : MainSound dec

/-- **The salted guest is knowledge sound**, from its open per-function obligations and the
decoder program's. -/
theorem knowledgeSound {dec : Val → Reader → FrameMap → SaltedDecoding}
    {decoder : Cost.MachineProgram} {sizeBound : ℕ} {budget : Execution guestProgram → ℕ}
    (h : Obligations dec) (hd : DecoderComputes decoder sizeBound budget dec) :
    (⟨guestProgram, decoder, sizeBound, budget⟩ : SaltedGuest).KnowledgeSound :=
  knowledgeSound_of_b2 (b2SoundL_of h.expTables h.vsDims h.vs h.walks) h.main hd

end
end LeanVM.SaltedGuest.End
