/-
  LeanVM.SaltedGuest.EndKnow

  The salted guest's knowledge soundness from B2 and its open obligations: `main`'s meaning over
  the core IR, and a decoder program that computes the decoding.
-/

module

public import LeanVM.SaltedGuest.EndLoc
public import LeanVM.Salted.Node

/-!
# The salted guest's soundness, its obligations named

B2 (`B2SoundL`, the kernel-checked certificates of the salted bytecode against its core IR)
locates `main`'s body at its frame on every valid execution (`mainBodyL_of`). What it does not
give, the per-function meanings of the core IR (B1), is named here as hypotheses:

* `MainSound dec`: **`main`'s obligation**. Over any call relation below the salted core IR's
  that unfolds along a frame map (`UnfoldsV`), on a memory whose words `0` and `1` hold a digest
  `D` and whose words `2` and `3` hold a digest `S`, a run of `main`'s body gives, read off its
  frame by `dec`, the seed `S`, a statement whose salted digest under `S` is `D`, and a witness
  that satisfies the salted node relation under `S` with at most `16` children. It rests on every
  callee's meaning (`…_sound_Spec` at the salted core IR), as the deployed guest's
  `B1.Main.main_sound_V_of_sub` does.
* `DecoderComputes decoder sizeBound budget dec`: the decoder program of the cost machine
  outputs, within its size bound and budget on every valid execution, the encoding of `dec`'s
  decoding off the execution's memory and frame map (`decodeWith dec`).

`knowledgeSound_of_b2`: from B2, `main`'s obligation and the decoder's, the salted guest
`⟨guestProgram, decoder, sizeBound, budget⟩` is knowledge sound
(`Recursion.Salted.SaltedGuest.KnowledgeSound`). The memory words `2` and `3` that `main`'s
obligation reads are the second digest of the public input, which `ValidExecution₂` puts there
(`second_loads`).
-/

namespace LeanVM.SaltedGuest.End

open LeanVM.Guest
open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.SaltedGuest.Check LeanVM.Guest.Check
open LeanVM.Node LeanVM.Protocol LeanVM.Protocol.KeccakHash Recursion.Salted Recursion.SecondDigest

@[expose] public section

/-! ## Frame maps over the salted core IR -/

/-- **A frame map**: a valuation for every call, by its callee and words. -/
abbrev FrameMap : Type := String → List E → List E → Val

/-- **A call relation that unfolds at the frame map `V`** over the salted core IR: a call holds
only when the callee's body holds at the valuation `V f args rets`, its parameters the arguments,
its calls in `C`. -/
def UnfoldsV (rd : Reader) (C : CallRel) (V : FrameMap) : Prop :=
  ∀ f args rets, C f args rets → ∃ fn, coreProgram.find? f = some fn ∧
    fn.params.map (V f args rets) = args ∧
    Stmt.HoldsList C rd (V f args rets) fn.body False (fun rs ↦ rs = rets)

/-- **The frame map of the memory `L`**: a call's valuation is its frame's (`Located.frameOf`). -/
noncomputable def frameV {κ : ℕ} (L : MemoryImage κ) : FrameMap :=
  fun f args rets ↦ Located.valAt L f (Located.frameOf L f args rets)

/-- The located relation unfolds along the memory's frame map. -/
theorem unfoldsV_RL {κ : ℕ} (L : MemoryImage κ) : UnfoldsV L.read (Located.RLg L) (frameV L) :=
  fun _ _ _ h ↦ by
    obtain ⟨fn, hf, hp, hb⟩ := Located.bodyAt_frameOf h
    exact ⟨fn, hf, hp, hb⟩

/-- A reader of a memory image of `2^1` to `2^32` words. -/
def MemOk (rd : Reader) : Prop := ∃ κ, 1 ≤ κ ∧ κ ≤ 32 ∧ ∃ L : MemoryImage κ, rd = L.read

/-! ## The obligations -/

/-- **`main`'s obligation**: over any call relation below the salted core IR's that unfolds along
a frame map, on a memory whose words `0`, `1` hold the digest `D` and words `2`, `3` the digest
`S`, a run of `main`'s body gives, read off by `dec`, the seed `S`, a statement of salted digest
`D` under it, and a witness of the salted node relation under it, with at most `16` children. -/
def MainSound (dec : Val → Reader → FrameMap → SeedStatementAndWitness) : Prop :=
  ∀ (rd : Reader), MemOk rd → ∀ (C : CallRel) (V : FrameMap), UnfoldsV rd C V →
    CallRel.Le C (coreProgram.Rel rd) →
  ∀ (D S : Digest) (σ : Val), LoadHolds rd 1 0 (digestHalves D).1 →
    LoadHolds rd 1 1 (digestHalves D).2 → LoadHolds rd 1 2 (digestHalves S).1 →
    LoadHolds rd 1 3 (digestHalves S).2 →
    Stmt.HoldsList C rd σ Data.core0.body False (fun rs => rs = []) →
      (dec σ rd V).seed = S ∧
        saltedStatementDigest (dec σ rd V).seed (dec σ rd V).statement = D ∧
        SaltedNodeRelation (bytecodeWords guestProgram) (dec σ rd V).seed
          (dec σ rd V).statement (dec σ rd V).witness ∧
        (dec σ rd V).witness.children.length ≤ 16

/-- **The decoding off a memory**: `dec` at `main`'s frame (`fp = 1`, the words of `main`'s
certificate's cells), the memory, and the memory's frame map. -/
noncomputable def decodeWith (dec : Val → Reader → FrameMap → SeedStatementAndWitness)
    {κ : ℕ} (L : MemoryImage κ) : SeedStatementAndWitness :=
  dec (valG L 1 (certOf 1)) L.read (frameV L)

/-- **The decoder program's obligation**: on every valid execution of the salted guest for a
public input of two digests, the decoder, of size at most `sizeBound`, run on the encoded program
and execution within `budget`, outputs the encoding of `dec`'s decoding off the memory. -/
def DecoderComputes (decoder : Cost.MachineProgram) (sizeBound : ℕ)
    (budget : Execution guestProgram → ℕ) (dec : Val → Reader → FrameMap → SeedStatementAndWitness) :
    Prop :=
  ∀ input (t : Execution guestProgram), ValidExecution₂ guestProgram input t →
    Cost.outputWithin decoder sizeBound (budget t) (Cost.encodeGuestWitnessDecoderInput guestProgram t) =
      some (Cost.encodeValue (decodeWith dec t.memory))

/-! ## From B2 -/

/-- **The second digest's cells**: a valid execution's memory for a public input of two digests
holds the two cells of the second digest at `g^2` and `g^3`. -/
theorem second_loads {input : PublicInput₂} {t : Execution guestProgram}
    (hv : ValidExecution₂ guestProgram input t) :
    LoadHolds t.memory.read 1 2 (digestHalves (publicInputDigest input.second)).1 ∧
      LoadHolds t.memory.read 1 3 (digestHalves (publicInputDigest input.second)).2 := by
  obtain ⟨-, h2, h3⟩ := hv
  rw [EndToEnd.Complete.digestScalars_publicDigest input.second]
  exact ⟨loadHolds_one h2, loadHolds_one h3⟩

variable {dec : Val → Reader → FrameMap → SeedStatementAndWitness}

/-- **Every valid execution explains its public input under its second digest**, from B2 and
`main`'s obligation: the decoding off the memory has the second digest for its seed, a statement
of the first digest under it, and a witness of the salted node relation, with at most `16`
children. -/
theorem explains_of (hb2 : B2SoundL) (hmain : MainSound dec) (input : PublicInput₂)
    (t : Execution guestProgram) (hv : ValidExecution₂ guestProgram input t) :
    (decodeWith dec t.memory).seed = publicInputDigest input.second ∧
      saltedStatementDigest (decodeWith dec t.memory).seed (decodeWith dec t.memory).statement =
        publicInputDigest input.first ∧
      SaltedNodeRelation (bytecodeWords guestProgram) (decodeWith dec t.memory).seed
        (decodeWith dec t.memory).statement (decodeWith dec t.memory).witness ∧
      (decodeWith dec t.memory).witness.children.length ≤ 16 := by
  obtain ⟨hb, h0, h1⟩ := mainBodyL_of hb2 hv.1
  obtain ⟨h2, h3⟩ := second_loads hv
  have hm : MemOk t.memory.read :=
    ⟨t.logMemorySize, hv.1.1.1, hv.1.1.2.1.trans (by decide), t.memory, rfl⟩
  exact hmain t.memory.read hm _ _ (unfoldsV_RL t.memory) (Located.rlg_le_rel t.memory) _ _ _
    h0 h1 h2 h3 hb

/-- **The salted guest is knowledge sound**, from B2, `main`'s obligation and the decoder
program's. -/
theorem knowledgeSound_of_b2 {decoder : Cost.MachineProgram} {sizeBound : ℕ}
    {budget : Execution guestProgram → ℕ} (hb2 : B2SoundL) (hmain : MainSound dec)
    (hd : DecoderComputes decoder sizeBound budget dec) :
    (⟨guestProgram, decoder, sizeBound, budget⟩ : SaltedGuest).KnowledgeSound :=
  fun input t hv ↦ ⟨decodeWith dec t.memory, hd input t hv, explains_of hb2 hmain input t hv⟩

end
end LeanVM.SaltedGuest.End
