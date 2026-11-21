/-
  LeanVM.SecondDigest.Assemble

  The specification of the whole verifier program with a second public digest, composed from
  leanVM's phase specifications and the phase for two digests, at `εmax = 2^-128` per group of
  challenges, and the doom certificate it gives.
-/

module

public import LeanVM.SecondDigest.Phase
public import LeanVM.Protocol.EndToEnd.Sound.Assemble

/-!
# The specification of the verifier with a second public digest

`leanVmSpec₂ prog input` is a specification of `leanVmVerifierProgram₂ (bytecodeWords prog)
(publicInputDigest input.first) (publicInputDigest input.second)` from no doom, with
postcondition rejection, at `εmax = 2^-128` and lead `0`; `leanVmCert₂` is its doom certificate
(`Spec.toCert`). It is leanVM's `leanVmSpec` (`LeanVM.Protocol.EndToEnd.Sound.Assemble`) with three
changes.

1. **The candidates of the front.** The stack's root creates `CommitPost₂`: no candidate of the
   committed word that holds the second digest (`StackHoldsSecondDigest`) satisfies the leanISA
   relation for the first digest (`CommitDoom₂`). The bus phase and the table sumcheck are
   leanVM's specifications (`busTableSpec_leanIsa`) on the candidates as oracles that hold the
   second digest (`candsOf₂`), a part of leanVM's candidates, so finite and at most `L₀ = 2^12`;
   the table seam gives leanVM's `PubPre` on the candidates of the history that hold the second
   digest (`tablePost_pubPre` at `HoldingSecond`).
2. **The public input** (`pubPartAt₂`): the phase for two digests (`pubPhaseSpec₂`) takes that
   doom to leanVM's `PubPost` with six claims on all candidates of the history, the doom the
   Keccak reduction starts from; its lead with the Keccak reduction's six first challenges is
   `L₀ · 7/|E|`, as leanVM's (`pubLead_le`).
3. **The count of claims.** The Keccak reduction starts from at most `545 + 6 = 551` claims and
   the opening batches at most `553` (`keccakPart₂`); the opening's error with ring switching's
   six challenges is at most `2^-128` for at most `553` claims (`openingError_le₂`).

The phases after the public input, ring switching and the stacked opening, are leanVM's
(`ringPart`).
-/

namespace Recursion.SecondDigest

open LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.LeanIsa LeanVM.Protocol.Whir.Sound
open LeanVM.Protocol.EndToEnd LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.EndToEnd.Sound
open scoped ENNReal NNReal

@[expose] public section

/-! ## The numeric clause -/

/-- The batching's error for at most `553` claims, as a natural number over `|E|`. -/
theorem eBatch_le₂ (J : ℕ) (P₀ : LevelCode) (hJ : J ≤ 553) (hL : P₀.listMax ≤ L₀) :
    eBatch J P₀ ≤ ((552 * L₀ : ℕ) : ℝ≥0∞) / ((2 ^ 192 : ℕ) : ℝ≥0∞) := by
  rw [eBatch, card_E_ennreal]
  refine ENNReal.div_le_div_right (Nat.cast_le.2 ?_) _
  exact Nat.mul_le_mul (by omega) hL

/-- **The opening's error for at most `553` claims**: ring switching's six challenges and the
batching of at most `553` claims, at a level-0 list of at most `2^12`, are at most `2^-128`. -/
theorem openingError_le₂ (J : ℕ) (P₀ : LevelCode) (hJ : J ≤ 553) (hL : P₀.listMax ≤ L₀) :
    (∑ _i ∈ Finset.range 6, (L₀ : ℝ≥0∞) * ((overE 1 : ℝ≥0) : ℝ≥0∞)) + eBatch J P₀ ≤
      (2 : ℝ≥0∞)⁻¹ ^ 128 := by
  refine le_eps_of_nat (n := 6 * L₀ + 552 * L₀)
    ((add_le_add le_rfl (eBatch_le₂ J P₀ hJ hL)).trans (le_of_eq ?_)) ?_
  · rw [sum_mul_overE_one, div_E_add]
  · norm_num

/-! ## The program after the announced sizes -/

/-- `verify_execution` with a second public digest after the announced sizes `(layout, ρ)`. -/
def veBody₂ (publicInput second : Digest) (layout : Verifier.Layout) (ρ : ℕ) :
    VerifierProgram Unit := do
  Verifier.commitStack layout.stackLog ρ
  let bus ← Verifier.verifyBusBalance computedBytecodeValue layout
  let claims ← Verifier.tablePhaseClaims layout bus
  let publicClaims ← publicInputPhase₂ layout publicInput second
  let claims := claims ++ publicClaims
  let (claims, keccakPoint, keccakSlices) ← Verifier.keccakPhaseClaims layout claims
  let (ringTarget, ringWeight) ← Verifier.ringSwitch keccakPoint keccakSlices
  Verifier.verifyStackedOpening layout.stackLog ρ
    (Verifier.ringSwitchClaim layout ringTarget ringWeight :: claims.map (·.stackClaim layout))

/-- `verify_execution` with a second public digest is the announced sizes, then `veBody₂`. -/
theorem verifyExecution₂_eq (bytecode : List K) (publicInput second : Digest) :
    verifyExecutionClaims₂ computedBytecodeValue bytecode publicInput second =
      (readAnnouncedSizes bytecode).bind fun a ↦ veBody₂ publicInput second a.1 a.2 := rfl

/-! ## The doom the stack's root creates -/

/-- **The commitment's doom for two digests**, for the value `(layout, ρ)` the announced sizes
gave: `layout` is the verifier's layout at sizes `s`, the history's first commitment is the word
`W₀`, and no candidate of `W₀` (at the threshold `A μ ρ`) that holds the second digest satisfies
the leanISA relation at `s` for the first digest. -/
def CommitDoom₂ (prog : LeanIsaProgram) (input : PublicInput₂) (A : ℕ → ℕ → ℕ)
    (a : Verifier.Layout × ℕ) (h : List Ev) : Prop :=
  ∃ s W₀, a.1 = verifierLayout prog s ∧ firstWord h = some W₀ ∧
    ∀ q ∈ Candidates (leanIsaμ prog s) a.2 (A (leanIsaμ prog s) a.2) W₀,
      StackHoldsSecondDigest prog s input.second q → ¬ M3Holds (leanIsaInstance prog s) input.first q

/-- **The doom the stack's root creates for two digests**: `CommitDoom₂`, and the stack's is the
only commitment. -/
def CommitPost₂ (prog : LeanIsaProgram) (input : PublicInput₂) (a : Verifier.Layout × ℕ) (_ : Unit)
    (h : List Ev) : Prop :=
  CommitDoom₂ prog input thrOf a h ∧ StackShape a.1.stackLog a.2 h

section Phases

variable (prog : LeanIsaProgram) (input : PublicInput₂) (s : Sizes) (ρ : ℕ)

/-- **The candidates of a committed word that hold the second digest**, as oracles of the
instance. -/
def candsOf₂ (W : Word) : Set (∀ i, TheOracle (leanIsaInstance prog s) i) :=
  (fun q ↦ fun _ ↦ q) ''
    {q | q ∈ Candidates (leanIsaμ prog s) ρ (thrOf (leanIsaμ prog s) ρ) W ∧
      StackHoldsSecondDigest prog s input.second q}

/-- The candidates that hold the second digest are a part of leanVM's. -/
theorem candsOf₂_subset (W : Word) : candsOf₂ prog input s ρ W ⊆ candsOf prog s ρ thrOf W :=
  Set.image_mono fun _ hq ↦ hq.1

/-- The candidates that hold the second digest are finite and at most `2^12`. -/
theorem candsOf₂_bound (hw : Whir.Admissible (verifierLayout prog s).stackLog ρ) (W : Word) :
    (candsOf₂ prog input s ρ W).Finite ∧ (candsOf₂ prog input s ρ W).ncard ≤ L₀ := by
  have hb := candsOf_bound (prog := prog) (s := s) (ρ := ρ) hw W
  refine ⟨hb.1.subset (candsOf₂_subset prog input s ρ W), ?_⟩
  exact (Set.ncard_le_ncard (candsOf₂_subset prog input s ρ W) hb.1).trans hb.2

/-- **The commitment's doom for two digests is the bus phase's** on the candidates that hold the
second digest. -/
theorem commitDoom₂_hdoom (h : List Ev)
    (hD : CommitDoom₂ prog input thrOf (verifierLayout prog s, ρ) h) :
    HDoom (candsOf₂ prog input s ρ) (Seam.commit (leanIsaInstance prog s)) input.first h := by
  obtain ⟨s', W, hs, hW, hq⟩ := hD
  obtain rfl := verifierLayout_injective prog hs.symm
  exact ⟨W, hW, by rintro _ ⟨q, ⟨hq', hsec⟩, rfl⟩ hin; exact hq q hq' hsec hin⟩

/-- The candidates of the history that hold the second digest, read as oracles, are those of
`candsOf₂`. -/
theorem holdingSecond_mem : ∀ h q, q ∈ HoldingSecond prog s (Cs prog s ρ) input.second h →
    ∀ W, firstWord h = some W → (fun _ ↦ toI prog s q) ∈ candsOf₂ prog input s ρ W := by
  rintro h q ⟨⟨W', hW', hq⟩, hsec⟩ W hW
  rw [hW] at hW'
  cases hW'
  exact ⟨_, ⟨hq, hsec⟩, rfl⟩

variable {prog s ρ}

open Classical in
/-- **The Keccak reduction, ring switching and the stacked opening**, for at most `551` claims. -/
noncomputable def keccakPart₂ (hw : Whir.Admissible (verifierLayout prog s).stackLog ρ)
    (hlb : LayoutBounds (verifierLayout prog s)) (cl : List Verifier.ColumnClaim)
    (hcl : cl.length ≤ 551) :
    Spec ((keccakPhaseClaims (verifierLayout prog s) cl).bind fun r ↦
        (ringSwitch r.2.1 r.2.2).bind fun y ↦
          verifyStackedOpening (verifierLayout prog s).stackLog ρ
            (ringSwitchClaim (verifierLayout prog s) y.1 y.2 ::
              r.1.map (·.stackClaim (verifierLayout prog s))))
      (fun h ↦ KeccakPre prog s (Cs prog s ρ) cl h ∧
        StackShape (verifierLayout prog s).stackLog ρ h)
      (fun _ _ ↦ False) εLean ((L₀ : ℝ≥0∞) * KeccakGkr.errE 6) 0 :=
  have he := phase_errors (leanIsaInstance prog s) ((μBus_le prog s hlb).trans (by norm_num))
    (B_leanIsa_le prog s)
  (Spec.frame (Spec.retInv (keccakPhaseSpec prog s (Cs prog s ρ) (cs_stable prog s ρ)
      (cs_ncard prog s ρ hw)
      (T := (∑ _i ∈ Finset.range 6, (L₀ : ℝ≥0∞) * ((overE 1 : ℝ≥0) : ℝ≥0∞)) +
        eBatch 553 (code₀ (verifierLayout prog s).stackLog ρ))
      (openingError_le₂ 553 _ le_rfl (listMax_le hw)) he.2.2.2.2.2.2.2.2.2 cl)
      (fun r ↦ r.1.length ≤ cl.length + 1) (retOK_keccakPhase _ cl))
    _ (stackShape_keep (movesOK_keccakPhase _ cl) _ _)).bind' fun r ↦
    if hr : r.1.length ≤ 552 then
      (ringPart hw r.1 r.2.1 r.2.2).mono (fun _ hp ↦ ⟨hp.1.1, hp.2⟩) (fun _ _ h ↦ h) le_rfl
        (add_le_add le_rfl (eBatch_le_of_le _ (by omega))) le_rfl
    else Spec.dead.mono (fun _ hp ↦ hr (by have := hp.1.2; omega)) (fun _ _ h ↦ h) le_rfl le_rfl
      le_rfl

open Classical in
/-- **The public input for two digests at the table sumcheck's point `pt`, then the Keccak
reduction, ring switching and the opening**, after at most `545` claims of the table phase, from
doom on the candidates that hold the second digest. The public input's challenge and the Keccak
reduction's six first challenges are one group, of lead at most `L₀ · 7/|E|` (`pubLead_le`). -/
noncomputable def pubPartAt₂ (hw : Whir.Admissible (verifierLayout prog s).stackLog ρ)
    (hlb : LayoutBounds (verifierLayout prog s)) (cl : List Verifier.ColumnClaim)
    (hcl : cl.length ≤ 545)
    (pt : Vector E (leanIsaInstance prog s).τmax) :
    Spec ((publicInputPhase₂ (verifierLayout prog s) (publicInputDigest input.first)
        (publicInputDigest input.second)).bind fun pc ↦
        (keccakPhaseClaims (verifierLayout prog s) (cl ++ pc)).bind fun r ↦
        (ringSwitch r.2.1 r.2.2).bind fun y ↦ verifyStackedOpening (verifierLayout prog s).stackLog ρ
          (ringSwitchClaim (verifierLayout prog s) y.1 y.2 ::
            r.1.map (·.stackClaim (verifierLayout prog s))))
      (fun h ↦ (OutLanesAt s cl pt.toList ∧
          PubPre₂ prog s (Cs prog s ρ) cl input.first input.second pt h) ∧
        StackShape (verifierLayout prog s).stackLog ρ h)
      (fun _ _ ↦ False) εLean ((L₀ : ℝ≥0∞) * ((overE 7 : ℝ≥0) : ℝ≥0∞)) 0 :=
  if hout : OutLanesAt s cl pt.toList then
    (((Spec.frame (Spec.retInv (pubPhaseSpec₂ prog s (Cs prog s ρ) cl input.first input.second pt
        (cs_stable prog s ρ) (cs_ncard prog s ρ hw) (T := (L₀ : ℝ≥0∞) * KeccakGkr.errE 6))
        (fun pc ↦ pc.length ≤ 6) (retOK_publicInputPhase₂ _ _ _))
      _ (stackShape_keep (movesOK_publicInputPhase₂ _ _ _) _ _)).mono
      (Pre' := fun h ↦ (OutLanesAt s cl pt.toList ∧
          PubPre₂ prog s (Cs prog s ρ) cl input.first input.second pt h) ∧
        StackShape (verifierLayout prog s).stackLog ρ h)
      (fun _ hp ↦ ⟨hp.1.2, hp.2⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun pc ↦
      if hpc : pc.length ≤ 6 then
        (keccakPart₂ hw hlb (cl ++ pc) (by rw [List.length_append]; omega)).mono
          (fun _ hp ↦ ⟨⟨pt, fun l ↦ (hout l).imp fun _ hv ↦ List.mem_append_left _ hv,
            hp.1.1⟩, hp.2⟩)
          (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
      else Spec.dead.mono (fun _ hp ↦ hpc hp.1.2) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).mono
      (fun _ h ↦ h) (fun _ _ h ↦ h) le_rfl (pubLead_le L₀) le_rfl
  else Spec.dead.mono (fun _ hp ↦ hout hp.1.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

open Classical in
/-- **Everything after the stack's root**: the bus and the table sumcheck on the candidates that
hold the second digest, from the root's doom, then, at the table sumcheck's point, the public input
for two digests, the Keccak reduction, ring switching and the opening. -/
noncomputable def restSpec₂
    (hw : Whir.Admissible (verifierLayout prog s).stackLog ρ)
    (hlb : LayoutBounds (verifierLayout prog s)) :
    Spec ((verifyBusBalance computedBytecodeValue (verifierLayout prog s)).bind fun bus ↦
        (tablePhaseClaims (verifierLayout prog s) bus).bind fun cl ↦
        (publicInputPhase₂ (verifierLayout prog s) (publicInputDigest input.first)
          (publicInputDigest input.second)).bind fun pc ↦
        (keccakPhaseClaims (verifierLayout prog s) (cl ++ pc)).bind fun r ↦
        (ringSwitch r.2.1 r.2.2).bind fun y ↦ verifyStackedOpening (verifierLayout prog s).stackLog ρ
          (ringSwitchClaim (verifierLayout prog s) y.1 y.2 ::
            r.1.map (·.stackClaim (verifierLayout prog s))))
      (fun h ↦ CommitPost₂ prog input (verifierLayout prog s, ρ) () h)
      (fun _ _ ↦ False) εLean (abError (leanIsaInstance prog s) L₀ + 0) 0 :=
  have he := phase_errors (leanIsaInstance prog s) ((μBus_le prog s hlb).trans (by norm_num))
    (B_leanIsa_le prog s)
  Spec.congr (VerifierProgram.bind_assoc _ _ _) <|
    ((Spec.frame (Spec.retInv (busTableSpec_leanIsa prog s input.first
        (candsOf₂ prog input s ρ) (fun W ↦ (candsOf₂_bound prog input s ρ hw W).1)
        (fun W ↦ (candsOf₂_bound prog input s ρ hw W).2) he.2.1 he.2.2.1 he.2.2.2.1
        he.2.2.2.2.1 he.2.2.2.2.2.1 he.2.2.2.2.2.2.1 (he.2.2.2.2.2.2.2.1 _))
        (fun cl ↦ cl.length ≤ 545) (retOK_busTable _))
      _ (stackShape_keep (movesOK_busTable _) _ _)).mono
      (fun h hp ↦ ⟨commitDoom₂_hdoom prog input s ρ h hp.1, hp.2⟩) (fun _ _ h ↦ h)
      le_rfl le_rfl le_rfl).bind' fun cl ↦
      if hcl : cl.length ≤ 545 then
        (Spec.exPre fun pt ↦ pubPartAt₂ input hw hlb cl hcl pt).mono
          (fun h hp ↦ by
            obtain ⟨pt, hout, hpre⟩ := tablePost_pubPre prog s (candsOf₂ prog input s ρ)
              input.first (HoldingSecond prog s (Cs prog s ρ) input.second)
              (holdingSecond_mem prog input s ρ) cl h hp.1.1
            exact ⟨pt, ⟨hout, hpre⟩, hp.2⟩) (fun _ _ h ↦ h)
          le_rfl le_rfl le_rfl
      else Spec.dead.mono (fun _ hp ↦ hcl hp.1.2) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

/-- **`verify_execution` with a second public digest after the announced sizes**, at good sizes:
the stack's root, then `restSpec₂`. -/
noncomputable def realSpec₂
    (hw : Whir.Admissible (verifierLayout prog s).stackLog ρ)
    (hlb : LayoutBounds (verifierLayout prog s)) :
    Spec (veBody₂ (publicInputDigest input.first) (publicInputDigest input.second)
        (verifierLayout prog s) ρ) (fun _ ↦ False)
      (fun _ _ ↦ False) εLean 0 0 :=
  (commitSpec (CommitPost₂ prog input (verifierLayout prog s, ρ))
      (verifierLayout prog s).stackLog ρ
      (phase_errors (leanIsaInstance prog s) ((μBus_le prog s hlb).trans (by norm_num))
        (B_leanIsa_le prog s)).1).bind' fun _ ↦
    restSpec₂ input hw hlb

end Phases

/-! ## The whole program -/

section Whole

variable (prog : LeanIsaProgram) (input : PublicInput₂)

open Classical in
/-- `verify_execution` with a second public digest after the announced value `a`: `realSpec₂` at
good sizes, dead otherwise. -/
noncomputable def bodySpec₂ (a : Verifier.Layout × ℕ) :
    Spec (veBody₂ (publicInputDigest input.first) (publicInputDigest input.second) a.1 a.2)
      (fun _ ↦ False) (fun _ _ ↦ False) εLean 0 0 :=
  if h : ∃ s, Good prog a s then
    (realSpec₂ (prog := prog) (s := h.choose) (ρ := a.2) input
      (by rw [← h.choose_spec.1]; exact h.choose_spec.2.2.1)
      (by rw [← h.choose_spec.1]; exact h.choose_spec.2.2.2)).congr
      (by rw [h.choose_spec.1])
  else Spec.dead

/-- **The specification of `verify_execution` with a second public digest.** -/
noncomputable def veSpec₂ :
    Spec (verifyExecutionClaims₂ computedBytecodeValue (bytecodeWords prog)
        (publicInputDigest input.first) (publicInputDigest input.second)) (fun _ ↦ False)
      (fun _ _ ↦ False) εLean 0 0 :=
  (readSizesSpec (bytecodeWords prog) (fun _ _ ↦ False)).bind' (bodySpec₂ prog input)

/-- **The specification of the verifier program with a second public digest**: from no doom,
rejecting where it returns in doom, every group's escape at most `2^-128` (discounted by its proof
of work), lead `0`, transported to the statement's program (`leanVmProgram₂_eq`); irreducible, so
that elaboration does not reduce the transport. -/
@[irreducible] noncomputable def leanVmSpec₂ :
    Spec (leanVmVerifierProgram₂ (bytecodeWords prog) (publicInputDigest input.first)
        (publicInputDigest input.second)) (fun _ ↦ False)
      (fun b _ ↦ b = false) εLean 0 0 :=
  ((veSpec₂ prog input).bind' fun _ ↦
    (Spec.ret (Post := fun b _ ↦ b = false) true).mono (fun _ h ↦ h.elim) (fun _ _ h ↦ h)
      le_rfl le_rfl le_rfl).congr (leanVmProgram₂_eq _ _ _).symm

/-- **The doom certificate of the verifier with a second public digest.** -/
noncomputable def leanVmCert₂ :
    Cert (leanVmVerifierProgram₂ (bytecodeWords prog) (publicInputDigest input.first)
      (publicInputDigest input.second)) :=
  (leanVmSpec₂ prog input).toCert

end Whole

end
end Recursion.SecondDigest
