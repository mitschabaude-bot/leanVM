/-
  LeanVM.SaltedGuest.Bounds.Valid

  The salted decoder's counts on a valid execution.
-/

module

public import LeanVM.SaltedGuest.EndReplay
public import LeanVM.SaltedGuest.B1.Main.FactsK
public import LeanVM.Cost.Bounds.Guest.Valid

/-!
# The salted decoder's counts on a valid execution

On a valid execution of the salted guest for a public input of two digests, `main`'s checks
(`B1.Main.main_factsK`, at the valuation `mainVal σ` of `main`'s frame `σ = valG t.memory 1
(certOf 1)`, the one the decoding by replay reads) bound the counts the decoding reads:

* `mainFactsK_valid`: the salted `main`'s facts there, for the second digest;
* **`countsK_valid`** (`CountsK`): at most `16` children; the declared claims of both schemes
  together, the raw signatures of each scheme, and the slots of both regions together each below
  the memory's size `2^κ`, `κ ≤ 30` (`assert_gpow`: each is the exponent of an address of the
  memory, and `n_total_g`'s exponent is the two regions' slots); and at most `2^20 - 1` slots
  of both regions together (`main`'s cap `MAX_CLAIMS`), so at most `2^20 - 1` declared claims
  and at most `2^20 - 1` raw signatures of both schemes together.

The raw signatures are not capped by a check of their own: each writes its mark, distinct from
every other's, into a slot of its scheme's region (`rawX_le`, `rawS_le`: two marks in one slot
would be two values at one address), so there are at most as many as the region has slots.
-/

namespace LeanVM.SaltedGuest.Bounds

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.B1 LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Main LeanVM.Node LeanVM.Protocol.Verifier
open LeanVM.SaltedGuest.End LeanVM.SaltedGuest.Check Recursion.Salted Recursion.SecondDigest

@[expose] public section

/-- **The counts a salted decoding reads off `main`'s valuation `σ`**, on a memory of `2^κ`
words. -/
structure CountsK (σ : Val) (κ : ℕ) : Prop where
  kids : nKids σ ≤ 16
  claims : gLog (σ (.n 0)) + gLog (σ (.n 3)) < 2 ^ κ
  rawX : nRawX σ < 2 ^ κ
  rawS : nRawS σ < 2 ^ κ
  slots : lxSlots σ + lsSlots σ < 2 ^ κ
  claimsCap : gLog (σ (.n 0)) + gLog (σ (.n 3)) ≤ 2 ^ 20 - 1
  rawCap : nRawX σ + nRawS σ ≤ 2 ^ 20 - 1
  slotsCap : lxSlots σ + lsSlots σ ≤ 2 ^ 20 - 1

/-- At most `m` items, when each has a slot below `m` holding its value, a slot holds one value at
most, and the items' values are distinct. -/
theorem le_of_slots {α : Type} {n m : ℕ} {P : ℕ → α → Prop} {val : ℕ → α}
    (hP : ∀ s v w, P s v → P s w → v = w) (hval : ∀ i < n, ∀ j < n, val i = val j → i = j)
    (h : ∀ i < n, ∃ s < m, P s (val i)) : n ≤ m := by
  classical
  choose f hf hPf using h
  let g : Fin n → Fin m := fun i => ⟨f i i.2, hf i i.2⟩
  have hg : Function.Injective g := by
    intro a b hab
    have hs : f a a.2 = f b b.2 := congrArg Fin.val hab
    have hb := hPf b b.2
    rw [← hs] at hb
    exact Fin.ext (hval a a.2 b b.2 (hP _ _ _ (hPf a a.2) hb))
  simpa using Fintype.card_le_of_injective g hg

/-- A slot below a region's bound `gen ^ r`, `r < 2^33`, is below `r`. -/
theorem belowLog_lt_of {b : E} {r s : ℕ} (hr : r < 2 ^ 33) (hb : b = gen ^ r) (h : BelowLog b s) :
    s < r := by
  obtain ⟨hs, e', he', hbe⟩ := h
  have := gen_pow_inj (a := r) (b := s + e' + 1) (by omega) (by omega) (hb.symm.trans hbe)
  omega

/-- **At most as many raw leanXMSS signatures as the leanXMSS region has slots.** -/
theorem rawX_le {C : CallRel} {rd : Reader} {σ : Val} {S : LeanVM.Protocol.Digest} {key : E}
    (MF : B1.Main.MainFactsK C rd σ S key) : lg σ 2 ≤ lg σ 0 + lg σ 1 := by
  have b0 := (MF.counts 0 (by simp)).2
  have b1 := (MF.counts 1 (by simp)).2
  have b2 := (MF.counts 2 (by simp)).2
  refine le_of_slots (P := fun s v => LoadHolds rd (σ (.n 45)) s v) (val := fun i => gen ^ i)
    (fun _ _ _ h h' => loadHolds_unique h h')
    (fun i hi j hj e => gen_pow_inj (by omega) (by omega) e) (fun i hi => ?_)
  obtain ⟨s, hs, hl⟩ := (MF.rawx i hi).2
  exact ⟨s, belowLog_lt_of (by omega) MF.lxs hs, hl⟩

/-- **At most as many raw leanSPHINCS signatures as the leanSPHINCS region has slots.** -/
theorem rawS_le {C : CallRel} {rd : Reader} {σ : Val} {S : LeanVM.Protocol.Digest} {key : E}
    (MF : B1.Main.MainFactsK C rd σ S key) : lg σ 5 ≤ lg σ 3 + lg σ 4 := by
  have b2 := (MF.counts 2 (by simp)).2
  have b3 := (MF.counts 3 (by simp)).2
  have b4 := (MF.counts 4 (by simp)).2
  have b5 := (MF.counts 5 (by simp)).2
  have c2 := (MF.counts 2 (by simp)).1
  refine le_of_slots
    (P := fun s v => LoadHolds rd (σ (.n 45) * (σ (.n 22) * gen ^ s)) 0 v)
    (val := fun j => σ (.n 2) * gen ^ j)
    (fun _ _ _ h h' => loadHolds_unique h h') (fun i hi j hj e => ?_) (fun j hj => ?_)
  · rw [c2, ← pow_add, ← pow_add] at e
    have := gen_pow_inj (by omega) (by omega) e
    omega
  · obtain ⟨s, hs, hl, -⟩ := MF.raws j hj
    exact ⟨s, belowLog_lt_of (by omega) MF.lss hs, hl⟩

/-- **The salted `main`'s facts on a valid execution**, at the valuation of `main`'s frame, for
the second digest. -/
theorem mainFactsK_valid {input : PublicInput₂} {t : Execution guestProgram}
    (hv : ValidExecution₂ guestProgram input t) :
    B1.Main.MainFactsK (Located.RLg t.memory) t.memory.read
      (B1.Main.mainVal (valG t.memory 1 (certOf 1))) (publicInputDigest input.second)
      (valG t.memory 1 (certOf 1) (.n 55)) := by
  obtain ⟨hb, -, -⟩ := mainBodyL_of b2SoundL hv.1
  obtain ⟨h2, h3⟩ := second_loads hv
  have hm : End.MemOk t.memory.read :=
    ⟨t.logMemorySize, hv.1.1.1, hv.1.1.2.1.trans (by decide), t.memory, rfl⟩
  exact B1.Main.main_factsK (Located.unfoldsV_replayK b2SoundL hv.1) (Located.rlg_le_rel t.memory)
    hm h2 h3 hb

/-- The counts of the salted `main`'s facts, on a memory of `2^κ` words, `κ ≤ 30`. -/
theorem countsK_of {C : CallRel} {κ : ℕ} (hκ : κ ≤ 30) {L : MemoryImage κ} {σ : Val} {S : LeanVM.Protocol.Digest}
    {key : E} (MF : B1.Main.MainFactsK C L.read σ S key) : CountsK σ κ := by
  have hpow : 2 ^ κ ≤ 2 ^ 30 := Nat.pow_le_pow_right (by norm_num) hκ
  have hlt : ∀ v ∈ [0, 1, 2, 3, 4, 5, 24], ∀ e, e < 2 ^ 32 → σ (.n v) = gen ^ e → e < 2 ^ κ := by
    intro v hv e he hve
    obtain ⟨w, hw⟩ := MF.addr v hv
    obtain ⟨e', he', h'⟩ := Cost.Bounds.Guest.load_gpow_lt hκ L hw
    have := gen_pow_inj (a := e) (b := e') (by omega) (by omega) (hve.symm.trans h')
    omega
  have hc : ∀ v ∈ [0, 1, 2, 3, 4, 5], gLog (σ (.n v)) < 2 ^ κ := fun v hv ↦ by
    rw [← lg_eq_gLog]
    exact hlt v (by simp only [List.mem_cons] at hv ⊢; tauto) _ (MF.counts v hv).2
      (MF.counts v hv).1
  have hk : gLog (σ (.n 6)) ≤ 16 := by rw [← lg_eq_gLog]; exact MF.kids.2
  have ht := MF.total.2
  have ht' := hlt 24 (by simp) _ ht MF.total.1
  have hx : gLog (σ (.n 22)) = lg σ 0 + lg σ 1 := by
    rw [MF.lxs, gLog_gen_pow (by
      have := (MF.counts 0 (by simp)).2; have := (MF.counts 1 (by simp)).2; omega)]
  have hs : gLog (σ (.n 23)) = lg σ 3 + lg σ 4 := by
    rw [MF.lss, gLog_gen_pow (by
      have := (MF.counts 3 (by simp)).2; have := (MF.counts 4 (by simp)).2; omega)]
  have h0 : gLog (σ (.n 0)) = lg σ 0 := (lg_eq_gLog σ 0).symm
  have h3 : gLog (σ (.n 3)) = lg σ 3 := (lg_eq_gLog σ 3).symm
  have hcap := MF.cap
  have hrx := rawX_le MF
  have hrs := rawS_le MF
  have h2 : nRawX σ = lg σ 2 := (lg_eq_gLog σ 2).symm
  have h5 : nRawS σ = lg σ 5 := (lg_eq_gLog σ 5).symm
  refine ⟨hk, ?_, hc 2 (by simp), hc 5 (by simp), ?_, ?_, ?_, ?_⟩
  · rw [h0, h3]; omega
  · unfold lxSlots lsSlots; rw [hx, hs]; omega
  · rw [h0, h3]; omega
  · rw [h2, h5]; omega
  · unfold lxSlots lsSlots; rw [hx, hs]; omega

/-- **On a valid execution of the salted guest, the counts its decoding reads are below the
memory's size**, at the valuation of `main`'s frame. -/
theorem countsK_valid {input : PublicInput₂} {t : Execution guestProgram}
    (hv : ValidExecution₂ guestProgram input t) :
    CountsK (B1.Main.mainVal (valG t.memory 1 (certOf 1))) t.logMemorySize :=
  countsK_of hv.1.1.2.1 (mainFactsK_valid hv)

/-- A valid execution's memory has at most `2^30` words. -/
theorem pow_le_valid {input : PublicInput₂} {t : Execution guestProgram}
    (hv : ValidExecution₂ guestProgram input t) : 2 ^ t.logMemorySize ≤ 2 ^ 30 :=
  Nat.pow_le_pow_right (by norm_num) hv.1.1.2.1

end
end LeanVM.SaltedGuest.Bounds
