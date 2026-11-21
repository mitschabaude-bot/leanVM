/-
  LeanVM.SaltedGuest.B1.FrameTransfer

  A salted call relation that unfolds at a frame map gives, on the unchanged functions, a deployed
  call relation that unfolds at the renamed frame map.
-/

module

public import LeanVM.SaltedGuest.B1.Da.Common

/-!
# Frame maps across the transfer

`rhoInv` undoes the loop helpers' renaming `Same.rho` on the closed set of unchanged functions
(`rhoInv_rho`: the renaming is injective there, `rho_inj`, as the pairs' deployed functions are
distinct). For a call relation `C` of the salted
core IR, `toDC C` is its calls of unchanged functions under their deployed names, and `toDV V` a
frame map `V` read at the deployed names. `unfoldsV_toD`: if `C` unfolds at `V` over the salted
core IR (`End.UnfoldsV`), then `toDC C` unfolds at `toDV V` over the deployed core IR
(`LeanVM.Guest.B1.UnfoldsV`): an unchanged function's deployed body is its salted body with the callees
renamed (`Same.agreesOn`), and its calls are of unchanged functions. `toDC_le`: below the salted
core IR's relation, `toDC C` is below the deployed one's. So every deployed statement of an
unchanged function over a frame map (`…_sound_w`, `…_holds` with `UnfoldsV`) holds of the salted
calls, at the frame map `toDV V`.
-/

namespace LeanVM.SaltedGuest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

set_option maxRecDepth 100000 in
theorem closed_chain : (Same.closed.map (·.2.2)).IsChain (· < ·) := by decide +kernel

/-- **The renaming is injective on the closed set**: the deployed functions of two pairs with one
deployed name are one (the deployed names are distinct), and the pairs' deployed indices are. -/
theorem rho_inj {f f' : String} (hf : Same.inS f = true) (hf' : Same.inS f' = true)
    (h : Same.rho f = Same.rho f') : f = f' := by
  obtain ⟨p, hp, rfl⟩ : ∃ p ∈ Same.closed, p.1 = f := by
    simpa only [Same.inS, List.contains_iff_mem, List.mem_map] using hf
  obtain ⟨p', hp', rfl⟩ : ∃ p ∈ Same.closed, p.1 = f' := by
    simpa only [Same.inS, List.contains_iff_mem, List.mem_map] using hf'
  obtain ⟨-, g', -, hg', -, hn, -⟩ := Same.closed_ok p hp
  obtain ⟨-, g'', -, hg'', -, hn', -⟩ := Same.closed_ok p' hp'
  obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.mp hg'
  obtain ⟨hj', rfl⟩ := List.getElem?_eq_some_iff.mp hg''
  have hjj : p.2.2 = p'.2.2 := by
    have hnd := Guest.coreProgram_names_nodup
    have e : (Guest.coreProgram.map (·.name))[p.2.2]'(by simpa using hj) =
        (Guest.coreProgram.map (·.name))[p'.2.2]'(by simpa using hj') := by
      simp only [List.getElem_map]; rw [hn, hn', h]
    exact (List.Nodup.getElem_inj_iff hnd).mp e
  have hnd : (Same.closed.map (·.2.2)).Nodup :=
    (List.isChain_iff_pairwise.mp closed_chain).imp (fun h ↦ Nat.ne_of_lt h)
  rw [List.inj_on_of_nodup_map hnd hp hp' hjj]

open Classical in
/-- The salted name of a deployed function name: the unchanged function of that deployed name, or
the name itself. -/
noncomputable def rhoInv (g : String) : String :=
  if h : ∃ f, Same.inS f = true ∧ Same.rho f = g then Classical.choose h else g

/-- **`rhoInv` undoes the renaming on the closed set.** -/
theorem rhoInv_rho {f : String} (hf : Same.inS f = true) : rhoInv (Same.rho f) = f := by
  have hex : ∃ f', Same.inS f' = true ∧ Same.rho f' = Same.rho f := ⟨f, hf, rfl⟩
  rw [rhoInv, dite_eq_left_of_eq_true (eq_true hex)]
  obtain ⟨h1, h2⟩ := Classical.choose_spec hex
  exact rho_inj h1 hf h2

/-- **A salted call relation's calls of unchanged functions, at their deployed names.** -/
noncomputable def toDC (C : CallRel) : CallRel := fun g args rets =>
  Same.inS (rhoInv g) = true ∧ Same.rho (rhoInv g) = g ∧ C (rhoInv g) args rets

/-- **A salted frame map, read at the deployed names.** -/
noncomputable def toDV (V : End.FrameMap) : LeanVM.Guest.B1.FrameMap := fun g args rets => V (rhoInv g) args rets

variable {rd : Reader} {C : CallRel}

theorem toDC_of {f : String} (hf : Same.inS f = true) {args rets : List E} (h : C f args rets) :
    toDC C (Same.rho f) args rets := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [rhoInv_rho hf]
  · exact hf
  · exact h

theorem toDV_rho (V : End.FrameMap) {f : String} (hf : Same.inS f = true) (args rets : List E) :
    toDV V (Same.rho f) args rets = V f args rets := by
  rw [toDV, rhoInv_rho hf]

theorem callsAgree_toDC : CallsAgree C (toDC C) Same.rho Same.inS := fun f hf args rets ↦ by
  constructor
  · exact toDC_of hf
  · rintro ⟨-, -, h⟩
    rwa [rhoInv_rho hf] at h

/-- **Below the salted core IR's relation, `toDC C` is below the deployed one's.** -/
theorem toDC_le (hle : CallRel.Le C (SaltedGuest.coreProgram.Rel rd)) :
    CallRel.Le (toDC C) (Guest.coreProgram.Rel rd) := by
  rintro g args rets ⟨hs, hr, h⟩
  have := (Same.rel_same rd hs args rets).mp (hle _ _ _ h)
  rwa [hr] at this

/-- **`toDC C` unfolds at `toDV V` over the deployed core IR** when `C` unfolds at `V` over the
salted one. -/
theorem unfoldsV_toD {V : End.FrameMap} (hV : End.UnfoldsV rd C V) :
    LeanVM.Guest.B1.UnfoldsV rd (toDC C) (toDV V) := by
  rintro g args rets ⟨hs, hr, h⟩
  obtain ⟨fn, hf, hp, hb⟩ := hV _ _ _ h
  obtain ⟨g1, g', hg1, hg', hpar, hbody, hcalls⟩ := Same.agreesOn _ hs
  obtain rfl : fn = g1 := Option.some.inj (hf.symm.trans hg1)
  rw [hr] at hg'
  refine ⟨g', hg', ?_, ?_⟩
  · rw [hpar]; exact hp
  · rw [hbody]
    exact (holdsList_mapCalls callsAgree_toDC fn.body _ hcalls Iff.rfl).mp hb

end
end LeanVM.SaltedGuest.B1
