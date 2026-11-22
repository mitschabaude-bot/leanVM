/-
  LeanVM.SaltedGuest.B1.Whir.OqSoundK

  The salted `opening_queries`' witness, sound at every level: the salted `open_stacked` is sound
  with its witness named.
-/

module

public import LeanVM.SaltedGuest.B1.Whir.OpenSK
public import LeanVM.SaltedGuest.B1.Opening.QueriesAllWK
public import LeanVM.Guest.B1.Opening.LoopsTable

/-!
# The salted queries' witness

`lvWK`: a level's queries' witness, read off the salted `opening_queries` call's frame and its
loop's frames (`oqsOfK`, the loop helper `oqLoopOfK` of the specialization); `oqSoundK_lvWK`: it is
sound (`OqSoundK`, from `opening_queries_all_sound_wK` at the specialization the names' facts name,
`shapes_loopsK`); `open_stacked_sound_wK_lvWK`: the salted `open_stacked` is sound with its witness
`open_stacked_osWK lvWK`.
-/

namespace LeanVM.SaltedGuest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Guest.B1.Whir
open LeanVM.SaltedGuest.B1

@[expose] public section

/-- The salted loop helper of a specialization. -/
def oqLoopOfK (name : String) : String :=
  ((openingQueriesLoopsK.find? (·.1 = name)).map (·.2.1)).getD ""

/-- The shapes' table and the salted specializations' agree, as a check. -/
def shapesLoopsKB : Bool :=
  openingQueriesShapes.all fun e ↦ openingQueriesLoopsK.any fun p ↦
    p.1 == e.1 && p.2.1 == oqLoopOfK e.1 && p.2.2.1.base == e.2.2.1 &&
      p.2.2.1.I == e.2.2.2.1 && p.2.2.1.pd == e.2.2.2.2.2.1 - e.2.2.2.2.2.2 &&
      p.2.2.1.cd == e.2.2.2.2.2.2 && p.2.2.2 == e.2.1

theorem shapesLoopsKB_true : shapesLoopsKB = true := by decide +kernel

/-- **Every shape has its salted specialization and loop helper.** -/
theorem shapes_loopsK {e : String × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ} (he : e ∈ openingQueriesShapes) :
    (e.1, oqLoopOfK e.1, (⟨e.2.2.1, e.2.2.2.1, e.2.2.2.2.2.1 - e.2.2.2.2.2.2, e.2.2.2.2.2.2⟩ : Oq),
      e.2.1) ∈ openingQueriesLoopsK := by
  have h := shapesLoopsKB_true
  simp only [shapesLoopsKB, List.all_eq_true, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨p, hp, ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩⟩ := h e he
  obtain ⟨n, l, ⟨b, i, pd, cd⟩, o⟩ := p
  simp only at h1 h2 h3 h4 h5 h6 h7
  subst h1 h2 h3 h4 h5 h6 h7
  exact hp

/-- **A level's salted queries' witness**: read off its `opening_queries` call's frame and its
loop's frames. -/
def lvWK : OqWit := fun rd Fr lvl lv args rets ↦
  oqsOfK (lvOq lvl lv) (lv.queries % 2 * (if lvl = 0 then 1 else 0)) (oqLoopOfK (oqNameOf lvl lv))
    (lv.queries / (1 + if lvl = 0 then 1 else 0)) rd (Fr (oqNameOf lvl lv) args rets) Fr

/-- **The salted queries' witness is sound.** -/
theorem oqSoundK_lvWK : OqSoundK lvWK := by
  intro rd C V hU hle c lvl lv hn args rets hC hN hNo hcdd hbits S hS
  have hq := hn.1.2.2.2.2.2.1
  have hp := opening_queries_all_sound_wK _ (shapes_loopsK hq)
  obtain ⟨fm, hf, hpm, hh⟩ := hU _ _ _ hC
  have hdep : lv.depth - lv.capDepth + lv.capDepth = lv.depth := Nat.sub_add_cancel hcdd
  have := hp rd C V hU hle fm (V (oqNameOf lvl lv) args rets) args rets
    (lv.queries / (1 + if lvl = 0 then 1 else 0)) hf hpm hh hN hNo
    (by simp only; rw [hdep]; exact hbits _ hN hNo) S hS
  simp only at this
  rw [hdep] at this
  exact this

/-- **The salted `open_stacked` is sound with its witness named.** -/
theorem open_stacked_sound_wK_lvWK : open_stacked_sound_w_SpecK lvWK :=
  open_stacked_sound_wK oqSoundK_lvWK

end
end LeanVM.SaltedGuest.B1.Whir
