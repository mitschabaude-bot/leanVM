/-
  LeanVM.SaltedGuest.B1.Callee

  A salted call of an unchanged function is the deployed function's call.
-/

module

public import LeanVM.SaltedGuest.Same
public import LeanVM.Guest.CoreLemmas

/-!
# Unchanged callees

`toD`: a call of a function of the closed set whose name the renaming keeps
(`Same.inS f`, `Same.rho f = f`, both decided by the kernel at a literal name) holds in the
deployed core IR when it holds in the salted one (`Same.rel_same'`); `toD_le`: so does every call
of a relation below the salted core IR's. `onlyS f rd`, the salted core IR's calls of `f` alone,
lies below the deployed core IR's (`onlyS_le`): a deployed statement about the calls of a relation
below the deployed core IR (`…_SpecC`) applies to it. `holdsList_toD`: a block whose callees are
in the closed set holds under the salted core IR's relation exactly when its renaming by `rho`
holds under the deployed one's; `body_toD`: so a prefix of an unchanged function's salted body that
holds gives the prefix of its deployed body.
-/

namespace LeanVM.SaltedGuest.B1

open LeanVM.Parameters LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

theorem toD {rd : Reader} {f : String} {args rets : List E} (hf : Same.inS f = true)
    (hr : Same.rho f = f) (h : SaltedGuest.coreProgram.Rel rd f args rets) :
    Guest.coreProgram.Rel rd f args rets :=
  (Same.rel_same' rd hf hr args rets).mp h

theorem toD_le {rd : Reader} {C : CallRel} (hC : CallRel.Le C (SaltedGuest.coreProgram.Rel rd))
    {f : String} {args rets : List E} (hf : Same.inS f = true) (hr : Same.rho f = f)
    (h : C f args rets) : Guest.coreProgram.Rel rd f args rets :=
  toD hf hr (hC _ _ _ h)

/-- The salted core IR's calls of `f` alone. -/
def onlyS (f : String) (rd : Reader) : CallRel :=
  fun g args rets ↦ g = f ∧ SaltedGuest.coreProgram.Rel rd g args rets

theorem onlyS_le {f : String} {rd : Reader} (hf : Same.inS f = true) (hr : Same.rho f = f) :
    CallRel.Le (onlyS f rd) (Guest.coreProgram.Rel rd) := by
  rintro g args rets ⟨rfl, h⟩
  exact toD hf hr h

theorem holdsList_toD {rd : Reader} {σ : Val} {ss : List Stmt} {next : Prop}
    {kret : List E → Prop} (hc : Stmt.callsAllList Same.inS ss = true) :
    Stmt.HoldsList (SaltedGuest.coreProgram.Rel rd) rd σ ss next kret ↔
      Stmt.HoldsList (Guest.coreProgram.Rel rd) rd σ (Stmt.mapCallsList Same.rho ss) next kret :=
  holdsList_mapCalls (fun _ hf args rets ↦ rel_transfer Same.agreesOn rd hf args rets) ss kret hc
    Iff.rfl

theorem mapCallsList_take (ρ : String → String) :
    ∀ (ss : List Stmt) (n : ℕ), Stmt.mapCallsList ρ (ss.take n) = (Stmt.mapCallsList ρ ss).take n
  | [], n => by cases n <;> rfl
  | s :: ss, 0 => rfl
  | s :: ss, n + 1 => by
      simp only [List.take_succ_cons, Stmt.mapCallsList, mapCallsList_take ρ ss n]

theorem callsAllList_take {p : String → Bool} :
    ∀ (ss : List Stmt) (n : ℕ), Stmt.callsAllList p ss = true →
      Stmt.callsAllList p (ss.take n) = true
  | [], n, _ => by cases n <;> rfl
  | s :: ss, 0, _ => rfl
  | s :: ss, n + 1, h => by
      simp only [Stmt.callsAllList, Bool.and_eq_true] at h
      simp only [List.take_succ_cons, Stmt.callsAllList, h.1, callsAllList_take ss n h.2,
        Bool.and_self]

/-- **A prefix of an unchanged function's body**: the salted body `bS` holding under the salted
core IR's relation gives the deployed body `bD`, the renaming of `bS` by `rho`, holding under the
deployed one's. -/
theorem body_toD {rd : Reader} {σ : Val} {bS bD : List Stmt} {n : ℕ} {next : Prop}
    {kret : List E → Prop} (hb : bD = Stmt.mapCallsList Same.rho bS)
    (hc : Stmt.callsAllList Same.inS bS = true)
    (h : Stmt.HoldsList (SaltedGuest.coreProgram.Rel rd) rd σ (bS.take n) next kret) :
    Stmt.HoldsList (Guest.coreProgram.Rel rd) rd σ (bD.take n) next kret := by
  rw [hb, ← mapCallsList_take]
  exact (holdsList_toD (callsAllList_take bS n hc)).mp h

end
end LeanVM.SaltedGuest.B1
