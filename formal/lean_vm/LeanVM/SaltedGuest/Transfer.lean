/-
  LeanVM.SaltedGuest.Transfer

  Two core programs that agree on a set of functions closed under calls, up to a renaming of the
  callees, have the same call relation on that set.
-/

module

public import LeanVM.Guest.Core

/-!
# Transferring a call relation between programs

`Stmt.mapCalls ρ` renames every callee of a statement by `ρ` (calls, conditional calls and the
functions of a `dispatch`); `Stmt.callsAll p` says that `p` holds of every callee.

* `holdsList_mapCalls`: a block holds under the call relation `C` exactly when its renaming holds
  under `C'`, if `C f` and `C' (ρ f)` agree on every callee `f` of the block.
* `relN_transfer`, `rel_transfer`: if every function `f` of a set `S` (a Boolean predicate on
  names) is found in `Q`, `ρ f` is found in `P` with the same parameters and the body renamed by
  `ρ`, and every callee of `f` is in `S`, then `Q`'s and `P`'s call relations agree at `f` and
  `ρ f`, at every depth and so in the limit.
-/

namespace LeanVM.Guest.Core

open LeanVM.Parameters

@[expose] public section

mutual
/-- A statement with its callees renamed by `ρ`. -/
def Stmt.mapCalls (ρ : String → String) : Stmt → Stmt
  | .atom a => .atom a
  | .ite c z n => .ite c (Stmt.mapCallsList ρ z) (Stmt.mapCallsList ρ n)
  | .match_ x arms => .match_ x (Stmt.mapCallsArms ρ arms)
  | .call f args rets => .call (ρ f) args rets
  | .callIf c f args => .callIf c (ρ f) args
  | .dispatch x fs args rets => .dispatch x (fs.map ρ) args rets
  | .ret vs => .ret vs

/-- A block with its callees renamed by `ρ`. -/
def Stmt.mapCallsList (ρ : String → String) : List Stmt → List Stmt
  | [] => []
  | s :: ss => Stmt.mapCalls ρ s :: Stmt.mapCallsList ρ ss

/-- `match` arms with their callees renamed by `ρ`. -/
def Stmt.mapCallsArms (ρ : String → String) : List (List Stmt) → List (List Stmt)
  | [] => []
  | a :: as => Stmt.mapCallsList ρ a :: Stmt.mapCallsArms ρ as
end

mutual
/-- `p` holds of every callee of a statement. -/
def Stmt.callsAll (p : String → Bool) : Stmt → Bool
  | .atom _ => true
  | .ite _ z n => Stmt.callsAllList p z && Stmt.callsAllList p n
  | .match_ _ arms => Stmt.callsAllArms p arms
  | .call f _ _ => p f
  | .callIf _ f _ => p f
  | .dispatch _ fs _ _ => fs.all p
  | .ret _ => true

/-- `p` holds of every callee of a block. -/
def Stmt.callsAllList (p : String → Bool) : List Stmt → Bool
  | [] => true
  | s :: ss => Stmt.callsAll p s && Stmt.callsAllList p ss

/-- `p` holds of every callee of `match` arms. -/
def Stmt.callsAllArms (p : String → Bool) : List (List Stmt) → Bool
  | [] => true
  | a :: as => Stmt.callsAllList p a && Stmt.callsAllArms p as
end

section Holds

variable {C C' : CallRel} {rd : Reader} {σ : Val} {ρ : String → String} {p : String → Bool}

/-- `C f` and `C' (ρ f)` agree wherever `p` holds. -/
def CallsAgree (C C' : CallRel) (ρ : String → String) (p : String → Bool) : Prop :=
  ∀ f, p f = true → ∀ args rets, C f args rets ↔ C' (ρ f) args rets

theorem dispatch_agree (h : CallsAgree C C' ρ p) {x : V} {args rets : List V} :
    ∀ (fs : List String), fs.all p = true →
      ((∃ (j : Nat) (hj : j < fs.length), σ x = ofK (addressOfIndex j) ∧
          C fs[j] (args.map σ) (rets.map σ)) ↔
        ∃ (j : Nat) (hj : j < (fs.map ρ).length), σ x = ofK (addressOfIndex j) ∧
          C' (fs.map ρ)[j] (args.map σ) (rets.map σ)) := by
  intro fs hfs
  rw [List.all_eq_true] at hfs
  constructor
  · rintro ⟨j, hj, hx, hc⟩
    exact ⟨j, by simpa using hj, hx, by
      simpa using (h fs[j] (hfs _ (List.getElem_mem hj)) _ _).mp hc⟩
  · rintro ⟨j, hj, hx, hc⟩
    have hj' : j < fs.length := by simpa using hj
    exact ⟨j, hj', hx, (h fs[j] (hfs _ (List.getElem_mem hj')) _ _).mpr (by simpa using hc)⟩

mutual
theorem holds_mapCalls (h : CallsAgree C C' ρ p) :
    ∀ (s : Stmt) {next next' : Prop} (kret : List E → Prop), s.callsAll p = true →
      (next ↔ next') → (Stmt.Holds C rd σ s next kret ↔ Stmt.Holds C' rd σ (s.mapCalls ρ) next' kret)
  | .atom a, _, _, _, _, hn => by
      simp only [Stmt.mapCalls, Stmt.Holds]
      exact and_congr_right fun _ ↦ hn
  | .ite c z n, _, _, kret, hs, hn => by
      simp only [Stmt.callsAll, Bool.and_eq_true] at hs
      simp only [Stmt.mapCalls, Stmt.Holds]
      exact and_congr_right fun _ ↦ and_congr
        (imp_congr_right fun _ ↦ holdsList_mapCalls h z kret hs.1 hn)
        (imp_congr_right fun _ ↦ holdsList_mapCalls h n kret hs.2 hn)
  | .match_ x arms, _, _, kret, hs, hn => by
      simp only [Stmt.callsAll] at hs
      simp only [Stmt.mapCalls, Stmt.Holds]
      exact holdsArms_mapCalls h arms 0 kret hs hn
  | .call f args rets, _, _, _, hs, hn => by
      simp only [Stmt.callsAll] at hs
      simp only [Stmt.mapCalls, Stmt.Holds]
      exact and_congr (h f hs _ _) hn
  | .callIf c f args, _, _, _, hs, hn => by
      simp only [Stmt.callsAll] at hs
      simp only [Stmt.mapCalls, Stmt.Holds]
      exact and_congr_right fun _ ↦ and_congr (imp_congr_right fun _ ↦ h f hs _ _) hn
  | .dispatch x fs args rets, _, _, _, hs, hn => by
      simp only [Stmt.callsAll] at hs
      simp only [Stmt.mapCalls, Stmt.Holds]
      exact and_congr (dispatch_agree h fs hs) hn
  | .ret vs, _, _, _, _, _ => by
      simp only [Stmt.mapCalls, Stmt.Holds]

theorem holdsList_mapCalls (h : CallsAgree C C' ρ p) :
    ∀ (ss : List Stmt) {next next' : Prop} (kret : List E → Prop), Stmt.callsAllList p ss = true →
      (next ↔ next') →
      (Stmt.HoldsList C rd σ ss next kret ↔
        Stmt.HoldsList C' rd σ (Stmt.mapCallsList ρ ss) next' kret)
  | [], _, _, _, _, hn => by simpa only [Stmt.mapCallsList, Stmt.HoldsList] using hn
  | s :: ss, _, _, kret, hs, hn => by
      simp only [Stmt.callsAllList, Bool.and_eq_true] at hs
      simp only [Stmt.mapCallsList, Stmt.HoldsList]
      exact holds_mapCalls h s kret hs.1 (holdsList_mapCalls h ss kret hs.2 hn)

theorem holdsArms_mapCalls (h : CallsAgree C C' ρ p) {x : V} :
    ∀ (arms : List (List Stmt)) (j : Nat) {next next' : Prop} (kret : List E → Prop),
      Stmt.callsAllArms p arms = true → (next ↔ next') →
      (Stmt.HoldsArms C rd σ x j arms next kret ↔
        Stmt.HoldsArms C' rd σ x j (Stmt.mapCallsArms ρ arms) next' kret)
  | [], _, _, _, _, _, _ => by simp only [Stmt.mapCallsArms, Stmt.HoldsArms]
  | a :: as, j, _, _, kret, hs, hn => by
      simp only [Stmt.callsAllArms, Bool.and_eq_true] at hs
      simp only [Stmt.mapCallsArms, Stmt.HoldsArms]
      exact or_congr (and_congr_right fun _ ↦ holdsList_mapCalls h a kret hs.1 hn)
        (holdsArms_mapCalls h as (j + 1) kret hs.2 hn)
end

end Holds

/-- **`Q` agrees with `P` on the functions of `S`, up to the renaming `ρ`**: each is found in `Q`,
its image under `ρ` is found in `P` with the same parameters and the renamed body, and its
callees are in `S`. -/
def AgreesOn (Q P : Program) (ρ : String → String) (S : String → Bool) : Prop :=
  ∀ f, S f = true → ∃ g g', Q.find? f = some g ∧ P.find? (ρ f) = some g' ∧
    g'.params = g.params ∧ g'.body = Stmt.mapCallsList ρ g.body ∧ Stmt.callsAllList S g.body = true

theorem relN_transfer {Q P : Program} {ρ : String → String} {S : String → Bool}
    (h : AgreesOn Q P ρ S) (rd : Reader) :
    ∀ n, CallsAgree (Q.relN rd n) (P.relN rd n) ρ S
  | 0 => fun _ _ _ _ ↦ by simp only [Program.relN]
  | n + 1 => fun f hf args rets ↦ by
      obtain ⟨g, g', hg, hg', hp, hb, hc⟩ := h f hf
      simp only [Program.relN, hg, hg', Option.some.injEq, exists_eq_left', Fn.Sem, hp, hb]
      exact exists_congr fun σ ↦ and_congr_right fun _ ↦
        holdsList_mapCalls (relN_transfer h rd n) g.body _ hc Iff.rfl

/-- **The call relations agree on `S`**, up to the renaming `ρ`. -/
theorem rel_transfer {Q P : Program} {ρ : String → String} {S : String → Bool}
    (h : AgreesOn Q P ρ S) (rd : Reader) {f : String} (hf : S f = true) (args rets : List E) :
    Q.Rel rd f args rets ↔ P.Rel rd (ρ f) args rets :=
  exists_congr fun n ↦ relN_transfer h rd n f hf args rets

end
end LeanVM.Guest.Core
