/-
  LeanVM.SaltedGuest.B1.Extract

  A statement of a block that holds, read off by its index.
-/

module

public import LeanVM.Guest.CoreLemmas

/-!
# Statements by index

A prefix `body.take n` that holds gives each of its statements whose predecessors have no `ret`:
`holds_of_take` its relation, `atom_of_take` an atom's, `call_of_take` a call's (the callee's
relation on the words of the arguments and returns). With the statement found by the kernel
(`body[i]? = some s`) and the predecessors' `noRetList` decided, a fact a prefix establishes is read
off the core IR without a template of the whole function.
-/

namespace LeanVM.Guest.Core

open LeanVM.Parameters

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}

theorem take_eq_cons {body : List Stmt} {n i : ℕ} {s : Stmt} (hin : i < n)
    (hb : body[i]? = some s) :
    body.take n = body.take i ++ s :: (body.drop (i + 1)).take (n - (i + 1)) := by
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp hb
  conv_lhs => rw [show n = i + ((n - (i + 1)) + 1) by omega, List.take_add,
    List.drop_eq_getElem_cons hi, List.take_succ_cons]

/-- **A statement of a prefix that holds**, its predecessors without a `ret`. -/
theorem holds_of_take {body : List Stmt} {n i : ℕ} {s : Stmt}
    (h : Stmt.HoldsList C rd σ (body.take n) True kret) (hin : i < n) (hb : body[i]? = some s)
    (hnr : Stmt.noRetList (body.take i) = true) :
    Stmt.Holds C rd σ s (Stmt.HoldsList C rd σ ((body.drop (i + 1)).take (n - (i + 1))) True kret)
      kret := by
  rw [take_eq_cons hin hb, holdsList_append, holdsList_noRet _ hnr] at h
  exact h.2

/-- **An atom of a prefix that holds.** -/
theorem atom_of_take {body : List Stmt} {n i : ℕ} {a : Atom}
    (h : Stmt.HoldsList C rd σ (body.take n) True kret) (hin : i < n)
    (hb : body[i]? = some (.atom a)) (hnr : Stmt.noRetList (body.take i) = true) :
    a.Holds rd σ :=
  (holds_of_take h hin hb hnr).1

/-- **A call of a prefix that holds**: the callee's relation on the words. -/
theorem call_of_take {body : List Stmt} {n i : ℕ} {f : String} {args rets : List V}
    (h : Stmt.HoldsList C rd σ (body.take n) True kret) (hin : i < n)
    (hb : body[i]? = some (.call f args rets)) (hnr : Stmt.noRetList (body.take i) = true) :
    C f (args.map σ) (rets.map σ) :=
  (holds_of_take h hin hb hnr).1

end
end LeanVM.Guest.Core
