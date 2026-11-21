/-
  LeanVM.SaltedGuest.B1.RunH

  Runs of the Spec's programs with a Merkle hash `H`, and the runs that open nothing, which do not
  depend on it.
-/

module

public import LeanVM.Guest.B1.Whir.Run

/-!
# Runs with a Merkle hash

The deployed guest's proofs read a Spec program by `runId`, the compiled reading at Keccak-256 and
Keccak-f[1600]; the salted guest's verifier authenticates its openings with the keyed hash. Here,
for any hash `H`:

* `runIdH H`: the compiled reading at `H` and Keccak-f[1600]; `RunsWithH H`, the deployed
  `Whir.RunsWith` at `H`, with its combinators (`RunsWithH.bind`, `RunsWithH.of_eq`,
  `runsWithH_ret`, `runsWithH_commitP`).
* `run_hash_free`: a run that consumes no phase of openings does not depend on the hash: the
  reading of a query consumes one. So every deployed `RunsTo` (which keeps the openings) is a run at
  any hash (`RunsTo.toH`, `RunsTo.withRootsH`): the segments of the verifier that open nothing
  (the announced sizes, the bus, the tables, the Keccak segment, the samples) carry over.
-/

namespace LeanVM.SaltedGuest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.B1 LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile

@[expose] public section

/-- The reading of a Spec program at the Merkle hash `H` and Keccak-f[1600]. -/
abbrev runIdH {α : Type} (H : Bytes → Digest) (p : VerifierProgram α) (st : VerifierProgramState) :
    Option (α × VerifierProgramState) :=
  Compile.runWithHash (m := Id) H keccakF1600 p st

/-- **A run at the hash `H`**: from any Spec sponge the guest carries as `s`, the program `p` reads
exactly the stream words `xs` and the phases of openings `os`, the commitments read so far being
`roots`, and returns `a`, leaving a sponge the guest carries as `s'` and the commitments `roots'`,
on any rest of the stream and of the phases. -/
def RunsWithH {α : Type} (H : Bytes → Digest) (p : VerifierProgram α) (s : Fs) (xs : List E)
    (os : List (List Opening)) (roots : List (Digest × ℕ × ℕ)) (a : α) (s' : Fs)
    (roots' : List (Digest × ℕ × ℕ)) : Prop :=
  ∀ sp : Sponge, s.Carries sp → ∀ (rest : List E) (orest : List (List Opening)),
    ∃ sp' : Sponge, s'.Carries sp' ∧
      runIdH H p ⟨sp, xs ++ rest, os ++ orest, roots⟩ = some (a, ⟨sp', rest, orest, roots'⟩)

variable {H : Bytes → Digest}

theorem run_bindH {α β : Type} (p : VerifierProgram α) (f : α → VerifierProgram β)
    (st : VerifierProgramState) :
    runIdH H (p.bind f) st = (runIdH H p st).bind (fun r => runIdH H (f r.1) r.2) := by
  induction p generalizing st with
  | ret a => rfl
  | fail => rfl
  | read k ih =>
    simp only [runIdH, VerifierProgram.bind, Compile.runWithHash]
    split
    · rfl
    · exact ih _ _
  | sample k ih => exact ih _ _
  | grind b k ih =>
    simp only [runIdH, VerifierProgram.bind, Compile.runWithHash]
    split
    · rfl
    · simp only [bind, pure]
      split
      · exact ih _
      · rfl
  | commit h w k ih =>
    simp only [runIdH, VerifierProgram.bind, Compile.runWithHash]
    split
    · simp only [bind]
      split
      · exact ih _
      · rfl
    · rfl
  | query i ps k ih =>
    simp only [runIdH, VerifierProgram.bind, Compile.runWithHash]
    split
    · simp only [bind]
      split
      · exact ih _ _
      · rfl
    · rfl

theorem runsWithH_ret {α : Type} (a : α) (s : Fs) (roots : List (Digest × ℕ × ℕ)) :
    RunsWithH H (pure a : VerifierProgram α) s [] [] roots a s roots :=
  fun sp h _ _ ↦ ⟨sp, h, rfl⟩

theorem RunsWithH.bind {α β : Type} {p : VerifierProgram α} {f : α → VerifierProgram β}
    {s s1 s2 : Fs} {xs ys : List E} {os1 os2 : List (List Opening)}
    {r0 r1 r2 : List (Digest × ℕ × ℕ)} {a : α} {b : β}
    (h1 : RunsWithH H p s xs os1 r0 a s1 r1) (h2 : RunsWithH H (f a) s1 ys os2 r1 b s2 r2) :
    RunsWithH H (p.bind f) s (xs ++ ys) (os1 ++ os2) r0 b s2 r2 := by
  intro sp hs rest orest
  obtain ⟨sp1, hs1, e1⟩ := h1 sp hs (ys ++ rest) (os2 ++ orest)
  obtain ⟨sp2, hs2, e2⟩ := h2 sp1 hs1 rest orest
  refine ⟨sp2, hs2, ?_⟩
  rw [run_bindH, List.append_assoc, List.append_assoc, e1]
  exact e2

theorem RunsWithH.of_eq {α : Type} {p : VerifierProgram α} {s s' t t' : Fs} {xs xs' : List E}
    {os os' : List (List Opening)} {r r' q q' : List (Digest × ℕ × ℕ)} {a a' : α}
    (h : RunsWithH H p s xs os r a t q) (hs : s = s') (hx : xs = xs') (ho : os = os')
    (hr : r = r') (ha : a = a') (ht : t = t') (hq : q = q') : RunsWithH H p s' xs' os' r' a' t' q' := by
  subst hs hx ho hr ha ht hq; exact h

/-- **A commitment** reads the root's two scalars, absorbs them, and appends the root with its
shape. -/
theorem runsWithH_commitP (s : Fs) (x0 x1 : E) {d : Digest}
    (hd : digestFromHalves (x0, x1) = some d) (height width : ℕ) (roots : List (Digest × ℕ × ℕ)) :
    RunsWithH H (VerifierProgram.readCommitment height width) s [x0, x1] [] roots ()
      ((s.absorb x0 dsObserve).absorb x1 dsObserve) (roots ++ [(d, height, width)]) := by
  intro sp hs rest orest
  have h1 := carries_absorb hs x0 dsObserve
  have h2 := carries_absorb h1 x1 dsObserve
  refine ⟨_, h2, ?_⟩
  show (match digestFromHalves (x0, x1) with
    | some root => runIdH H (VerifierProgram.ret ()) _
    | none => none) = _
  rw [hd]
  rfl

/-! ## Runs that open nothing -/

/-- **A run consumes phases of openings, and one that consumes none does not depend on the
hash.** -/
theorem run_hash_free {α : Type} (H H' : Bytes → Digest) (p : VerifierProgram α) :
    ∀ (st : VerifierProgramState) (r : α × VerifierProgramState), runIdH H p st = some r →
      r.2.openings.length ≤ st.openings.length ∧
        (r.2.openings.length = st.openings.length → runIdH H' p st = some r) := by
  induction p with
  | ret a =>
    intro st r h
    simp only [runIdH, Compile.runWithHash, pure, Option.some.injEq] at h
    subst h
    exact ⟨le_rfl, fun _ ↦ rfl⟩
  | fail => intro st r h; cases h
  | read k ih =>
    intro st r h
    simp only [runIdH, Compile.runWithHash] at h ⊢
    split at h
    · cases h
    · rename_i x xs hs
      obtain ⟨h1, h2⟩ := ih x _ r h
      exact ⟨h1, h2⟩
  | sample k ih =>
    intro st r h
    exact ih (Compile.squeeze (m := Id) keccakF1600 st.sponge).1
      { st with sponge := (Compile.squeeze (m := Id) keccakF1600 st.sponge).2 } r h
  | grind b k ih =>
    intro st r h
    simp only [runIdH, Compile.runWithHash] at h ⊢
    split at h
    · cases h
    · rename_i n xs hs
      simp only [bind, pure] at h ⊢
      split at h
      · rename_i hp
        obtain ⟨h1, h2⟩ := ih _ r h
        refine ⟨h1, fun he ↦ ?_⟩
        simp only [hp, ↓reduceIte]
        exact h2 he
      · cases h
  | commit hgt w k ih =>
    intro st r h
    simp only [runIdH, Compile.runWithHash] at h ⊢
    split at h
    · rename_i x0 x1 xs hs
      simp only [bind] at h ⊢
      split at h
      · rename_i root hr
        obtain ⟨h1, h2⟩ := ih _ r h
        refine ⟨h1, fun he ↦ ?_⟩
        exact h2 he
      · cases h
    · cases h
  | query i ps k ih =>
    intro st r h
    simp only [runIdH, Compile.runWithHash] at h
    split at h
    · rename_i root hgt w phase rest hr ho
      simp only [bind] at h
      split at h
      · rename_i rows _
        obtain ⟨hle, -⟩ := ih rows _ r h
        have hl : st.openings.length = rest.length + 1 := by rw [ho]; rfl
        simp only at hle
        refine ⟨by omega, fun he ↦ ?_⟩
        omega
      · cases h
    · cases h

/-- **A deployed run that keeps the openings is a run at any hash.** -/
theorem runId_toH {α : Type} {p : VerifierProgram α} {st st' : VerifierProgramState} {a : α}
    (h : runId p st = some (a, st')) (ho : st'.openings = st.openings) :
    runIdH H p st = some (a, st') :=
  (run_hash_free keccak256 H p st (a, st') h).2 (by rw [ho])

/-- **A deployed run of a segment that opens nothing is a run at any hash.** -/
theorem RunsTo.withRootsH {α : Type} {p : VerifierProgram α} {s s' : Fs} {xs : List E} {a : α}
    (h : RunsTo p s xs a s') (roots : List (Digest × ℕ × ℕ)) :
    RunsWithH H p s xs [] roots a s' roots := fun sp hs rest orest ↦ by
  obtain ⟨sp', hs', e⟩ := h sp hs rest ([] ++ orest) roots
  exact ⟨sp', hs', runId_toH e rfl⟩

end
end LeanVM.SaltedGuest.B1
