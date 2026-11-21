/-
  LeanVM.SaltedGuest.B1.VerifySub.TablesS

  The tables' segment with the second digest's claims, from the deployed one's run.
-/

module

public import LeanVM.SaltedGuest.B1.VerifySub.Accept2
public import LeanVM.SecondDigest.Program
public import LeanVM.SaltedGuest.B1.VerifySub.Template
public import LeanVM.Guest.B1.Tables.Vt.Pi

/-!
# The tables' segment with a second digest

`tablesSeg₂` is the deployed `Tables.tablesSeg` followed by the second digest's three claims at the
public challenge, once the memory holds four words (`tablesSeg₂_eq`); the challenge is the first
coordinate of the point of the last claim `tablesSeg` returns (`pubChallengeOf`, the public input's
third claim's). So a deployed run of `tablesSeg` is a run of `tablesSeg₂` returning its claims and
the second ones (`runsTo_tablesSeg₂`).

`vsSeedClaimsS_holds`: the salted `verify_sub`'s seed claims after `verify_tables` (as
`verify_tables` binds the public input, `Tables.vt_pi`): its seed's two cells are canonical and the
pool's slots `167 .. 169` hold the lines through their limbs `0`, `1` at the challenge `rm`
(`.n 654`) and `0`.
-/

namespace LeanVM.SaltedGuest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Front Recursion.SecondDigest

@[expose] public section

/-- The public challenge, off the claims `tablesSeg` returns: the first coordinate of the last
claim's point. -/
def pubChallengeOf (claims : List ColumnClaim) : E := (claims.getLastD default).point.headD 0

theorem pubChallengeOf_append (cl : List ColumnClaim) (layout : Layout) (pi : Digest) (r : E) :
    pubChallengeOf (cl ++ pubClaims layout pi r) = r := by
  simp [pubChallengeOf, pubClaims, pubPoint, List.getLastD_eq_getLast?, List.getLast?_append]

/-- **With four memory words, `tablesSeg₂` is `tablesSeg` followed by the second digest's
claims.** -/
theorem tablesSeg₂_eq (ev : (List K → List E → VerifierProgram E)) {layout : Layout}
    (h4 : MemoryHasFourWords layout) (pi second : Digest) (alphas : List E) (beta : E)
    (point tv : List E) :
    tablesSeg₂ ev layout pi second alphas beta point tv =
      (Tables.tablesSeg ev layout pi alphas beta point tv).bind fun bc ↦
        VerifierProgram.ret (bc.1, bc.2 ++ secondClaims layout second (pubChallengeOf bc.2)) := by
  unfold tablesSeg₂ Tables.tablesSeg
  simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq, VerifierProgram.bind_assoc,
    VerifierProgram.ret_bind]
  refine congrArg _ (funext fun bus ↦ congrArg _ (funext fun cl ↦ ?_))
  rw [publicInputPhase₂_eq, publicInputPhase_eq, LeanVM.Guest.B1.VerifySub.require_true h4]
  simp only [VerifierProgram.bind_eq, VerifierProgram.ret_bind, VerifierProgram.bind_assoc]
  refine congrArg _ (funext fun r ↦ ?_)
  simp only [pubChallengeOf_append, List.append_assoc]

/-- **A deployed run of `tablesSeg` is a run of `tablesSeg₂`**, with the second digest's claims
after its own. -/
theorem runsTo_tablesSeg₂ {ev : (List K → List E → VerifierProgram E)} {layout : Layout}
    (h4 : MemoryHasFourWords layout) {pi second : Digest} {alphas : List E} {beta : E}
    {point tv : List E} {s s' : Fs} {xs : List E} {bus : BusResult} {claims : List ColumnClaim}
    (h : RunsTo (Tables.tablesSeg ev layout pi alphas beta point tv) s xs (bus, claims) s') :
    RunsTo (tablesSeg₂ ev layout pi second alphas beta point tv) s xs
      (bus, claims ++ secondClaims layout second (pubChallengeOf claims)) s' := by
  rw [tablesSeg₂_eq ev h4]
  have := RunsTo.bind (f := fun bc : BusResult × List ColumnClaim ↦
      (VerifierProgram.ret (bc.1, bc.2 ++ secondClaims layout second (pubChallengeOf bc.2)) :
        VerifierProgram (BusResult × List ColumnClaim))) h (runsTo_ret _ s')
  rw [List.append_nil] at this
  exact this

section Seed

open LeanVM.Guest LeanVM.Guest.Value LeanVM.Guest.B1.VerifySub

variable {C : CallRel} {rd : Reader} {σ : Val} {next : Prop} {kret : List E → Prop}

/-- **The seed's claims**: the seed's cells canonical, and the pool's slots `167 .. 169` the lines
through their limbs at the challenge. -/
theorem vsSeedClaimsS_holds (h : Stmt.HoldsList C rd σ vsSeedClaimsS next kret) :
    IsCanonical128 (σ (.n 2)) ∧ IsCanonical128 (σ (.n 3)) ∧
      LoadHolds rd (σ (.n 6)) 167 (multilinearEval [ofK ((σ (.n 2)).limb 0),
        ofK ((σ (.n 3)).limb 0)] [σ (.n 654)]) ∧
      LoadHolds rd (σ (.n 6)) 168 (multilinearEval [ofK ((σ (.n 2)).limb 1),
        ofK ((σ (.n 3)).limb 1)] [σ (.n 654)]) ∧
      LoadHolds rd (σ (.n 6)) 169 0 ∧ next := by
  simp only [vsSeedClaimsS, vsAdd, vsConst, vsMul, vsLd, Stmt.HoldsList, Stmt.Holds,
    Atom.Holds] at h
  obtain ⟨-, a657, c658, m659, k656, cp660, -, a662, c663, m664, k661, cp665, a666, m667, a668,
    l167, a669, m670, a671, l168, c672, l169, hn⟩ := h
  rw [word_y_inv] at c658 c663
  rw [m659, a657, c658] at k656
  rw [m664, a662, c663] at k661
  obtain ⟨hc2, hl2⟩ := (split_iff _ _).mp k656
  obtain ⟨hc3, hl3⟩ := (split_iff _ _).mp k661
  have hh2 : σ (.n 659) = ofK ((σ (.n 2)).limb 1) := by
    rw [m659, a657, c658, hl2]; exact split_hi hc2
  have hh3 : σ (.n 664) = ofK ((σ (.n 3)).limb 1) := by
    rw [m664, a662, c663, hl3]; exact split_hi hc3
  refine ⟨hc2, hc3, ?_, ?_, ?_, hn⟩
  · have e : multilinearEval [ofK ((σ (.n 2)).limb 0), ofK ((σ (.n 3)).limb 0)] [σ (.n 654)] =
        σ (.n 668) := by
      rw [a668, m667, a666, cp660, cp665, ← hl2, ← hl3]
      simp only [multilinearEval, List.foldl, foldPairs, List.headD]
      ring
    rw [e]; exact l167
  · have e : multilinearEval [ofK ((σ (.n 2)).limb 1), ofK ((σ (.n 3)).limb 1)] [σ (.n 654)] =
        σ (.n 671) := by
      rw [a671, m670, a669, ← hh2, ← hh3]
      simp only [multilinearEval, List.foldl, foldPairs, List.headD]
      ring
    rw [e]; exact l168
  · rw [c672, Tables.tb_word_zero] at l169; exact l169

end Seed

end
end LeanVM.SaltedGuest.B1.VerifySub
