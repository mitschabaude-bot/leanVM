/-
  LeanVM.SaltedGuest.B1.VerifySub.TablesS

  The tables' segment with the second digest's claims, from the deployed one's run.
-/

module

public import LeanVM.SaltedGuest.B1.VerifySub.Accept2
public import LeanVM.SecondDigest.Program

/-!
# The tables' segment with a second digest

`tablesSeg₂` is the deployed `Tables.tablesSeg` followed by the second digest's three claims at the
public challenge, once the memory holds four words (`tablesSeg₂_eq`); the challenge is the first
coordinate of the point of the last claim `tablesSeg` returns (`pubChallengeOf`, the public input's
third claim's). So a deployed run of `tablesSeg` is a run of `tablesSeg₂` returning its claims and
the second ones (`runsTo_tablesSeg₂`).
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

end
end LeanVM.SaltedGuest.B1.VerifySub
