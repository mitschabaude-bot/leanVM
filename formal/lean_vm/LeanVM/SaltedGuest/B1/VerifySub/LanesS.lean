/-
  LeanVM.SaltedGuest.B1.VerifySub.LanesS

  The salted `verify_sub`'s output lanes.
-/

module

public import LeanVM.SaltedGuest.B1.VerifySub.FrontAll
public import LeanVM.Guest.B1.VerifySub.LanesK

/-!
# The salted output lanes

`vs_lanesS`: the deployed `vs_lanes` for the salted front (`VsFrontS`): the `25` output lanes'
claims among the tables' segment's are on `KECCAK`'s output columns at the table sumcheck's point
cut to the table's height, their values at `col_eval_words·g^107` (`col_eval_words` at `655`).
-/

namespace LeanVM.SaltedGuest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub

@[expose] public section

/-- The GKR's capacity: `verify_bus_gkr`'s first five return words. -/
theorem VsFrontS.capG_eq {bytecode : List K} {C : CallRel} {rd : Reader} {σ : Val}
    (F : VsFrontS bytecode C rd σ) :
    F.capG = [σ (.n 636), σ (.n 637), σ (.n 638), σ (.n 639), σ (.n 640)] := by
  have h := F.hretG
  rw [show [σ (.n 636), σ (.n 637), σ (.n 638), σ (.n 639), σ (.n 640), σ (.n 641), σ (.n 642),
    σ (.n 643), σ (.n 644)] = ([σ (.n 636), σ (.n 637), σ (.n 638), σ (.n 639), σ (.n 640)] ++
      [σ (.n 641)]) ++ [σ (.n 642), σ (.n 643), σ (.n 644)] from rfl] at h
  obtain ⟨h1, -⟩ := List.append_inj' h (by rw [F.hvL]; rfl)
  exact (List.append_inj' h1 rfl).1.symm

/-- The claimed fixed polynomial value at the bus's bytecode point. -/
def vsFixedS (σ : Val) (point : List E) : BytecodeClaim :=
  ⟨point.take 19 ++ vsAlphaVals σ, σ (.n 653)⟩

/-- **The salted output lanes**, as the deployed `vs_lanes`: their claims are on `KECCAK`'s output columns at one point, the table
sumcheck's point `chis` cut to the table's height `τ ≤ |chis|`, and their values are
at `col_eval_words·g^107` (claims `112 .. 136`, read in place: `col_eval_words` holds claims `5 .. 163`). -/
theorem vs_lanesS {bytecode : List K} (hbl : bytecode.length = 2 ^ 23) {C : CallRel} {rd : Reader}
    {σ : Val} (F : VsFrontS bytecode C rd σ) :
    ∃ chis : List E, ReadsAt rd (σ (.n 645)) chis ∧ vsTau F.rowsN ≤ chis.length ∧
      (lanesOf F.claims).map (·.column) = keccakOutputColumns ∧
      (∀ c ∈ lanesOf F.claims, c.point = chis.take (vsTau F.rowsN)) ∧
      ReadsAt rd (σ (.n 655) * gen ^ 107) ((lanesOf F.claims).map (·.value)) ∧
      (lanesOf F.claims).length = 25 := by
  have hctx := F.hctx
  simp only [Tables.TCtx] at hctx
  obtain ⟨chis, -, -, hchi, -, -, hcl, hcol, hpts⟩ := hctx
  obtain ⟨hlanes, -⟩ := lanes_eq hcol
  -- the table phase's points
  obtain ⟨sp4, hs4⟩ := carrier_of_squeeze F.hbeta
  obtain ⟨sp5, hs5⟩ := RunsTo.carrier F.hrunG hs4
  rw [F.capG_eq] at hs5
  have hcl' : F.claims.length = 167 := hcl
  have hτdef : vsTau F.rowsN = (Tables.tableHeightsOf F.rowsN).getD 5 0 := rfl
  have hrunT := F.hrunT (claimedBytecodeValue (vsFixedS σ F.r.2.1)) (by
    rw [logBytecode_eq hbl]; exact bytecodeAt_claimed bytecode _ _)
  obtain ⟨pt, hptL, hpt⟩ := RunsTo.always hrunT hs5 (tablesSeg_lanes _ _ _ _ _ _ _)
  rw [layoutOf_heights, show opKeccak = 5 from rfl] at hpt
  rw [layoutOf_heights] at hptL
  have hτpt : vsTau F.rowsN ≤ pt.length := by
    rw [hptL]
    exact mem_le_foldl_max 0 (getD_mem' (by rw [tableHeights_length _ F.hrowsL]; omega))
  -- a lane's point
  have hlane : ∀ i < 25, (F.claims[112 + i]?.map (·.point)) = some (chis.take (vsTau F.rowsN)) ∧
      (chis.take (vsTau F.rowsN)).length = vsTau F.rowsN := by
    intro i hi
    have hlt : 112 + i < F.claims.length := by rw [hcl']; omega
    have hmem : F.claims[112 + i] ∈ (F.claims.drop 112).take 25 := by
      rw [List.mem_iff_getElem]
      exact ⟨i, by simp; omega, by simp⟩
    have hout : F.claims[112 + i].column ∈ keccakOutputColumns := by
      apply claimColumns_lanes
      rw [← hcol, ← List.map_drop, ← List.map_take]
      exact List.mem_map_of_mem hmem
    have e1 := hpt _ (List.getElem_mem hlt) hout
    obtain ⟨-, -, h5, -⟩ := hpts (112 + i) F.claims[112 + i].point (by simp [hlt])
    have e2 := h5 (by omega) (show 112 + i < 164 by omega)
    have hlen : F.claims[112 + i].point.length = vsTau F.rowsN := by
      rw [e1, List.length_take, ← hτdef]; omega
    rw [hlen] at e2
    refine ⟨by simpa [List.getElem?_eq_getElem hlt] using congrArg some e2, by rw [← e2, hlen]⟩
  have hτ : vsTau F.rowsN ≤ chis.length := by
    have := (hlane 0 (by omega)).2
    rw [List.length_take] at this
    omega
  refine ⟨chis, hchi, hτ, ?_, ?_, ?_, ?_⟩
  · rw [hlanes, List.map_take, List.map_drop, hcol]
    exact claimColumns_lanes_eq
  · intro c hc
    rw [hlanes, List.mem_iff_getElem] at hc
    obtain ⟨i, hi, rfl⟩ := hc
    have hi' : i < 25 := by simp at hi; omega
    have := (hlane i hi').1
    simp only [List.getElem_take, List.getElem_drop]
    rw [List.getElem?_eq_getElem (by rw [hcl']; omega)] at this
    simpa using this
  · rw [hlanes]
    intro k hk
    have hk' : k < 25 := by simp [hcl'] at hk; omega
    rw [loadHolds_mul_gen_pow]
    have e2 : Tables.nPooled = 164 := rfl
    have e3 : Tables.nBusClaims = 5 := rfl
    have := F.hcew (107 + k) (by simp [hcl']; omega)
    simp only [List.getElem_map, List.getElem_take, List.getElem_drop] at this ⊢
    convert this using 3
    omega
  · rw [hlanes]; simp [hcl']

end
end LeanVM.SaltedGuest.B1.VerifySub
