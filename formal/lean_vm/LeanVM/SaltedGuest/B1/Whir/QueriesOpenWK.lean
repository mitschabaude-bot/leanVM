/-
  LeanVM.SaltedGuest.B1.Whir.QueriesOpenWK

  A level's salted queries with their witness named: the openings `toOpening` builds of the queries'
  witness and the cap's cells pass `openOne` at the keyed hash, and the queries' sum is the Spec's.
-/

module

public import LeanVM.SaltedGuest.B1.Merkle.OpenK
public import LeanVM.Guest.B1.Whir.LvQW

/-!
# The salted queries' openings

`QueryOpensSK S`, `MeaningOpeningQueriesWK S`: the deployed `QueryOpensS`,
`MeaningOpeningQueriesW` with each leaf hashed and climbed under the key of the seed `S`;
`LvQWK`: a level's salted `opening_queries` calls sound with their queries named, under every seed
whose key the cap's buffer holds after its cells. `queries_open_wK`: the deployed `queries_open_w`
over a cap checked under the key (`MeaningCapK`), each opening passing `openOneWithHash
(keyedHash S)` (`Merkle.query_openOne_wK`).
-/

namespace LeanVM.SaltedGuest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Guest.B1.Whir LeanVM.SaltedGuest.B1 LeanVM.SaltedGuest.B1.Merkle
open Recursion.Salted

@[expose] public section

variable {rd : Reader}

/-- **A query's opening under the seed `S`**: the deployed `QueryOpensS` with the leaf hashed and
climbed under the key of `S`. -/
def QueryOpensSK (S : Digest) (rd : Reader) (base I depth cd : ℕ) (cap flags wp : E) (q : ℕ) (row : List K)
    (sibs : List Digest) (d : E) : Prop :=
  row.length = (if base = 1 then I else 3 * I) ∧ sibs.length = depth - cd ∧
    ∃ w : ℕ → E,
      (∀ l < rowLo I + I / rowLo I, LoadHolds rd wp l (w l)) ∧
      LoadHolds rd cap (2 * (2 ^ cd + q / 2 ^ (depth - cd)))
        (digestHalves (climbK S (keyedHash S (row.flatMap K.toBytes)) q sibs)).1 ∧
      LoadHolds rd cap (2 * (2 ^ cd + q / 2 ^ (depth - cd)) + 1)
        (digestHalves (climbK S (keyedHash S (row.flatMap K.toBytes)) q sibs)).2 ∧
      LoadHolds rd flags (2 ^ (cd - 1) + q / 2 ^ (depth - cd + 1)) 1 ∧
      d = rowDot base I row w

/-- **The salted `opening_queries`' meaning under the seed `S`, its queries those of `ws`**: the
deployed `MeaningOpeningQueriesW` with each query's opening `QueryOpensSK S`. -/
def MeaningOpeningQueriesWK (S : Digest) (odd base I depth cd : ℕ) (rd : Reader) (ws : List QW) :
    List E → List E → Prop
  | [cap, flags, lam, lamN, qptrs, wp, nG], rets =>
      ∃ N < ordG, nG = gen ^ N ∧ lam ≠ 0 ∧ ws.length = oqCount odd base N ∧
        ∃ (bps : ℕ → E) (ds : ℕ → E),
          (∀ k < oqCount odd base N, LoadHolds rd qptrs k (bps k) ∧
            (ws.getD k default).1 < 2 ^ depth ∧
            (∀ i < qwN depth cd,
              LoadHolds rd (bps k) i (gen ^ qwVal depth cd (ws.getD k default).1 i)) ∧
            QueryOpensSK S rd base I depth cd cap flags wp (ws.getD k default).1
              (ws.getD k default).2.1 (ws.getD k default).2.2 (ds k)) ∧
          ∃ ch : E, (∀ i ≤ N, LoadHolds rd ch i (oqChain odd base lam⁻¹ ds i)) ∧
            rets = [oqChain odd base lam⁻¹ ds N * lamN]
  | _, _ => False

/-- A level's salted `opening_queries` calls of `C`, sound with their queries `W` at the call's
words under every seed whose key the cap's buffer holds after its cells. -/
def LvQWK (rd : Reader) (C : CallRel) (lvl : ℕ) (lv : OsLv) (W : List E → List E → List QW) :
    Prop :=
  ∀ args rets, C (oqNameOf lvl lv) args rets →
    args.getD 6 0 = gen ^ (lv.queries / (1 + if lvl = 0 then 1 else 0)) →
    lv.queries / (1 + if lvl = 0 then 1 else 0) < ordG → lv.capDepth ≤ lv.depth →
    (∀ N, args.getD 6 0 = gen ^ N → N < ordG → QueryWinsOk rd (args.getD 4 0)
      (oqCount (lv.queries % 2 * (if lvl = 0 then 1 else 0)) (if lvl = 0 then 1 else 0) N)
      lv.depth lv.capDepth) →
    ∀ S : Digest, (∀ c : Fin 13, LoadHolds rd (args.getD 0 0) (4 * 2 ^ lv.capDepth + c.val)
      (keyCells S c)) →
    MeaningOpeningQueriesWK S (lv.queries % 2 * (if lvl = 0 then 1 else 0))
      (if lvl = 0 then 1 else 0) lv.interleave lv.depth lv.capDepth rd (W args rets) args rets

/-- **The salted queries' openings and sum, named**: the deployed `queries_open_w` under the key of
`S`, each opening passing `openOne` at the keyed hash. -/
theorem queries_open_wK {odd base I depth cd q N0 : ℕ} {cap flags lam lamN qptrs wp nG sum r0 r1 : E}
    {root : Digest} {ws : List QW} {cap0 : E} (hc0 : cap0 = cap)
    {S : Digest} (hm : MeaningOpeningQueriesWK S odd base I depth cd rd ws [cap, flags, lam, lamN, qptrs, wp, nG]
      [sum])
    (hcap : MeaningCapK (2 ^ cd) rd [cap, flags] [r0, r1])
    (hkey : ∀ c : Fin 13, LoadHolds rd cap (4 * 2 ^ cd + c.val) (keyCells S c))
    (hroot : (r0, r1) = digestHalves root) (hcd : 2 ≤ cd) (hcd8 : cd ≤ 8) (hcdd : cd ≤ depth)
    (hnG : nG = gen ^ N0) (hN0 : N0 < ordG) (hQ : oqCount odd base N0 = q) (hodd : odd ≤ 1)
    (hb : base = 1 ∨ (base = 0 ∧ odd = 0))
    (qs : List ℕ) (hqsl : qs.length = q) (hqlt : ∀ k < q, qs.getD k 0 < 2 ^ depth)
    (hbits : ∀ k < q, ∃ bp, LoadHolds rd qptrs k bp ∧
      FrameRun rd bp (qwN depth cd) fun i ↦ gen ^ qwVal depth cd (qs.getD k 0) i)
    (hlamN : lamN = lam ^ q) {width : ℕ} (hwidth : (if base = 1 then I else 3 * I) = width)
    (specRow : List K → List E) (fd : List E)
    (hdot : ∀ (row : List K) (w : ℕ → E), row.length = width →
      (∀ l < rowLo I + I / rowLo I, LoadHolds rd wp l (w l)) →
        rowDot base I row w = dot (specRow row) (eqKernel fd)) :
    (ws.map (toOpening rd cap0 cd depth)).length = q ∧
      (∀ k (hk : k < qs.length) (ho : k < (ws.map (toOpening rd cap0 cd depth)).length),
        Id.run (Compile.openOneWithHash (m := Id) (keyedHash S) root depth width qs[k]
          (ws.map (toOpening rd cap0 cd depth))[k]) = true) ∧
      sum = enforcedSum (((ws.map (toOpening rd cap0 cd depth)).map (·.leaf)).map specRow) fd
        (powers lam q) ∧
      (ws.map (toOpening rd cap0 cd depth)).map Opening.leafIndex = qs := by
  subst hc0
  obtain ⟨N, hN, hnG', hlam, hwl, bps, ds, hall, ch, -, hret⟩ := hm
  have hNN : N = N0 := gen_pow_inj hN hN0 (hnG'.symm.trans hnG)
  subst hNN
  rw [hQ] at hwl hall
  have hql : (ws.map (toOpening rd cap0 cd depth)).length = q := by rw [List.length_map, hwl]
  -- the positions
  have hqs' : ∀ k < q, (ws.getD k default).1 = qs.getD k 0 := by
    intro k hk
    obtain ⟨hbp, hlt, hb', -⟩ := hall k hk
    obtain ⟨bp, hbp', hbits'⟩ := hbits k hk
    have e := loadHolds_unique hbp hbp'
    subst e
    exact winPos_unique hcd8 hlt (hqlt k hk) hb' hbits'
  have hget : ∀ k (hk : k < q), (ws.map (toOpening rd cap0 cd depth))[k]'(by rw [hql]; exact hk) =
      toOpening rd cap0 cd depth (ws.getD k default) := by
    intro k hk
    rw [List.getElem_map, List.getD_eq_getElem _ _ (by rw [hwl]; exact hk)]
  refine ⟨hql, fun k hk ho ↦ ?_, ?_, ?_⟩
  · have hkq : k < q := by rw [hql] at ho; exact ho
    obtain ⟨-, hlt, -, hop⟩ := hall k hkq
    obtain ⟨hrow, hsl, w, -, h0, h1, hfl, -⟩ := hop
    rw [hget k hkq, ← List.getD_eq_getElem _ 0 hk, ← hqs' k hkq]
    exact query_openOne_wK hcd hcdd hcap hkey hroot hlt (hrow.trans hwidth) hsl h0 h1 hfl
  · have hds : ∀ k < q, ds k = dot (specRow (ws.getD k default).2.1) (eqKernel fd) := by
      intro k hk
      obtain ⟨-, -, -, hrow, -, w, hw, -, -, -, hd⟩ := hall k hk
      rw [hd]
      exact hdot _ _ (hrow.trans hwidth) hw
    obtain ⟨hret, -⟩ := List.cons_eq_cons.mp hret
    rw [hret, hlamN, ← hQ, oqChain_powers hlam hodd hb, hQ]
    have hrl : (((ws.map (toOpening rd cap0 cd depth)).map (·.leaf)).map specRow).length = q := by
      simp [hwl]
    rw [← hrl, enforcedSum_eq, hrl]
    unfold powSum
    have hL : ∀ k < q, (((ws.map (toOpening rd cap0 cd depth)).map (·.leaf)).map specRow).getD k [] =
        specRow (ws.getD k default).2.1 := by
      intro k hk
      rw [List.getD_eq_getElem _ _ (by simp [hwl]; omega), List.getD_eq_getElem _ _ (by omega)]
      simp [toOpening]
    have hmap : (List.range q).map (fun k ↦ lam ^ k * ds k) =
        (List.range q).map (fun k ↦ lam ^ k *
          dot ((((ws.map (toOpening rd cap0 cd depth)).map (·.leaf)).map specRow).getD k [])
            (eqKernel fd)) := by
      refine List.map_congr_left fun k hk ↦ ?_
      have hk' : k < q := List.mem_range.mp hk
      rw [hds k hk', hL k hk']
    rw [hmap]
  · apply List.ext_getElem (by simp [hwl, hqsl])
    intro k h1 h2
    have hk : k < q := by simpa [hwl] using h1
    have e := hqs' k hk
    rw [List.getD_eq_getElem _ _ (by rw [hwl]; exact hk), List.getD_eq_getElem _ _ h2] at e
    simpa [toOpening] using e

end
end LeanVM.SaltedGuest.B1.Whir
