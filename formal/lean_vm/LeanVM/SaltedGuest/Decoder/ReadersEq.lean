/-
  LeanVM.SaltedGuest.Decoder.ReadersEq

  The salted decoder's compiled readers are the salted decoding's readers at a frame map keyed by
  the callees' indices.
-/

module

public import LeanVM.SaltedGuest.Decoder.Readers
public import LeanVM.SaltedGuest.B1.Main.SoundVK
public import LeanVM.SaltedGuest.B1.Whir.OsSame

/-!
# The salted readers, compiled, are the decoding's

At a frame map `Vn` keyed by the salted functions' indices, and the frame map by name
`byName Vn f = Vn (nameIndex f)` (the salted replayed frame map is so, `Located.frameVFastNK_nameIndex`):

* the callees' indices: `nameIndex` of the readers' callees (`nameIndex_of`, the salted core IR's
  entries by the kernel's `rfl`), and the unchanged signature functions kept by the renaming
  (`Whir.sameOf`), so `toDV (byName Vn)` reads them at their salted indices;
* **`xmssAtFrameTK_eq`**, **`sphincsAtFrameTK_eq`** (at `Vn = frameAtAK table locs rd`),
  **`daAtFrameK_eq`**, **`hintsAtFrameK_eq`**: the compiled readers are the witnesses
  `B1.Main.decWitK` reads.
-/

namespace LeanVM.SaltedGuest.Decoder

open LeanVM.Parameters LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.Fast LeanVM.Guest.B1.Da
open LeanVM.Extraction.Fast LeanVM.Protocol.Verifier LeanVM.Node LeanVM.Cost.Decoder
open LeanVM.SaltedGuest.B1

@[expose] public section

/-- A frame map keyed by the salted functions' indices, read by name. -/
noncomputable def byName (Vn : NFrames) : End.FrameMap := fun f ↦ Vn (nameIndex f)

/-! ## The callees' indices -/

theorem nameIndex_of {k : ℕ} {g : Fn} (hk : SaltedGuest.coreProgram[k]? = some g) :
    nameIndex g.name = k + 1 := by
  obtain ⟨hl, hg⟩ := List.getElem?_eq_some_iff.mp hk
  unfold nameIndex
  rw [← hg, findIdx_name_of_nodup coreProgram_names_nodup hl]

set_option maxRecDepth 100000

kernel_rfl rc38 : SaltedGuest.coreProgram[38]? = some LeanVM.SaltedGuest.Data.core38
kernel_rfl rc20 : SaltedGuest.coreProgram[20]? = some LeanVM.SaltedGuest.Data.core20
kernel_rfl rc19 : SaltedGuest.coreProgram[19]? = some LeanVM.SaltedGuest.Data.core19
kernel_rfl rc27 : SaltedGuest.coreProgram[27]? = some LeanVM.SaltedGuest.Data.core27
kernel_rfl rc30 : SaltedGuest.coreProgram[30]? = some LeanVM.SaltedGuest.Data.core30
kernel_rfl rc31 : SaltedGuest.coreProgram[31]? = some LeanVM.SaltedGuest.Data.core31
kernel_rfl rc393 : SaltedGuest.coreProgram[393]? = some LeanVM.SaltedGuest.Data.core393
kernel_rfl rc35 : SaltedGuest.coreProgram[35]? = some LeanVM.SaltedGuest.Data.core35
kernel_rfl rc18 : SaltedGuest.coreProgram[18]? = some LeanVM.SaltedGuest.Data.core18

theorem idx_loop2 : nameIndex "__loop2" = 39 := nameIndex_of rc38
theorem idx_verify_sig_lean_sphincs : nameIndex "verify_sig_lean_sphincs" = 21 := nameIndex_of rc20
theorem idx_sp_wots : nameIndex "sp_wots" = 20 := nameIndex_of rc19
theorem idx_da_verify : nameIndex "da_verify" = 28 := nameIndex_of rc27
theorem idx_da_verify_column : nameIndex "da_verify_column" = 31 := nameIndex_of rc30
theorem idx_da_verify_cell : nameIndex "da_verify_cell" = 32 := nameIndex_of rc31
theorem idx_loop26 : nameIndex "__loop26" = 394 := nameIndex_of rc393
theorem idx_aggregate_claims : nameIndex "aggregate_claims" = 36 := nameIndex_of rc35
theorem idx_verify_sub : nameIndex "verify_sub" = 19 := nameIndex_of rc18

kernel_rfl sc16 : Same.closed[16]? = some ("sp_wots", 19, 19)
kernel_rfl sc17 : Same.closed[17]? = some ("verify_sig_lean_sphincs", 20, 20)
kernel_rfl sc25 : Same.closed[25]? = some ("__loop2", 38, 36)
kernel_rfl dc19 : Guest.coreProgram[19]? = some LeanVM.Guest.Data.core19
kernel_rfl dc20 : Guest.coreProgram[20]? = some LeanVM.Guest.Data.core20
kernel_rfl dc36 : Guest.coreProgram[36]? = some LeanVM.Guest.Data.core36

theorem same_sp_wots : Same.inS "sp_wots" = true ∧ Same.rho "sp_wots" = "sp_wots" :=
  Whir.sameOf sc16 dc19 rfl
theorem same_verify_sig_lean_sphincs :
    Same.inS "verify_sig_lean_sphincs" = true ∧
      Same.rho "verify_sig_lean_sphincs" = "verify_sig_lean_sphincs" :=
  Whir.sameOf sc17 dc20 rfl
theorem same_loop2 : Same.inS "__loop2" = true ∧ Same.rho "__loop2" = "__loop2" :=
  Whir.sameOf sc25 dc36 rfl

/-- An unchanged function kept by the renaming, read through `toDV`, is read at its own name. -/
theorem toDV_same (V : End.FrameMap) {f : String} (h : Same.inS f = true ∧ Same.rho f = f) :
    toDV V f = V f := by
  funext args rets
  have := toDV_rho V h.1 args rets
  rwa [h.2] at this

/-! ## The readers -/

/-- **The leanXMSS reader, compiled, is the decoding's.** -/
theorem xmssAtFrameTK_eq (table : Array (Guest.Located.CallKey × K)) (locs : Array (Array ℕ))
    (rd : Reader) :
    xmssAtFrameTK readerTabs table locs rd =
      fun args ↦ Sig.xmssSigOf (toDV (byName (frameAtAK table locs rd)) "__loop2" args []) := by
  funext args
  rw [xmssAtFrameTK, ← frameAtAK_eq_frameValAtK, toDV_same _ same_loop2, byName, idx_loop2,
    show readerTabs.xmss = xmssTabs from rfl, xmssSigOfA_tabs, xmssSigOfN_eq]

/-- **The leanSPHINCS reader, compiled, is the decoding's.** -/
theorem sphincsAtFrameTK_eq (table : Array (Guest.Located.CallKey × K)) (locs : Array (Array ℕ))
    (rd : Reader) (w47 : E) :
    sphincsAtFrameTK readerTabs table locs rd w47 =
      fun p ↦ Sig.sphincsSigOf (toDV (byName (frameAtAK table locs rd)) "verify_sig_lean_sphincs"
        [p, w47] []) (toDV (byName (frameAtAK table locs rd))) := by
  funext p
  have hN := sphincsSigOfN_eq ((frameAtAK table locs rd 21 [p, w47] []))
    (toDV (byName (frameAtAK table locs rd)))
  simp only [sphincsSigOfN, name_sp_wots, toDV_same _ same_sp_wots, byName, idx_sp_wots] at hN
  rw [toDV_same _ same_verify_sig_lean_sphincs, byName, idx_verify_sig_lean_sphincs, ← hN,
    sphincsAtFrameTK, sphincsAtFpK]
  simp only [← frameAtAK_eq_frameValAtK, show readerTabs.sphincs = spTabs from rfl]

theorem cellSymsOfSK_eq (σ : Val) : cellSymsOfSK σ = Da.cellSymsOfS σ := by
  unfold cellSymsOfSK Da.cellSymsOfS cellSymsOf
  apply List.map_congr_left
  intro j _
  simp only [Function.comp_apply, shiftV, V.n]
  rfl

/-- **The DA reader, compiled, is the decoding's.** -/
theorem daAtFrameK_eq (Vn : NFrames) (key : E) :
    daAtFrameK discreteLogTables Vn key =
      fun args rets ↦ Da.dvWitK (byName Vn "da_verify" (args ++ [key]) rets) (byName Vn) := by
  funext args rets
  simp only [daAtFrameK, dvWitNDK, dvWitNAtK, dvWitNColsK, Da.dvWitK, byName, idx_da_verify,
    gLogD_tables, daRowCount_eq]
  generalize Vn 28 (args ++ [key]) rets = σ
  rw [show min (Main.gLog (σ (V.n 2))) 1024 = Da.dvRowsS σ from rfl]
  congr 1
  refine congrArg (daRows _) (funext fun i ↦ funext fun h ↦ ?_)
  simp only [dvSymsColsK, Da.dvSymsPS]
  by_cases hc : i < Da.dvRowsS σ ∧ h < 128
  · have hcol : (dvColsK σ Vn).getD h (0, 0) = (dvColVNK σ Vn h (.n 14), dvColVNK σ Vn h (.n 15)) := by
      simp [dvColsK, dvColWordsK, colWordsOfK, Array.getD_eq_getD_getElem?, hc.2]
    simp only [hc.1, hc.2, and_self, ↓reduceIte]
    rw [hcol]
    simp only [dvSymsCellK, cellSymsAtK, dvRowVWK, dvColVNK, Da.dvSymsS, Da.colSymsS, Da.colRowVS,
      dvColArgsK, Da.dvColArgsS, byName, idx_da_verify_column, idx_loop26, idx_da_verify_cell,
      cellSymsOfSK_eq, LeanVM.Guest.Value.gen_pow_eq_ofK, List.getD_cons_succ, List.getD_cons_zero]
  · simp only [hc, ↓reduceIte]

/-- **The batching's reader, compiled, is the decoding's.** -/
theorem hintsAtFrameK_eq (rd : Reader) (Vn : NFrames) (s0 s1 : E) :
    hintsAtFrameK rd Vn s0 s1 =
      fun args ↦ Main.aggHintsS rd (byName Vn "aggregate_claims" ([s0, s1] ++ args) []) := by
  funext args
  rw [hintsAtFrameK, byName, idx_aggregate_claims]
  rfl

end

end LeanVM.SaltedGuest.Decoder
