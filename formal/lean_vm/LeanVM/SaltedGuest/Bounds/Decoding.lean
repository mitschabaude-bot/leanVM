/-
  LeanVM.SaltedGuest.Bounds.Decoding

  The salted decoder's decodings on a valid execution: the children's claims, the DA matrix's
  rows, the encoded size.
-/

module

public import LeanVM.SaltedGuest.Bounds.Valid
public import LeanVM.SaltedGuest.EndDecoder

/-!
# The salted decoder's decodings on a valid execution

Every decoding the salted decoder program outputs, within its size and price, is its top's
(`outputWithin_saltedDecoder_any`), which is `B1.Main.decK B1.VerifySub.vsPiOfK` at the compiled
frame map by name (`decTopK_form`); on a valid execution for a public input of two digests it is
the decoding by replay off the memory (`output_valid`), whose counts `main`'s checks bound
(`countsK_valid`). So, over the executions `SaltedGuest.KnowledgeSound` quantifies over
(`ValidExecution₂`):

* **`childClaims_valid`**: every child of a decoding the decoder outputs has at most `2^20`
  signature claims (a child's claims are slots of the two regions, `kidSlots_length_le`, at most
  `2^20` together, `main`'s cap);
* **`stmtClaims_valid`**: the decoding's own statement has at most `2^20` signature claims (its
  declared claims of both schemes together, at most the regions' slots);
* **`hints_le`**: its batching hints have at most `23` sumcheck messages, on every execution;
* **`daRows_le`**: the DA matrix of every decoding the decoder outputs has at most
  `LeanDa.maxRows = 1024` rows, on every execution (the decoder reads at most `1024` rows,
  `dvWitK_ok`); on a valid execution this also follows from the node relation (`OpensUnder`);
* **`decodingSize_valid`**: every decoding its output decodes to has an encoding of size at most
  `decodingSizeBoundValid = 346031412918` (about `2^38.33`): at most `16` children, the declared
  claims of both schemes together, a child's claims and the raw signatures of each scheme at most
  `2^20`, a child's proof within `21475247062` (its stream's words at most `2^32 + 121`, the
  dispatch table's openings), the DA matrix within `1024` rows of `32768` symbols, the batching's
  `23` rounds. The children's proofs dominate.
-/

namespace LeanVM.SaltedGuest.Bounds

open LeanVM.Cost LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Fast
open LeanVM.Guest.B1 LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Node LeanVM.Cost.Decoder
open LeanVM.SaltedGuest.Decoder LeanVM.SaltedGuest.End LeanVM.SaltedGuest.Check
open Recursion.Salted Recursion.SecondDigest

@[expose] public section

/-! ## The decodings the decoder outputs -/

/-- The compiled top's decoding is `decK vsPiOfK` at a frame map by name. -/
theorem decTopK_form (prog : LeanIsaProgram) (κ : ℕ) (mem : Vector E (2 ^ κ)) :
    ∃ (σ : Val) (rd : Reader) (Vn : NFrames),
      decTopK prog κ mem = B1.Main.decK B1.VerifySub.vsPiOfK σ rd (byName Vn) := by
  unfold decTopK decTopTablesK decTopStatesK
  rw [mainValDK_eq, decTopFramesK_eq]
  exact ⟨_, _, _, rfl⟩

/-- **A decoding the decoder outputs is its top's**, on every execution. -/
theorem output_any (t : Execution guestProgram) {dec : SeedStatementAndWitness}
    (h : outputWithin saltedDecoder saltedDecoder.size (saltedDecoderPrice t)
      (encodeGuestWitnessDecoderInput guestProgram t) = some (encodeValue dec)) :
    dec = decTopK guestProgram t.logMemorySize (memoryVector t.memory) := by
  rw [outputWithin_saltedDecoder_any] at h
  exact (encodeValue_decoded_injective (Option.some.inj h)).symm

/-- **A decoding the decoder outputs on a valid execution is the decoding by replay.** -/
theorem output_valid {input : PublicInput₂} {t : Execution guestProgram}
    (hv : ValidExecution₂ guestProgram input t) {dec : SeedStatementAndWitness}
    (h : outputWithin saltedDecoder saltedDecoder.size (saltedDecoderPrice t)
      (encodeGuestWitnessDecoderInput guestProgram t) = some (encodeValue dec)) :
    dec = decodeWithR (B1.Main.decK B1.VerifySub.vsPiOfK) t.memory := by
  rw [decoderComputesR_saltedDecoder input t hv] at h
  exact (encodeValue_decoded_injective (Option.some.inj h)).symm

/-! ## The decoding's fields -/

section Fields

variable (σ : Val) (rd : Reader) (V : End.FrameMap)

theorem decK_children :
    (B1.Main.decK B1.VerifySub.vsPiOfK σ rd V).witness.children =
      (List.range (Main.nKids (B1.Main.mainVal σ))).map
        (Main.decKid rd (B1.Main.mainVal σ) (fun args => B1.VerifySub.vsPiOfK rd (V "verify_sub" args []) V)) :=
  rfl

theorem decK_xmss_length :
    (B1.Main.decK B1.VerifySub.vsPiOfK σ rd V).witness.xmssSignatures.length =
      Main.nRawX (B1.Main.mainVal σ) := by
  show ((List.range _).map _).length = _
  rw [List.length_map, List.length_range]

theorem decK_sphincs_length :
    (B1.Main.decK B1.VerifySub.vsPiOfK σ rd V).witness.sphincsSignatures.length =
      Main.nRawS (B1.Main.mainVal σ) := by
  show ((List.range _).map _).length = _
  rw [List.length_map, List.length_range]

theorem decK_statement :
    (B1.Main.decK B1.VerifySub.vsPiOfK σ rd V).statement = Main.decStmt (B1.Main.mainVal σ) rd :=
  rfl

theorem decK_stmt_claims :
    (B1.Main.decK B1.VerifySub.vsPiOfK σ rd V).statement.claims.xmss.length +
      (B1.Main.decK B1.VerifySub.vsPiOfK σ rd V).statement.claims.sphincs.length =
      Main.gLog (B1.Main.mainVal σ (.n 0)) + Main.gLog (B1.Main.mainVal σ (.n 3)) := by
  rw [decK_statement]
  simp only [Main.decStmt, List.length_map, List.length_range]

theorem decK_daMatrix (c : DaClaim) (m : LeanVM.Da.MatrixWitness)
    (h : (B1.Main.decK B1.VerifySub.vsPiOfK σ rd V).witness.daMatrix = some (c, m)) :
    m.rows.length ≤ 1024 ∧ ∀ r ∈ m.rows, r.length ≤ 32768 := by
  change (B1.Main.decWitK B1.VerifySub.vsPiOfK σ rd V).daMatrix = _ at h
  rw [decWitK_eq] at h
  simp only [Main.decWit] at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]
    exact dvWitK_ok _ _
  · cases h

theorem decK_hints :
    (B1.Main.decK B1.VerifySub.vsPiOfK σ rd V).witness.batchingHints.sumcheckMessages.length ≤ 23 := by
  show (B1.Main.aggHintsS rd _).sumcheckMessages.length ≤ 23
  simp only [B1.Main.aggHintsS, B1.Main.aggRoundsS, List.length_map, List.length_range, le_refl]

/-- A decoded child's claims are at most the two regions' slots. -/
theorem kidStmt_claims_le (c : ℕ) :
    (Main.kidStmt rd σ c).claims.xmss.length + (Main.kidStmt rd σ c).claims.sphincs.length ≤
      Main.lxSlots σ + Main.lsSlots σ := by
  have h1 := B1.Main.kidSlots_length_le rd σ 0 (Main.lxSlots σ) (Main.countOf rd σ c)
    (Main.countOf rd σ (c + 1))
  have h2 := B1.Main.kidSlots_length_le rd σ (Main.lxSlots σ) (Main.lsSlots σ)
    (Main.countOf rd σ c + Main.segCount rd σ 0 (Main.lxSlots σ) (Main.countOf rd σ c)
      (Main.countOf rd σ (c + 1)))
    (Main.countOf rd σ (c + 1))
  simp only [Main.kidStmt, List.length_map]
  omega

end Fields

/-! ## The children's claims -/

/-- **On a valid execution of the salted guest, every child of a decoding the decoder outputs has
at most `2^20` signature claims.** -/
theorem childClaims_valid {input : PublicInput₂} {t : Execution guestProgram}
    (hv : ValidExecution₂ guestProgram input t) (dec : SeedStatementAndWitness)
    (h : outputWithin saltedDecoder saltedDecoder.size (saltedDecoderPrice t)
      (encodeGuestWitnessDecoderInput guestProgram t) = some (encodeValue dec)) :
    ∀ child ∈ dec.witness.children,
      child.statement.claims.xmss.length + child.statement.claims.sphincs.length ≤ 2 ^ 20 := by
  intro child hc
  rw [output_valid hv h] at hc
  have hC := countsK_valid hv
  unfold decodeWithR at hc
  rw [decK_children] at hc
  obtain ⟨c, -, rfl⟩ := List.mem_map.mp hc
  have h1 := kidStmt_claims_le (B1.Main.mainVal (valG t.memory 1 (certOf 1))) t.memory.read c
  have h2 := hC.slotsCap
  exact h1.trans (by omega)

/-- **On a valid execution of the salted guest, the statement of a decoding the decoder outputs has
at most `2^20` signature claims.** -/
theorem stmtClaims_valid {input : PublicInput₂} {t : Execution guestProgram}
    (hv : ValidExecution₂ guestProgram input t) (dec : SeedStatementAndWitness)
    (h : outputWithin saltedDecoder saltedDecoder.size (saltedDecoderPrice t)
      (encodeGuestWitnessDecoderInput guestProgram t) = some (encodeValue dec)) :
    dec.statement.claims.xmss.length + dec.statement.claims.sphincs.length ≤ 2 ^ 20 := by
  rw [output_valid hv h]
  unfold decodeWithR
  rw [decK_stmt_claims]
  have := (countsK_valid hv).claimsCap
  omega

/-! ## The batching hints -/

/-- **The batching hints of every decoding the decoder outputs have at most `23` sumcheck
messages**, on every execution (the decoder reads `23` rounds, with or without children). -/
theorem hints_le (t : Execution guestProgram) (dec : SeedStatementAndWitness)
    (h : outputWithin saltedDecoder saltedDecoder.size (saltedDecoderPrice t)
      (encodeGuestWitnessDecoderInput guestProgram t) = some (encodeValue dec)) :
    dec.witness.batchingHints.sumcheckMessages.length ≤ 23 := by
  rw [output_any t h]
  obtain ⟨σ, rd, Vn, e⟩ := decTopK_form guestProgram t.logMemorySize (memoryVector t.memory)
  rw [e]
  exact decK_hints σ rd _

/-! ## The DA matrix -/

/-- **The DA matrix of every decoding the decoder outputs has at most `LeanDa.maxRows` rows**, on
every execution. -/
theorem daRows_le (t : Execution guestProgram) (dec : SeedStatementAndWitness)
    (h : outputWithin saltedDecoder saltedDecoder.size (saltedDecoderPrice t)
      (encodeGuestWitnessDecoderInput guestProgram t) = some (encodeValue dec)) :
    ∀ claim matrix, dec.witness.daMatrix = some (claim, matrix) →
      matrix.rows.length ≤ LeanDa.maxRows := by
  intro claim matrix hm
  rw [output_any t h] at hm
  obtain ⟨σ, rd, Vn, e⟩ := decTopK_form guestProgram t.logMemorySize (memoryVector t.memory)
  rw [e] at hm
  exact (decK_daMatrix σ rd _ claim matrix hm).1

/-! ## The encoded size -/

/-- **A decoding's size from its fields' bounds**: at most `n` claims in its statement, `k`
children of at most `c` claims and of proofs of size at most `P`, at most `r` raw signatures of
each scheme, the DA matrix within `1024` rows of `32768` symbols, `23` batching rounds. -/
theorem size_decoding_le (d : SeedStatementAndWitness) {n k c P r : ℕ}
    (hs : d.statement.claims.xmss.length + d.statement.claims.sphincs.length ≤ n)
    (hsd : d.statement.deferredClaim.bytecodePoint.length ≤ 23)
    (hk : d.witness.children.length ≤ k)
    (hc : ∀ child ∈ d.witness.children,
      child.statement.claims.xmss.length + child.statement.claims.sphincs.length ≤ c ∧
        child.statement.deferredClaim.bytecodePoint.length ≤ 23 ∧
        child.freshClaim.bytecodePoint.length ≤ 23 ∧ (encodeValue child.proof).size ≤ P)
    (hx : d.witness.xmssSignatures.length ≤ r) (hy : d.witness.sphincsSignatures.length ≤ r)
    (hd : ∀ cl m, d.witness.daMatrix = some (cl, m) →
      m.rows.length ≤ 1024 ∧ ∀ row ∈ m.rows, row.length ≤ 32768)
    (hh : d.witness.batchingHints.sumcheckMessages.length ≤ 23) :
    (encodeValue d).size ≤ 5 + (14 * n + 130) + ((k * ((14 * c + 130) + 121 + P + 1 + 1) + 1) +
      (r * 474 + 1) + (r * 1539 + 1) + 67110926 + 236 + 1) + 1 := by
  rw [size_decoding, size_nodeWitness]
  have hseed := size_digest d.seed
  have hstmt := size_stmt d.statement hs hsd
  have h1 := size_list_le d.witness.children hk (b := (14 * c + 130) + 121 + P + 1)
    (fun child hch ↦ by
      obtain ⟨a1, a2, a3, a4⟩ := hc child hch
      show (MachineValue.constructor 0 [encodeValue child.statement, encodeValue child.freshClaim,
        encodeValue child.proof]).size ≤ _
      rw [size_ctor3]
      have := size_stmt child.statement a1 a2
      have := size_bcClaim child.freshClaim a3
      omega)
  have h2 := size_list_le d.witness.xmssSignatures hx (b := 473)
    (fun x _ ↦ by rw [size_pair]; have := size_xmssClaim x.1; have := size_xmssSig x.2; omega)
  have h3 := size_list_le d.witness.sphincsSignatures hy (b := 1538)
    (fun x _ ↦ by rw [size_pair]; have := size_sphincsClaim x.1; have := size_sphincsSig x.2; omega)
  have h4 := size_daOption d.witness.daMatrix hd
  have h5 := size_hints d.witness.batchingHints hh
  omega

/-- **The salted decoding's size bound on a valid execution**: about `2^41.33`. -/
def decodingSizeBoundValid : ℕ := 346031412918

/-- **On a valid execution of the salted guest, every decoding the decoder's output decodes to
has an encoding of size at most `decodingSizeBoundValid`.** -/
theorem decodingSize_valid {input : PublicInput₂} {t : Execution guestProgram}
    (hv : ValidExecution₂ guestProgram input t) (output : MachineValue)
    (dec : SeedStatementAndWitness)
    (h : outputWithin saltedDecoder saltedDecoder.size (saltedDecoderPrice t)
      (encodeGuestWitnessDecoderInput guestProgram t) = some output)
    (hd : decodeDecoded output = some dec) :
    (encodeValue dec).size ≤ decodingSizeBoundValid := by
  have ho : output = encodeValue dec := by
    rw [outputWithin_saltedDecoder_any] at h
    obtain rfl := Option.some.inj h
    rw [decodeDecoded_enc] at hd
    obtain rfl := Option.some.inj hd
    rfl
  subst ho
  have hkids := childClaims_valid hv dec h
  have eA := output_any t h
  have eV := output_valid hv h
  obtain ⟨σ₁, rd₁, Vn, e₁⟩ := decTopK_form guestProgram t.logMemorySize (memoryVector t.memory)
  rw [e₁] at eA
  have hC := countsK_valid hv
  unfold decodeWithR at eV
  refine (size_decoding_le dec (n := 2 ^ 20) (k := 16) (c := 2 ^ 20) (P := 21475247062)
    (r := 2 ^ 20) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_).trans (by unfold decodingSizeBoundValid; norm_num)
  · rw [eV, decK_stmt_claims]; have := hC.claimsCap; omega
  · rw [eV, decK_statement]; exact deferOfCells_len _
  · rw [eV, decK_children, List.length_map, List.length_range]; exact hC.kids
  · intro child hch
    refine ⟨hkids child hch, ?_⟩
    rw [eA, decK_children] at hch
    obtain ⟨c, -, rfl⟩ := List.mem_map.mp hch
    refine ⟨decKid_deferred_len _ _ _ _, decKid_fresh_len _ _ _ _, ?_⟩
    rw [decKid_proof]
    show (encodeValue (B1.VerifySub.vsPiOfK rd₁ (byName Vn "verify_sub" _ []) (byName Vn))).size ≤ _
    rw [← vsPiOfNK_eq]
    exact size_vsPiOfNK _ _ _
  · rw [eV, decK_xmss_length]; have := hC.rawCap; omega
  · rw [eV, decK_sphincs_length]; have := hC.rawCap; omega
  · rw [eV]; exact decK_daMatrix _ _ _
  · rw [eV]; exact decK_hints _ _ _

end
end LeanVM.SaltedGuest.Bounds
