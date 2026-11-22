/-
  LeanVM.SaltedGuest.Bounds.PriceK

  The salted decoder program's price on a valid execution, a formula in its steps.
-/

module

public import LeanVM.SaltedGuest.Bounds.TopK
public import LeanVM.SaltedGuest.Bounds.Valid
public import LeanVM.Cost.Bounds.Decoder.ReplayLength
public import LeanVM.Cost.Bounds.Guest.Budget

/-!
# The salted decoder's price

On a valid execution of the salted guest (`ValidExecution₂`, a memory of at most `2^30` words):

* `replayStatesOfK_length`: the replay lists at most `stepCount + 1` states;
* `countsWithin_valid`: the counts the witness reads, at most `16` children and `2^20` of each
  other count (`CountsK`, the claim cap of the salted `main`);
* **`saltedDecoderPrice_le_at`**: for every exponent `e` with `2·(stepCount + 1) < 2^e`, the price
  is at most `saltedPriceAt e stepCount`, which is `saltedStepPriceK e` per step and a constant;
* **`saltedDecoderPrice_le`**: at the entry table's exponent of the steps
  (`guestDecoderEntryTableKeyExponent`), the formula in `stepCount` alone;
* **`saltedDecoderPrice_le_of_steps30`**: at most `2^30` steps, the price is at most
  `saltedPrice30 ≤ 2^52`; **`saltedDecoderPrice_le_of_steps35`**: at most `2^35` steps, at most
  `saltedPrice35 ≤ 2^57`.
-/

namespace LeanVM.SaltedGuest.Bounds

open LeanVM.Cost.Bounds.Guest LeanVM.SaltedGuest.Decoder LeanVM.Cost LeanVM.Cost.Bounds
open LeanVM.Cost.Library LeanVM.Parameters LeanVM.Guest.Core LeanVM.Guest.Fast
open LeanVM.Extraction.Fast LeanVM.Semantics LeanVM.SaltedGuest.Check
open Recursion.Salted Recursion.SecondDigest

public section

/-- The price of one replayed state: its step at a memory of at most `2^30` words and the guest's
`2^19` instructions, and its filing in the entry table of at most `2^e` pairs. -/
@[expose] def saltedStepPriceK (e : ℕ) : ℕ := runnerStepPrice 30 19 + 46 + statePriceK e 1271

/-- **The salted decoder's price on a valid execution of `steps` steps**, the entry table's
exponent `e`: per state `saltedStepPriceK e`, the frames stage, the tables built once (the
logarithm's, the salted preconditions, entries and frame cells, the powers, the readers', `open_stacked`'s,
the pc table) and the address tables of a memory of `2^30` words. -/
@[expose] def saltedPriceAt (e steps : ℕ) : ℕ :=
  saltedStepPriceK e * (steps + 1) + framesPriceK e 1271 + 2541 + 90351983 + tablesPriceK +
    17565 + 36800 + 11134 + 14460000 +
    ((74 * 30 + 121) * 2 ^ 30 + (74 * 19 + 121) * 2 ^ 19 + 42) + 30

/-- **A valid execution's replay lists at most `stepCount + 1` states.** -/
theorem replayStatesOfK_length {input : PublicInput₂} {t : Execution guestProgram}
    (hv : ValidExecution₂ guestProgram input t) :
    (Decoder.replayStatesOf (powTable t.logMemorySize) (powTable guestProgram.logSize)
      guestProgram (Decoder.memoryVector t.memory)).length ≤ t.stepCount + 1 := by
  obtain ⟨κ, L, T⟩ := t
  have h30 : κ ≤ 30 := hv.1.1.2.1
  have hκ : κ < 64 := by omega
  have hT : LeanVM.Semantics.run guestProgram L T ⟨addressOfIndex 0, 1⟩ =
      some (Registers.final guestProgram) :=
    LeanVM.Guest.safe_of_validExecution hv.1
  show (Decoder.replayStatesOf (powTable κ) (powTable guestProgram.logSize) guestProgram
    (Decoder.memoryVector L)).length ≤ T + 1
  rw [Decoder.replayStatesOf_eq, Decoder.memoryVector_get, LeanVM.Guest.Located.statesTable_eq hκ]
  exact statesIn_length_le (LeanVM.Protocol.Halting.stepIn_powIndex hκ L) T LeanVM.Guest.Located.replayFuel _ hT

/-- The decoder's valuation of `main`'s frame at the deployed numbers is `main`'s. -/
theorem mainValDK_valid {input : PublicInput₂} {t : Execution guestProgram}
    (hv : ValidExecution₂ guestProgram input t) :
    mainValDK locsTableK (Decoder.memReader (powTable t.logMemorySize)
      (Decoder.memoryVector t.memory)) = LeanVM.SaltedGuest.B1.Main.mainVal (valG t.memory 1 (certOf 1)) := by
  have h30 : t.logMemorySize ≤ 30 := hv.1.1.2.1
  have hκ : t.logMemorySize < 64 := by omega
  rw [Decoder.memReader_memoryVector, LeanVM.Guest.Located.readTable_powTable hκ, mainValDK_eq]
  have hσ : mainValK locsTableK t.memory.read = valG t.memory 1 (certOf 1) := by
    rw [mainValK_eq]
    rfl
  rw [hσ]

/-- **On a valid execution, the counts the decoder's witness reads**: at most `16` children, and
at most `2^20` declared claims and raw signatures of a scheme and slots in a region. -/
theorem countsWithin_valid {input : PublicInput₂} {t : Execution guestProgram}
    (hv : ValidExecution₂ guestProgram input t) :
    CountsWithin discreteLogTables (mainValDK locsTableK (Decoder.memReader
      (powTable t.logMemorySize) (Decoder.memoryVector t.memory))) 16 (2 ^ 20) (2 ^ 20) := by
  rw [mainValDK_valid hv]
  have hC := countsK_valid hv
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold Decoder.nKidsD; rw [Decoder.gLogD_tables]; exact hC.kids
  · unfold Decoder.lxSlotsD; rw [Decoder.gLogD_tables]; have := hC.slotsCap
    unfold LeanVM.Guest.B1.Main.lxSlots LeanVM.Guest.B1.Main.lsSlots at this; omega
  · unfold Decoder.lsSlotsD; rw [Decoder.gLogD_tables]; have := hC.slotsCap
    unfold LeanVM.Guest.B1.Main.lxSlots LeanVM.Guest.B1.Main.lsSlots at this; omega
  · rw [Decoder.gLogD_tables]; have := hC.claimsCap; omega
  · rw [Decoder.gLogD_tables]; have := hC.claimsCap; omega
  · unfold Decoder.nRawXD; rw [Decoder.gLogD_tables]; have := hC.rawCap
    unfold LeanVM.Guest.B1.Main.nRawX LeanVM.Guest.B1.Main.nRawS at this; omega
  · unfold Decoder.nRawSD; rw [Decoder.gLogD_tables]; have := hC.rawCap
    unfold LeanVM.Guest.B1.Main.nRawX LeanVM.Guest.B1.Main.nRawS at this; omega

/-- **The salted decoder program's price on a valid execution**, the entry table's exponent `e`
any with `2·(stepCount + 1) < 2^e`: at most `saltedPriceAt e stepCount`. -/
theorem saltedDecoderPrice_le_at {input : PublicInput₂} {t : Execution guestProgram}
    (hv : ValidExecution₂ guestProgram input t) (e : ℕ) (he : 2 * (t.stepCount + 1) < 2 ^ e) :
    saltedDecoderPrice t ≤ saltedPriceAt e t.stepCount := by
  have hP := saltedDecoder_includes
  have hκ : t.logMemorySize ≤ 30 := hv.1.1.2.1
  have hlen := replayStatesOfK_length hv
  unfold saltedDecoderPrice
  rw [decTopKC.costEq saltedDecoder hP]
  have h1 := discreteLogTables_cost saltedDecoder (by includes)
  have h2 := genPows_cost saltedDecoder (by includes)
  have h3 := readerTabs_cost saltedDecoder (by includes)
  have h4 := whirTabsK_cost saltedDecoder (by includes)
  have h5 := pcTableTK_cost saltedDecoder (by includes)
  have h6 := tablesK_cost saltedDecoder (by includes) (by includes) (by includes) (by includes)
    (by includes)
  have h7 := decoderTables_cost saltedDecoder (by includes) guestProgram t.logMemorySize
    (by omega)
  have h8 := decTopTablesK_costK saltedDecoder (by includes) guestProgram hκ
    (Decoder.memoryVector t.memory) e (by omega) (countsWithin_valid hv)
  rw [LeanVM.SaltedGuest.guest_logSize] at h7 h8 hlen
  have hr : runnerStepPrice t.logMemorySize 19 ≤ runnerStepPrice 30 19 := by
    unfold runnerStepPrice; omega
  have ha : (74 * t.logMemorySize + 121) * 2 ^ t.logMemorySize ≤ (74 * 30 + 121) * 2 ^ 30 :=
    Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by norm_num) hκ)
  have hm : (runnerStepPrice t.logMemorySize 19 + 46 + statePriceK e 1271) *
      (Decoder.replayStatesOf (powTable t.logMemorySize) (powTable 19) guestProgram
        (Decoder.memoryVector t.memory)).length ≤ saltedStepPriceK e * (t.stepCount + 1) :=
    Nat.mul_le_mul (by unfold saltedStepPriceK; omega) hlen
  unfold saltedPriceAt
  omega

/-- **The salted decoder program's price on a valid execution, a formula in its steps**: at the
entry table's exponent `guestDecoderEntryTableKeyExponent stepCount = log₂(stepCount + 1) + 2`. -/
theorem saltedDecoderPrice_le {input : PublicInput₂} {t : Execution guestProgram}
    (hv : ValidExecution₂ guestProgram input t) :
    saltedDecoderPrice t ≤
      saltedPriceAt (LeanVM.Node.guestDecoderEntryTableKeyExponent t.stepCount) t.stepCount :=
  saltedDecoderPrice_le_at hv _ (tableExponent_spec t.stepCount)

/-- The price at `2^30` steps. -/
@[expose] def saltedPrice30 : ℕ := saltedPriceAt 32 (2 ^ 30)

/-- The price at `2^35` steps. -/
@[expose] def saltedPrice35 : ℕ := saltedPriceAt 37 (2 ^ 35)

theorem saltedPrice30_le : saltedPrice30 ≤ 2 ^ 52 := by decide +kernel

theorem saltedPrice35_le : saltedPrice35 ≤ 2 ^ 57 := by decide +kernel

/-- **On a valid execution of at most `2^30` steps, the salted decoder's price is at most
`saltedPrice30 ≤ 2^52`.** -/
theorem saltedDecoderPrice_le_of_steps30 {input : PublicInput₂} {t : Execution guestProgram}
    (hv : ValidExecution₂ guestProgram input t) (hs : t.stepCount ≤ 2 ^ 30) :
    saltedDecoderPrice t ≤ saltedPrice30 := by
  have h := saltedDecoderPrice_le_at hv 32 (by omega)
  have hm := Nat.mul_le_mul_left (saltedStepPriceK 32) (show t.stepCount + 1 ≤ 2 ^ 30 + 1 by omega)
  unfold saltedPrice30 saltedPriceAt at *
  omega

/-- **On a valid execution of at most `2^35` steps, the salted decoder's price is at most
`saltedPrice35 ≤ 2^57`.** -/
theorem saltedDecoderPrice_le_of_steps35 {input : PublicInput₂} {t : Execution guestProgram}
    (hv : ValidExecution₂ guestProgram input t) (hs : t.stepCount ≤ 2 ^ 35) :
    saltedDecoderPrice t ≤ saltedPrice35 := by
  have h := saltedDecoderPrice_le_at hv 37 (by omega)
  have hm := Nat.mul_le_mul_left (saltedStepPriceK 37) (show t.stepCount + 1 ≤ 2 ^ 35 + 1 by omega)
  unfold saltedPrice35 saltedPriceAt at *
  omega

end

end LeanVM.SaltedGuest.Bounds
