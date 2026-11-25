/-
  LeanVM.SaltedGuest.Decoder.Bits

  The salted decoder program's bit length, below `2^64`, by evaluation of a bound.
-/

module

public import LeanVM.Salted.ProgramCode
public import LeanVM.SaltedGuest.Decoder.Program
public import Mathlib.Data.Nat.Size

/-!
# The salted decoder program's bit length

A bound on a code's length that the kernel evaluates: a number's code (`natCode n`,
`2·|bits n| + 1` bits) is at most `natLenB n` (`2·64 + 1` below `2^64`, `2·2048 + 1` below
`2^2048`, `2n + 1` beyond), a function index's code at most `1 + natLenB (f + N)` in a program of at
most `N` functions (`indexCode_length_le`); a term's code at most `termB N t`
(`termCode_length_le`), a program's at most its length's and its bodies' (`bits_le`), and for a
program built from indexed bodies (`MachineProgram.ofList`) the bodies' and the literal `0` once per
index (`sum_ofList_le`).

**`saltedDecoder_bits_le : saltedDecoder.bits ≤ 2 ^ 64`**: the bound evaluated over the compiled top's
bodies (`decTopKC.costDeps`) and the entry, by `decide +kernel` (`decoderBodiesB_le`, about 20 s and
7 GB: the packed frame cells are `8221` literals of at most `1024` bits); the value is
`saltedDecoderBitsBound = 57790849` (about `2^25.8`); the program has `1182` functions
(`saltedDecoderLength_eq`).
-/

namespace LeanVM.SaltedGuest.Decoder

open LeanVM.Cost Recursion.Salted

@[expose] public section

set_option exponentiation.threshold 2100

/-- A bound on a number's binary digits. -/
def bitsUB (n : ℕ) : ℕ := if n < 2 ^ 64 then 64 else if n < 2 ^ 2048 then 2048 else n

/-- A bound on a number's code. -/
def natLenB (n : ℕ) : ℕ := 2 * bitsUB n + 1

theorem bitsUB_mono {m n : ℕ} (h : m ≤ n) : bitsUB m ≤ bitsUB n := by
  unfold bitsUB; split_ifs <;> omega

theorem natLenB_mono {m n : ℕ} (h : m ≤ n) : natLenB m ≤ natLenB n := by
  have := bitsUB_mono h; unfold natLenB; omega

theorem size_le_bitsUB (n : ℕ) : n.size ≤ bitsUB n := by
  unfold bitsUB
  split_ifs with h1 h2
  · exact Nat.size_le.2 h1
  · exact Nat.size_le.2 h2
  · exact Nat.size_le.2 n.lt_two_pow_self

theorem natCode_length_le (n : ℕ) : (natCode n).length ≤ natLenB n := by
  have := size_le_bitsUB n
  simp only [natCode, List.length_append, List.length_replicate, List.length_cons,
    Nat.size_eq_bits_len]
  unfold natLenB; omega

theorem indexCode_length_le {N self : ℕ} (hs : self ≤ N) (f : ℕ) :
    (indexCode self f).length ≤ 1 + natLenB (f + N) := by
  unfold indexCode
  split_ifs
  · have := natCode_length_le (f - self)
    have := natLenB_mono (show f - self ≤ f + N by omega)
    simp only [List.length_cons]; omega
  · have := natCode_length_le (self - f)
    have := natLenB_mono (show self - f ≤ f + N by omega)
    simp only [List.length_cons]; omega

theorem operationIndex_le (o : PrimitiveOperation) : operationIndex o ≤ 21 := by
  cases o <;> simp [operationIndex]

mutual

/-- A bound on a value's code in a program of at most `N` functions. -/
def valueB (N : ℕ) : MachineValue → ℕ
  | .nat n => natLenB 0 + natLenB n
  | .constructor tag fs => natLenB 1 + natLenB tag + natLenB fs.length + valuesB N fs
  | .array ⟨es⟩ => natLenB 2 + natLenB es.length + valuesB N es
  | .closure f us => natLenB 3 + (1 + natLenB (f + N)) + natLenB us.length + valuesB N us

/-- A bound on values' codes. -/
def valuesB (N : ℕ) : List MachineValue → ℕ
  | [] => 0
  | v :: vs => valueB N v + valuesB N vs

end

mutual

/-- A bound on a term's code in a program of at most `N` functions. -/
def termB (N : ℕ) : Term → ℕ
  | .position i => natLenB 0 + natLenB i
  | .literal v => natLenB 1 + valueB N v
  | .primitive _ ts => natLenB 2 + natLenB 21 + natLenB ts.length + termsB N ts
  | .constructor tag ts => natLenB 3 + natLenB tag + natLenB ts.length + termsB N ts
  | .field i t => natLenB 4 + natLenB i + termB N t
  | .case t alts => natLenB 5 + termB N t + natLenB alts.length + termsB N alts
  | .letIn t b => natLenB 6 + termB N t + termB N b
  | .call f ts => natLenB 7 + (1 + natLenB (f + N)) + natLenB ts.length + termsB N ts
  | .closure f ts => natLenB 8 + (1 + natLenB (f + N)) + natLenB ts.length + termsB N ts
  | .applyClosure t ts => natLenB 9 + termB N t + natLenB ts.length + termsB N ts

/-- A bound on terms' codes. -/
def termsB (N : ℕ) : List Term → ℕ
  | [] => 0
  | t :: ts => termB N t + termsB N ts

end

mutual

theorem valueCode_length_le {N self : ℕ} (hs : self ≤ N) :
    ∀ v : MachineValue, (valueCode self v).length ≤ valueB N v
  | .nat n => by
    have := natCode_length_le 0; have := natCode_length_le n
    simp only [valueCode, valueB, List.length_append]; omega
  | .constructor tag fs => by
    have := natCode_length_le 1; have := natCode_length_le tag
    have := natCode_length_le fs.length; have := valuesCode_length_le hs fs
    simp only [valueCode, valueB, List.length_append]; omega
  | .array ⟨es⟩ => by
    have := natCode_length_le 2; have := natCode_length_le es.length
    have := valuesCode_length_le hs es
    simp only [valueCode, valueB, List.length_append]; omega
  | .closure f us => by
    have := natCode_length_le 3; have := indexCode_length_le hs f
    have := natCode_length_le us.length; have := valuesCode_length_le hs us
    simp only [valueCode, valueB, List.length_append]; omega

theorem valuesCode_length_le {N self : ℕ} (hs : self ≤ N) :
    ∀ vs : List MachineValue, (valuesCode self vs).length ≤ valuesB N vs
  | [] => by simp [valuesCode, valuesB]
  | v :: vs => by
    have := valueCode_length_le hs v; have := valuesCode_length_le hs vs
    simp only [valuesCode, valuesB, List.length_append]; omega

end

mutual

theorem termCode_length_le {N self : ℕ} (hs : self ≤ N) :
    ∀ t : Term, (termCode self t).length ≤ termB N t
  | .position i => by
    have := natCode_length_le 0; have := natCode_length_le i
    simp only [termCode, termB, List.length_append]; omega
  | .literal v => by
    have := natCode_length_le 1; have := valueCode_length_le hs v
    simp only [termCode, termB, List.length_append]; omega
  | .primitive o ts => by
    have := natCode_length_le 2; have := natCode_length_le (operationIndex o)
    have := natLenB_mono (operationIndex_le o)
    have := natCode_length_le ts.length; have := termsCode_length_le hs ts
    simp only [termCode, termB, List.length_append]; omega
  | .constructor tag ts => by
    have := natCode_length_le 3; have := natCode_length_le tag
    have := natCode_length_le ts.length; have := termsCode_length_le hs ts
    simp only [termCode, termB, List.length_append]; omega
  | .field i t => by
    have := natCode_length_le 4; have := natCode_length_le i
    have := termCode_length_le hs t
    simp only [termCode, termB, List.length_append]; omega
  | .case t alts => by
    have := natCode_length_le 5; have := termCode_length_le hs t
    have := natCode_length_le alts.length; have := termsCode_length_le hs alts
    simp only [termCode, termB, List.length_append]; omega
  | .letIn t b => by
    have := natCode_length_le 6; have := termCode_length_le hs t
    have := termCode_length_le hs b
    simp only [termCode, termB, List.length_append]; omega
  | .call f ts => by
    have := natCode_length_le 7; have := indexCode_length_le hs f
    have := natCode_length_le ts.length; have := termsCode_length_le hs ts
    simp only [termCode, termB, List.length_append]; omega
  | .closure f ts => by
    have := natCode_length_le 8; have := indexCode_length_le hs f
    have := natCode_length_le ts.length; have := termsCode_length_le hs ts
    simp only [termCode, termB, List.length_append]; omega
  | .applyClosure t ts => by
    have := natCode_length_le 9; have := termCode_length_le hs t
    have := natCode_length_le ts.length; have := termsCode_length_le hs ts
    simp only [termCode, termB, List.length_append]; omega

theorem termsCode_length_le {N self : ℕ} (hs : self ≤ N) :
    ∀ ts : List Term, (termsCode self ts).length ≤ termsB N ts
  | [] => by simp [termsCode, termsB]
  | t :: ts => by
    have := termCode_length_le hs t; have := termsCode_length_le hs ts
    simp only [termsCode, termsB, List.length_append]; omega

end

theorem bodiesCode_length_le (N : ℕ) :
    ∀ (ts : List Term) (start : ℕ), start + ts.length ≤ N →
      (bodiesCode start ts).length ≤ (ts.map (termB N)).sum
  | [], _, _ => by simp [bodiesCode]
  | t :: ts, start, h => by
    have := termCode_length_le (N := N) (self := start) (by simp at h; omega) t
    have := bodiesCode_length_le N ts (start + 1) (by simp at h; omega)
    simp only [bodiesCode, List.length_append, List.map_cons, List.sum_cons]; omega

/-- **A program's bit length**: at most its length's code and its bodies' bounds. -/
theorem bits_le (P : MachineProgram) :
    P.bits ≤ natLenB P.toList.length + (P.toList.map (termB P.toList.length)).sum := by
  unfold MachineProgram.bits programCode
  have := natCode_length_le P.toList.length
  have := bodiesCode_length_le P.toList.length P.toList 0 (by omega)
  simp only [List.length_append]; omega

/-- A weight's sum over a program built from indexed bodies: the bodies' weights and the literal
`0`'s once per index. -/
theorem sum_ofList_le (w : Term → ℕ) (l : List (ℕ × Term)) :
    ((MachineProgram.ofList l).toList.map w).sum ≤
      (l.map fun p ↦ w p.2).sum + ((l.map (·.1)).foldr max 0 + 1) * w (.literal (.nat 0)) := by
  have key : ∀ (l : List (ℕ × Term)) (A : MachineProgram),
      ((l.foldl (fun P p ↦ P.setIfInBounds p.1 p.2) A).toList.map w).sum ≤
        (A.toList.map w).sum + (l.map fun p ↦ w p.2).sum := by
    intro l
    induction l with
    | nil => intro A; simp
    | cons p l ih =>
      intro A
      have h1 := ih (A.setIfInBounds p.1 p.2)
      have h2 : ((A.setIfInBounds p.1 p.2).toList.map w).sum ≤ (A.toList.map w).sum + w p.2 := by
        rw [Array.setIfInBounds_def]
        split
        · rw [Array.toList_set]; exact LeanVM.Cost.sum_map_set_le _ _ _ _
        · omega
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      omega
  have := key l (Array.replicate ((l.map (·.1)).foldr max 0 + 1) (.literal (.nat 0)))
  unfold MachineProgram.ofList
  dsimp only
  simp only [Array.toList_replicate, List.map_replicate, List.sum_replicate, smul_eq_mul] at this
  omega

theorem size_ofList (l : List (ℕ × Term)) :
    (MachineProgram.ofList l).toList.length = (l.map (·.1)).foldr max 0 + 1 := by
  have key : ∀ (l : List (ℕ × Term)) (A : MachineProgram),
      Array.size (l.foldl (fun P p ↦ P.setIfInBounds p.1 p.2) A) = Array.size A := by
    intro l
    induction l with
    | nil => intro A; rfl
    | cons p l ih => intro A; rw [List.foldl_cons, ih, Array.size_setIfInBounds]
  unfold MachineProgram.ofList
  rw [Array.length_toList, key, Array.size_replicate]

/-- The salted decoder's bodies' bound, evaluated: the number of its functions. -/
def saltedDecoderLength : ℕ := (((0, decoderEntryBody decTopKC.costIdx) :: decTopKC.costDeps).map
  (·.1)).foldr max 0 + 1

/-- **The salted decoder's bit length's bound**: its length's code, its bodies' bounds and the
literal `0` at every index. -/
def saltedDecoderBitsBound : ℕ :=
  natLenB saltedDecoderLength +
    ((((0, decoderEntryBody decTopKC.costIdx) :: decTopKC.costDeps).map
      fun p ↦ termB saltedDecoderLength p.2).sum +
    saltedDecoderLength * termB saltedDecoderLength (.literal (.nat 0)))

set_option maxRecDepth 100000 in
/-- The bound, evaluated by the kernel. -/
theorem decoderBodiesB_le : saltedDecoderBitsBound ≤ 2 ^ 64 := by decide +kernel

/-- **The salted decoder program's bit length is at most `2^64`.** -/
theorem saltedDecoder_bits_le : saltedDecoder.bits ≤ 2 ^ 64 := by
  have h1 := bits_le saltedDecoder
  have hl : saltedDecoder.toList.length = saltedDecoderLength := size_ofList _
  have h2 := sum_ofList_le (termB saltedDecoderLength)
    (decoderProgramBodiesOf decTopKC.costIdx decTopKC.costDeps)
  rw [hl] at h1
  have e : saltedDecoder = MachineProgram.ofList
      (decoderProgramBodiesOf decTopKC.costIdx decTopKC.costDeps) := rfl
  rw [← e] at h2
  have := decoderBodiesB_le
  unfold saltedDecoderBitsBound at this
  unfold saltedDecoderLength at hl h1 h2 this
  unfold decoderProgramBodiesOf at h2
  omega

/-- The salted decoder program has `1182` functions. -/
theorem saltedDecoderLength_eq : saltedDecoderLength = 1182 := by decide +kernel

end

end LeanVM.SaltedGuest.Decoder
