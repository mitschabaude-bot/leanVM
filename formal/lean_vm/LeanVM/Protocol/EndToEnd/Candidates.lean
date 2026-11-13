/-
  LeanVM.Protocol.EndToEnd.Candidates

  The stacks a level-0 commitment binds: those whose encoding agrees with the committed word on
  enough columns. The object the front phases' doom and WHIR's starting relation quantify over,
  and from which the knowledge extractor picks.
-/

module

public import LeanVM.Protocol.Whir.NovelBasis
public import LeanVM.Protocol.Compile.Prog

/-!
# The candidates of a commitment

The deployed commitment (`verify_execution` step 2 and `verify_whir` level 0,
`crates/verifier/src/lib.rs:235-237` and `whir.rs:185-211` at leanVM `40f877dc`) is a Merkle
root of a word of `2^(μ − 6 + R)` columns, each a leaf of `64` words of `K`. The
leaf stores the lanes of its column in reverse order (`row.reverse`): lane `u` of column `v` is
word `63 − u` of leaf `v` (`laneOf`). Lane `u` of an honest word is the encoding (`enc`, the
novel-basis Reed-Solomon code) of the stack's block `u`: the `2^(μ−6)` consecutive cells at offset
`u · 2^(μ−6)`, so that the stack's coordinates are the message's `μ − 6` low bits and the lane's
six high bits (`blockOf`, Annex B "Optimizations", `f(u, x) = q(x, u)`).

`Agrees μ R W q S` says the encoding of the stack `q` agrees with the word `W` on every lane at
every column of `S`. A column is *listed* (`Listed`) when its leaf has the `2^6` words of the
level: the word a compiled run's extraction reads leaves the columns with no accepted opening
empty (`Compile.Rom.extract`), and a well-shaped word lists every column. `Candidates μ R A W` are
the stacks whose encoding agrees with `W` on at least `A` listed columns: with
`A = ⌈(√ρ₋ + η)·n⌉`, the stacks of the Johnson list at radius `1 − √ρ₋ − η`, on the listed
columns. A smaller listing has fewer candidates (`candidates_mono`), and on a well-shaped word
they are the stacks agreeing on any `A` columns (`candidates_of_wellShaped`). The front phases' doom (no candidate is in their state function) and WHIR's
starting relation (every candidate violates a pooled claim) quantify over them; the knowledge
extractor returns the candidate satisfying the relation when there is one.

Candidates are `K`-valued stacks by type: a codeword of the `E`-code close to a `K`-valued word is
`K`-valued (WHIR's soundness proves the list members are the encodings of candidates).
-/

namespace LeanVM.Protocol.EndToEnd

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Whir

@[expose] public section

/-- The number of lanes of the level-0 commitment: `2^6`. -/
abbrev laneBits : ℕ := 6

/-- Lane `u` of column `v` of a committed level-0 word, as an element of `E`: word `63 − u` of the
leaf (the leaf stores the lanes reversed; a missing word reads `0`). -/
def laneOf (W : Word) (u : Fin (2 ^ laneBits)) (v : ℕ) : E :=
  ofK ((W v).reverse.getD u 0)

/-- Block `u` of the stack: cell `x + 2^(μ−6)·u`, the message the lane `u` encodes, indexed by the
`μ − 6` low bits `x` (bit `0` first). -/
def blockOf {μ : ℕ} (q : Column μ) (u : Fin (2 ^ laneBits)) :
    (Fin (μ - laneBits) → Bool) → E :=
  fun x ↦ ofK (q.values.getD (bitsToNat x + 2 ^ (μ - laneBits) * u) 0)

/-- The encoding of the stack `q` agrees with the word `W` at every lane of every column of `S`. -/
def Agrees (μ R : ℕ) (W : Word) (q : Column μ) (S : Finset (Fin (2 ^ (μ - laneBits + R)))) :
    Prop :=
  ∀ v ∈ S, ∀ u, laneOf W u v = enc (μ - laneBits) R (blockOf q u) v

/-- Column `v` of a committed level-0 word is **listed**: its leaf has the `2^6` words. -/
def Listed (W : Word) (v : ℕ) : Prop := (W v).length = 2 ^ laneBits

/-- The **candidates** of a committed word: the stacks whose encoding agrees with it on at least
`A` listed columns. -/
def Candidates (μ R A : ℕ) (W : Word) : Set (Column μ) :=
  {q | ∃ S : Finset (Fin (2 ^ (μ - laneBits + R))), A ≤ S.card ∧ (∀ v ∈ S, Listed W v) ∧
    Agrees μ R W q S}

/-- The stacks whose encoding agrees with `W` on at least `A` columns, listed or not: the
candidates of a word that lists every column (`candidates_of_wellShaped`). -/
def AgreeingStacks (μ R A : ℕ) (W : Word) : Set (Column μ) :=
  {q | ∃ S : Finset (Fin (2 ^ (μ - laneBits + R))), A ≤ S.card ∧ Agrees μ R W q S}

/-- Candidates agree with the word. -/
theorem candidates_subset_agreeingStacks {μ R A : ℕ} (W : Word) :
    Candidates μ R A W ⊆ AgreeingStacks μ R A W :=
  fun _ ⟨S, hS, _, hag⟩ ↦ ⟨S, hS, hag⟩

/-- **A smaller listing has fewer candidates**: if every listed column of `W` is a column of `W'`
with the same leaf, every candidate of `W` is a candidate of `W'`. -/
theorem candidates_mono {μ R A : ℕ} {W W' : Word} (h : ∀ v, Listed W v → W' v = W v) :
    Candidates μ R A W ⊆ Candidates μ R A W' := by
  rintro q ⟨S, hS, hl, hag⟩
  refine ⟨S, hS, fun v hv ↦ ?_, fun v hv u ↦ ?_⟩
  · rw [Listed, h v (hl v hv)]; exact hl v hv
  · rw [laneOf, h v (hl v hv)]; exact hag v hv u

/-- **On a well-shaped word every column is listed**: the candidates are the stacks whose encoding
agrees with it on any `A` columns. -/
theorem candidates_of_wellShaped {μ R A : ℕ} {W : Word} (hW : WellShaped (2 ^ laneBits) W) :
    Candidates μ R A W = AgreeingStacks μ R A W := by
  ext q
  exact ⟨fun ⟨S, hS, _, hag⟩ ↦ ⟨S, hS, hag⟩, fun ⟨S, hS, hag⟩ ↦ ⟨S, hS, fun v _ ↦ hW v, hag⟩⟩

end
end LeanVM.Protocol.EndToEnd
