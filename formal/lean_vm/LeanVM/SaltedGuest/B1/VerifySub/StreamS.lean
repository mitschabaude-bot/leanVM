/-
  LeanVM.SaltedGuest.B1.VerifySub.StreamS

  The salted `verify_sub` reads the proof's words from its cursor: the stream up to the opening.
-/

module

public import LeanVM.SaltedGuest.B1.VerifySub.FrontAll
public import LeanVM.Guest.B1.VerifySub.Stream

/-!
# The salted stream

`vs_streamS`: the deployed `vs_stream` at the salted values: the words from the cursor `29` to
`683` are the announced words, the stack's root, the bus's GKR words, the tables' and the Keccak
segment's.
-/

namespace LeanVM.SaltedGuest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub

@[expose] public section

theorem vs_streamS {κ : ℕ} (hκ : κ ≤ 32) (L : MemoryImage κ) {bytecode : List K} {C : CallRel}
    {σ : Val} (F : VsFrontS bytecode C L.read σ) {xsK : List E}
    (hxsK : ReadsAt L.read (σ (.n 651)) xsK) (e683 : σ (.n 683) = σ (.n 651) * gen ^ xsK.length) :
    wordsAt L.read (σ (.n 29)) (cursorLen (σ (.n 29)) (σ (.n 683))) =
      vsWordsS σ ++ [σ (.n 334), σ (.n 344)] ++ F.xsG ++ F.xsT ++ xsK := by
  -- the cursor after the bus's GKR
  have e641 : σ (.n 641) = σ (.n 29) * gen ^ 10 * gen ^ F.xsG.length := by
    have hr := F.hretG
    rw [show [σ (.n 636), σ (.n 637), σ (.n 638), σ (.n 639), σ (.n 640), σ (.n 641), σ (.n 642),
      σ (.n 643), σ (.n 644)] = ([σ (.n 636), σ (.n 637), σ (.n 638), σ (.n 639), σ (.n 640)] ++
        [σ (.n 641)]) ++ [σ (.n 642), σ (.n 643), σ (.n 644)] from rfl] at hr
    obtain ⟨h1, -⟩ := List.append_inj' hr (by rw [F.hvL]; rfl)
    obtain ⟨-, h2⟩ := List.append_inj' h1 rfl
    simpa using h2
  -- the words
  have h10 : ReadsAt L.read (σ (.n 29)) (vsWordsS σ ++ [σ (.n 334), σ (.n 344)]) := by
    intro k hk
    simp only [vsWordsS, List.cons_append, List.nil_append, List.length_cons, List.length_nil] at hk
    have hw := F.hw
    interval_cases k
    · exact (hw 0 (by norm_num)).1
    · exact (hw 1 (by norm_num)).1
    · exact (hw 2 (by norm_num)).1
    · exact (hw 3 (by norm_num)).1
    · exact (hw 4 (by norm_num)).1
    · exact (hw 5 (by norm_num)).1
    · exact (hw 6 (by norm_num)).1
    · exact (hw 7 (by norm_num)).1
    · exact F.w8.1
    · exact F.w9.1
  have hlen10 : (vsWordsS σ ++ [σ (.n 334), σ (.n 344)]).length = 10 := rfl
  have hall : ReadsAt L.read (σ (.n 29))
      (vsWordsS σ ++ [σ (.n 334), σ (.n 344)] ++ F.xsG ++ F.xsT ++ xsK) := by
    rw [readsAt_append, readsAt_append, readsAt_append]
    refine ⟨⟨⟨h10, ?_⟩, ?_⟩, ?_⟩
    · rw [hlen10]; exact F.hxsG
    · rw [List.length_append, hlen10, pow_add, ← mul_assoc, ← e641]; exact F.hxsT
    · rw [List.length_append, List.length_append, hlen10, pow_add, pow_add, ← mul_assoc,
        ← mul_assoc, ← e641, ← F.e854]
      exact hxsK
  have hq : σ (.n 683) = σ (.n 29) *
      gen ^ (vsWordsS σ ++ [σ (.n 334), σ (.n 344)] ++ F.xsG ++ F.xsT ++ xsK).length := by
    rw [e683, F.e854, e641]
    simp only [List.length_append, hlen10, pow_add]
    ring
  rw [cursorLen_eq (ne_zero_of_load (by omega) L F.w8.1) hq (mem_size_le hκ L hall),
    wordsAt_eq hall]

end
end LeanVM.SaltedGuest.B1.VerifySub
