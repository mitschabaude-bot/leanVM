/-
  LeanVM.SaltedGuest.B1.VerifySub.Front

  The salted `verify_sub`'s front sections: the seed, the announced words, the root, the bus
  challenges.
-/

module

public import LeanVM.SaltedGuest.B1.VerifySub.Template
public import LeanVM.Protocol.KeccakHash
public import LeanVM.Guest.Value.KeccakSponge
public import LeanVM.Guest.B1.VerifySub.Front
public import LeanVM.SecondDigest.Verifier

/-!
# The front of `verify_sub`

* `vs_seedS`: the seed's `KECCAK` (`keccak_cells([seed_0, seed_1, pi_0, pi_1, seed_0, seed_1],
  sp, final=0)`): the two pairs of cells are digests' and its capacity is
  `keccakF (seedInput₂ seed pi seed)`'s;
* `vsReadsT_holdsS`, `vs_absorb8S`: the eight announced words read from the stream and, from the
  seed's capacity, absorbed (the first four permuted in);
* `vsRootsT_holdsS`, `vs_absorbRootS`: the root's two words read, the last four announced words
  permuted in;
* `vsSqzT_holdsS`, `vsAlphasT_holdsS`: squeezes, the four bus challenges.
-/

namespace LeanVM.SaltedGuest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest LeanVM.Guest.B1.VerifySub Recursion.SecondDigest
open LeanVM.Guest.Value.Keccak LeanVM.Guest.Value.KeccakEval

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val} {next : Prop} {kret : List E → Prop}

/-! ## The seed -/

/-- The seed's `KECCAK` atom. -/
abbrev vsSeedAtomS : Atom :=
  .keccak [.n 2, .n 3, .n 0, .n 1, .n 7, .n 8, .n 9, .n 10, .n 12, .n 12, .n 13, .n 14, .n 15]
    (vsRun 16 13) false false

/-- The head: the seed's copies, the zero cells, the seed's atom. -/
theorem vsHeadT_holdsS (h : Stmt.HoldsList C rd σ vsHeadS next kret) :
    σ (.n 7) = σ (.n 2) ∧ σ (.n 8) = σ (.n 3) ∧ σ (.n 9) = 0 ∧ σ (.n 10) = 0 ∧
      σ (.n 12) = 0 ∧ σ (.n 13) = 0 ∧ σ (.n 14) = 0 ∧ σ (.n 15) = 0 ∧ vsSeedAtomS.Holds rd σ ∧
      next := by
  simp only [vsHeadS, vsAlloc, vsConst, keccakA, Stmt.HoldsList, Stmt.Holds] at h
  obtain ⟨-, c7, c8, h9, h10, -, h12, h13, h14, h15, hk, -, -, -, hn⟩ := h
  simp only [Atom.Holds, word_zero] at c7 c8 h9 h10 h12 h13 h14 h15
  exact ⟨c7, c8, h9, h10, h12, h13, h14, h15, hk, hn⟩

/-- **The seed call of two digests**: one block of the IV's, the first digest's and the second
digest's cells, zero-extended, is `keccakF (seedInput₂ iv pi second)`. -/
theorem absorbChunks_seed₂ (iv pi second : Digest) :
    Keccak.absorbChunks 1 Keccak.zeroState (cellsBytes [(digestHalves iv).1, (digestHalves iv).2,
      (digestHalves pi).1, (digestHalves pi).2, (digestHalves second).1, (digestHalves second).2]) =
      keccakF1600 (seedInput₂ iv pi second) := by
  rw [Keccak.absorbChunks, Keccak.absorbChunks, Keccak.absorbBlock_take, absorbBlock_eq]
  refine congrArg keccakF1600 ?_
  apply Vector.ext
  intro i hi
  simp only [xorRate, Vector.getElem_ofFn, seedInput₂]
  split
  · rename_i h17
    rw [Keccak.leLane_cellsBytes, Keccak.lane_zeroState, UInt64.zero_xor]
    interval_cases i <;> simp [digestHalves, limb_zero]
  · rename_i h17
    rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega),
      Keccak.lane_zeroState]

/-- **The seed**: the four cells are two digests' cells, and the capacity the atom writes is the
seed state of the child's digest under the seed (`seedInput₂ seed pi seed`). -/
theorem vs_seedS (hk : vsSeedAtomS.Holds rd σ) (h7 : σ (.n 7) = σ (.n 2)) (h8 : σ (.n 8) = σ (.n 3))
    (h9 : σ (.n 9) = 0) (h10 : σ (.n 10) = 0) (h12 : σ (.n 12) = 0) (h13 : σ (.n 13) = 0)
    (h14 : σ (.n 14) = 0) (h15 : σ (.n 15) = 0) :
    ∃ seed pi : Digest, (σ (.n 2), σ (.n 3)) = digestHalves seed ∧
      (σ (.n 0), σ (.n 1)) = digestHalves pi ∧
      [σ (.n 24), σ (.n 25), σ (.n 26), σ (.n 27), σ (.n 28)] =
        capOf (keccakF1600 (seedInput₂ seed pi seed)) := by
  obtain ⟨-, -, hc, -⟩ := keccakA_perm hk
  obtain ⟨seed, es⟩ := digest_of_canonical (hc (σ (.n 2)) (by simp)) (hc (σ (.n 3)) (by simp))
  obtain ⟨pi, ep⟩ := digest_of_canonical (hc (σ (.n 0)) (by simp)) (hc (σ (.n 1)) (by simp))
  refine ⟨seed, pi, es, ep, ?_⟩
  obtain ⟨-, -, hK⟩ := (keccak_holds_13 (outs := vsRun 16 13) (by simp [vsRun])).mp hk
  have hch := Keccak.keccak_chain
    (P := [σ (.n 2), σ (.n 3), σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3)]) (S0 := Keccak.zeroState)
    (B := 1)
    (I := fun _ ↦ cells13 ([.n 2, .n 3, .n 0, .n 1, .n 7, .n 8, .n 9, .n 10, .n 12, .n 12,
      .n 13, .n 14, .n 15].map σ))
    (O := fun k ↦ if k = 0 then cellsOfState Keccak.zeroState false else cells13 ((vsRun 16 13).map σ))
    (by simp)
    (fun k hk c hc ↦ by
      obtain rfl : k = 0 := by omega
      fin_cases c <;> simp_all [cells13, Keccak.cellsOfState_zero])
    (fun k hk c hc ↦ by
      obtain rfl : k = 0 := by omega
      fin_cases c <;> simp_all [cells13, Keccak.cellsOfState_zero])
    (fun k hk ↦ by
      obtain rfl : k = 0 := by omega
      exact hK)
  simp only [one_ne_zero, ↓reduceIte] at hch
  rw [show [σ (.n 2), σ (.n 3), σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3)] = [(digestHalves seed).1,
    (digestHalves seed).2, (digestHalves pi).1, (digestHalves pi).2, (digestHalves seed).1,
    (digestHalves seed).2] by rw [← es, ← ep], absorbChunks_seed₂] at hch
  simp only [capOf]
  rw [← congrFun hch 8, ← congrFun hch 9, ← congrFun hch 10, ← congrFun hch 11, ← congrFun hch 12]
  rfl

/-! ## The announced words -/

/-- The values of the eight announced words. -/
def vsXS (i : ℕ) : ℕ := [31, 41, 51, 61, 84, 94, 104, 114].getD i 0

/-- Word `i` read at stream offset `off` into `x`, packed (`fs_next`). -/
def WordAtS (rd : Reader) (σ : Val) (off x : ℕ) : Prop :=
  LoadHolds rd (σ (.n 29)) off (σ (.n x)) ∧ FsPackOk σ (.n x) (x + 1) dsObserve

/-- The announced words' perm atom. -/
abbrev vsAtom50S : Atom :=
  .keccak [.n 38, .n 40, .n 48, .n 50, .n 58, .n 60, .n 68, .n 70, .n 24, .n 25, .n 26, .n 27, .n 28]
    (vsRun 71 13) false false

theorem vsReadsT_holdsS (h : Stmt.HoldsList C rd σ vsReadsS next kret) :
    (∀ i < 8, WordAtS rd σ i (vsXS i)) ∧
      (∀ i < 6, LoadHolds rd (σ (.n 30)) i (σ (.n (vsXS (i + 1))))) ∧ vsAtom50S.Holds rd σ ∧ next := by
  rw [vsReadsS] at h
  simp only [holdsList_append] at h
  obtain ⟨w0, h⟩ := (holds_fsNextT _ _ _ _ _).1 h
  obtain ⟨w1, h⟩ := (holds_fsNextT _ _ _ _ _).1 h
  obtain ⟨r1, h⟩ := holds_ld1.1 h
  obtain ⟨w2, h⟩ := (holds_fsNextT _ _ _ _ _).1 h
  obtain ⟨r2, h⟩ := holds_ld1.1 h
  obtain ⟨w3, h⟩ := (holds_fsNextT _ _ _ _ _).1 h
  obtain ⟨r3, h⟩ := holds_ld1.1 h
  obtain ⟨hk, h⟩ := holds_atom1.1 h
  obtain ⟨w4, h⟩ := (holds_fsNextT _ _ _ _ _).1 h
  obtain ⟨r4, h⟩ := holds_ld1.1 h
  obtain ⟨w5, h⟩ := (holds_fsNextT _ _ _ _ _).1 h
  obtain ⟨r5, h⟩ := holds_ld1.1 h
  obtain ⟨w6, h⟩ := (holds_fsNextT _ _ _ _ _).1 h
  obtain ⟨r6, h⟩ := holds_ld1.1 h
  obtain ⟨w7, hn⟩ := (holds_fsNextT _ _ _ _ _).1 h
  refine ⟨fun i hi ↦ ?_, fun i hi ↦ ?_, hk, hn⟩
  · interval_cases i
    · exact w0
    · exact w1
    · exact w2
    · exact w3
    · exact w4
    · exact w5
    · exact w6
    · exact w7
  · interval_cases i
    · exact r1
    · exact r2
    · exact r3
    · exact r4
    · exact r5
    · exact r6

/-- The eight announced words' values. -/
def vsWordsS (σ : Val) : List E :=
  [σ (.n 31), σ (.n 41), σ (.n 51), σ (.n 61), σ (.n 84), σ (.n 94), σ (.n 104), σ (.n 114)]

/-- A word's two packed cells, once the first is canonical. -/
theorem wordAt_cellsS {off x : ℕ} (h : WordAtS rd σ off x) (hc : IsCanonical128 (σ (.n (x + 7)))) :
    (σ (.n (x + 7)), σ (.n (x + 9))) = Keccak.scalarCells (σ (.n x)) dsObserve :=
  fsPackT_cells h.2 hc

/-- **The announced words absorbed** from the seed's capacity: the first four permuted in by the
atom, the last four waiting. -/
theorem vs_absorb8S (hw : ∀ i < 8, WordAtS rd σ i (vsXS i)) (hk : vsAtom50S.Holds rd σ) :
    (⟨[σ (.n 24), σ (.n 25), σ (.n 26), σ (.n 27), σ (.n 28)], []⟩ : Fs).absorbAll (vsWordsS σ)
        dsObserve =
      ⟨[σ (.n 79), σ (.n 80), σ (.n 81), σ (.n 82), σ (.n 83)],
        [(σ (.n 84), dsObserve), (σ (.n 94), dsObserve), (σ (.n 104), dsObserve),
          (σ (.n 114), dsObserve)]⟩ := by
  have hcap := keccak_cap hk
  rw [vsRun_drop8] at hcap
  obtain ⟨-, -, hc, -⟩ := keccakA_perm hk
  have c0 := wordAt_cellsS (hw 0 (by omega)) (hc (σ (.n 38)) (List.mem_map_of_mem (by simp)))
  have c1 := wordAt_cellsS (hw 1 (by omega)) (hc (σ (.n 48)) (List.mem_map_of_mem (by simp)))
  have c2 := wordAt_cellsS (hw 2 (by omega)) (hc (σ (.n 58)) (List.mem_map_of_mem (by simp)))
  have c3 := wordAt_cellsS (hw 3 (by omega)) (hc (σ (.n 68)) (List.mem_map_of_mem (by simp)))
  simp only [vsXS, List.getD_cons_zero, List.getD_cons_succ] at c0 c1 c2 c3
  have e := absorb8_shape [σ (.n 24), σ (.n 25), σ (.n 26), σ (.n 27), σ (.n 28)] (σ (.n 31))
    (σ (.n 41)) (σ (.n 51)) (σ (.n 61)) (σ (.n 84)) (σ (.n 94)) (σ (.n 104)) (σ (.n 114))
  have hl : rateOf [(σ (.n 31), dsObserve), (σ (.n 41), dsObserve), (σ (.n 51), dsObserve),
      (σ (.n 61), dsObserve)] ++ [σ (.n 24), σ (.n 25), σ (.n 26), σ (.n 27), σ (.n 28)] =
      List.map σ [.n 38, .n 40, .n 48, .n 50, .n 58, .n 60, .n 68, .n 70, .n 24, .n 25, .n 26,
        .n 27, .n 28] := by
    rw [rateOf_four, ← c0, ← c1, ← c2, ← c3]; rfl
  rw [vsWordsS, e, Fs.perm, hl, ← hcap]

/-! ## The root -/

/-- The root's perm atom: the last four announced words. -/
abbrev vsAtom649S : Atom :=
  .keccak [.n 91, .n 93, .n 101, .n 103, .n 111, .n 113, .n 121, .n 123, .n 79, .n 80, .n 81, .n 82,
    .n 83] (vsRun 321 13) false false

theorem vsRootsT_holdsS (h : Stmt.HoldsList C rd σ vsRootsS next kret) :
    vsAtom649S.Holds rd σ ∧ WordAtS rd σ 8 334 ∧ WordAtS rd σ 9 344 ∧
      C "assert_canonical" [σ (.n 334)] [σ (.n 354)] ∧
      C "assert_canonical" [σ (.n 344)] [σ (.n 355)] ∧ next := by
  rw [vsRootsS] at h
  simp only [holdsList_append] at h
  obtain ⟨hk, h⟩ := holds_atom1.1 h
  obtain ⟨w8, h⟩ := (holds_fsNextT _ _ _ _ _).1 h
  obtain ⟨w9, h⟩ := (holds_fsNextT _ _ _ _ _).1 h
  obtain ⟨c1, c2, -, hn⟩ := h
  exact ⟨hk, w8, w9, c1, c2, hn⟩

/-- **The root's words absorbed** after the announced ones: the last four permuted in. -/
theorem vs_absorbRootS (hw : ∀ i < 8, WordAtS rd σ i (vsXS i)) (hk : vsAtom649S.Holds rd σ) :
    (((⟨[σ (.n 79), σ (.n 80), σ (.n 81), σ (.n 82), σ (.n 83)],
        [(σ (.n 84), dsObserve), (σ (.n 94), dsObserve), (σ (.n 104), dsObserve),
          (σ (.n 114), dsObserve)]⟩ : Fs).absorb (σ (.n 334)) dsObserve).absorb (σ (.n 344))
        dsObserve) =
      ⟨[σ (.n 329), σ (.n 330), σ (.n 331), σ (.n 332), σ (.n 333)],
        [(σ (.n 334), dsObserve), (σ (.n 344), dsObserve)]⟩ := by
  have hcap := keccak_cap hk
  rw [vsRun_drop8] at hcap
  obtain ⟨-, -, hc, -⟩ := keccakA_perm hk
  have c4 := wordAt_cellsS (hw 4 (by omega)) (hc (σ (.n 91)) (List.mem_map_of_mem (by simp)))
  have c5 := wordAt_cellsS (hw 5 (by omega)) (hc (σ (.n 101)) (List.mem_map_of_mem (by simp)))
  have c6 := wordAt_cellsS (hw 6 (by omega)) (hc (σ (.n 111)) (List.mem_map_of_mem (by simp)))
  have c7 := wordAt_cellsS (hw 7 (by omega)) (hc (σ (.n 121)) (List.mem_map_of_mem (by simp)))
  simp only [vsXS, List.getD_cons_zero, List.getD_cons_succ] at c4 c5 c6 c7
  have e := absorb2_shape [σ (.n 79), σ (.n 80), σ (.n 81), σ (.n 82), σ (.n 83)] (σ (.n 84))
    (σ (.n 94)) (σ (.n 104)) (σ (.n 114)) (σ (.n 334)) (σ (.n 344))
  have hl : rateOf [(σ (.n 84), dsObserve), (σ (.n 94), dsObserve), (σ (.n 104), dsObserve),
      (σ (.n 114), dsObserve)] ++ [σ (.n 79), σ (.n 80), σ (.n 81), σ (.n 82), σ (.n 83)] =
      List.map σ [.n 91, .n 93, .n 101, .n 103, .n 111, .n 113, .n 121, .n 123, .n 79, .n 80, .n 81,
        .n 82, .n 83] := by
    rw [rateOf_four, ← c4, ← c5, ← c6, ← c7]; rfl
  rw [e, Fs.perm, hl, ← hcap]

/-! ## Squeezes -/

/-- **A squeeze with nothing waiting** (`vsSqzS`), on the zero cells. -/
theorem vsSqzT_holdsS {capb o : ℕ} (h10 : σ (.n 12) = 0) (h11 : σ (.n 13) = 0)
    (h12 : σ (.n 14) = 0) (h13 : σ (.n 15) = 0)
    (h : Stmt.HoldsList C rd σ (vsSqzS capb o) next kret) :
    (⟨(vsRun capb 5).map σ, []⟩ : Fs).squeeze =
        (σ (.n (o + 19)), ⟨[σ (.n (o + 8)), σ (.n (o + 9)), σ (.n (o + 10)), σ (.n (o + 11)),
          σ (.n (o + 12))], []⟩) ∧ next := by
  simp only [vsSqzS, Stmt.HoldsList, Stmt.Holds, keccakA] at h
  obtain ⟨hk, h⟩ := h
  obtain ⟨hch, hn⟩ := (holds_challengeT _ _ _ _ _).1 h
  have hs := squeeze_atom (s := ⟨(vsRun capb 5).map σ, []⟩) (b := o + 13) hk
    (by simp only [List.map_append, List.map_cons, List.map_nil, h10, h11, h12, h13, rateOf_nil])
    hch
  rw [vsRun_drop8] at hs
  obtain ⟨e1, e2⟩ := hs
  simp only [Fs.squeeze] at e1 e2 ⊢
  rw [← e1, ← e2]
  exact ⟨rfl, hn⟩

/-- The second root word's perm atom: the root waiting, the bus's first challenge. -/
abbrev vsAtom671S : Atom :=
  .keccak [.n 341, .n 343, .n 351, .n 353, .n 12, .n 13, .n 14, .n 15, .n 329, .n 330, .n 331,
    .n 332, .n 333] (vsRun 357 13) false false

/-- **The four bus challenges** (G:3226-3232). -/
theorem vsAlphasT_holdsS (h10 : σ (.n 12) = 0) (h11 : σ (.n 13) = 0) (h12 : σ (.n 14) = 0)
    (h13 : σ (.n 15) = 0) (w8 : WordAtS rd σ 8 334) (w9 : WordAtS rd σ 9 344)
    (h : Stmt.HoldsList C rd σ vsAlphasS next kret) :
    (⟨[σ (.n 329), σ (.n 330), σ (.n 331), σ (.n 332), σ (.n 333)],
        [(σ (.n 334), dsObserve), (σ (.n 344), dsObserve)]⟩ : Fs).squeezeN 4 =
      ([σ (.n 376), σ (.n 396), σ (.n 416), σ (.n 436)],
        ⟨[σ (.n 425), σ (.n 426), σ (.n 427), σ (.n 428), σ (.n 429)], []⟩) ∧
      ReadsAt rd (σ (.n 356)) [σ (.n 376), σ (.n 396), σ (.n 416), σ (.n 436)] ∧ next := by
  simp only [vsAlphasS, holdsList_append, Stmt.HoldsList, Stmt.Holds, vsLd] at h
  obtain ⟨hk, h⟩ := h
  obtain ⟨hch, l0, h⟩ := (holds_challengeT _ _ _ _ _).1 h
  obtain ⟨s1, l1, h⟩ := vsSqzT_holdsS h10 h11 h12 h13 h
  obtain ⟨s2, l2, h⟩ := vsSqzT_holdsS h10 h11 h12 h13 h
  obtain ⟨s3, l3, hn⟩ := vsSqzT_holdsS h10 h11 h12 h13 h
  obtain ⟨-, -, hc, -⟩ := keccakA_perm hk
  have c8 := wordAt_cellsS w8 (hc (σ (.n 341)) (List.mem_map_of_mem (by simp)))
  have c9 := wordAt_cellsS w9 (hc (σ (.n 351)) (List.mem_map_of_mem (by simp)))
  have hs := squeeze_atom (s := ⟨[σ (.n 329), σ (.n 330), σ (.n 331), σ (.n 332), σ (.n 333)],
    [(σ (.n 334), dsObserve), (σ (.n 344), dsObserve)]⟩) (b := 370) hk
    (by simp only [List.map_cons, List.map_nil, h10, h11, h12, h13, rateOf_two, ← c8, ← c9]; rfl)
    hch
  rw [vsRun_drop8] at hs
  refine ⟨?_, fun k hk ↦ ?_, hn⟩
  · have e0 : (⟨[σ (.n 329), σ (.n 330), σ (.n 331), σ (.n 332), σ (.n 333)],
        [(σ (.n 334), dsObserve), (σ (.n 344), dsObserve)]⟩ : Fs).squeeze =
        (σ (.n 376), ⟨[σ (.n 365), σ (.n 366), σ (.n 367), σ (.n 368), σ (.n 369)], []⟩) :=
      Prod.ext hs.1.symm (congrArg (Fs.mk · []) hs.2.symm)
    have e1 : (⟨[σ (.n 365), σ (.n 366), σ (.n 367), σ (.n 368), σ (.n 369)], []⟩ : Fs).squeeze =
        (σ (.n 396), ⟨[σ (.n 385), σ (.n 386), σ (.n 387), σ (.n 388), σ (.n 389)], []⟩) := s1
    have e2 : (⟨[σ (.n 385), σ (.n 386), σ (.n 387), σ (.n 388), σ (.n 389)], []⟩ : Fs).squeeze =
        (σ (.n 416), ⟨[σ (.n 405), σ (.n 406), σ (.n 407), σ (.n 408), σ (.n 409)], []⟩) := s2
    have e3 : (⟨[σ (.n 405), σ (.n 406), σ (.n 407), σ (.n 408), σ (.n 409)], []⟩ : Fs).squeeze =
        (σ (.n 436), ⟨[σ (.n 425), σ (.n 426), σ (.n 427), σ (.n 428), σ (.n 429)], []⟩) := s3
    simp only [Fs.squeezeN, e0, e1, e2, e3]
  · simp only [List.length_cons, List.length_nil] at hk
    interval_cases k
    · exact l0
    · exact l1
    · exact l2
    · exact l3

end
end LeanVM.SaltedGuest.B1.VerifySub
