/-
  LeanVM.SaltedGuest.Decoder.OutputSize

  The size of the salted decoder program's output, on every execution of the salted guest.
-/

module

public import LeanVM.SaltedGuest.Decoder.Program
public import LeanVM.Cost.GuestDecoding
public import LeanVM.Cost.FieldMul
public import LeanVM.SaltedGuest.B1.Main.ChildClaims
import all LeanVM.Guest.B1.Main.Interface

/-!
# The size of the salted decoder's output

On every execution of the salted guest (valid or not, any memory size), the salted decoder
program's output within its own size and price is the encoding of its top's decoding
(`outputWithin_saltedDecoder_any`), which is `B1.Main.decK B1.VerifySub.vsPiOfK` at the salted
`main`'s valuation, the memory and the compiled frame map by name (`decTopFramesK_eq`), so its size
is that of a decoding, bounded on every input (`decK_size`):

* the encodings' sizes: a number's limbs, a list (`size_list_le`), a function of a finite domain
  and a vector (`size_fun_le`, `size_vec_le`); the fixed-size types (digests, keys, messages, the
  leanXMSS and leanSPHINCS signatures, claims);
* the decoding's lists: at most `2^34` declared claims of each scheme, children, raw signatures of
  each scheme (each count a logarithm, `Main.gLog_lt`), a child's claims at most `2^35 - 2`
  (`Main.decK_child_claims`), a child's proof's stream at most `2^32 + 121` words, its openings at
  most `6` levels of at most `227` queries, a query's row at most `64` symbols and its path at
  most `28` digests (the salted dispatches' table, `osCallsTabK`), the DA matrix at most `1024`
  rows of `128 · 256` symbols, the batching's `23` rounds.

**`saltedDecoder_output_size`**: the output's size is at most `decodingSizeBoundK`, a number
(about `2^72.9`: the children's claims dominate); **`saltedDecoder_decodings_bounded`**: the form
of `SaltedGuest.DecodingsBounded`, every decoding the output decodes to.
-/

namespace LeanVM.SaltedGuest.Decoder

open LeanVM.Cost LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Fast
open LeanVM.Guest.B1 LeanVM.Guest.B1.Whir LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Node LeanVM.Cost.Decoder LeanVM.SaltedGuest.B1

@[expose] public section

/-! ## Encodings' sizes -/

theorem size_ctor (t : ℕ) (fs : List MachineValue) :
    (MachineValue.constructor t fs).size = MachineValue.sizeList fs + 1 := by
  simp only [MachineValue.size]

theorem sizeList_cons (v : MachineValue) (vs : List MachineValue) :
    MachineValue.sizeList (v :: vs) = v.size + MachineValue.sizeList vs := by
  simp only [MachineValue.sizeList]

theorem sizeList_nil : MachineValue.sizeList [] = 0 := by simp only [MachineValue.sizeList]

theorem size_nat_of_lt {n : ℕ} (h : n < 2 ^ 64) : (MachineValue.nat n).size = 1 := by
  simp only [MachineValue.size, limbs_of_lt h]

theorem size_ofList_le : ∀ (vs : List MachineValue) (b : ℕ), (∀ v ∈ vs, v.size ≤ b) →
    (MachineValue.ofList vs).size ≤ vs.length * (b + 1) + 1
  | [], b, _ => by simp [MachineValue.ofList, MachineValue.size, MachineValue.sizeList]
  | v :: vs, b, h => by
    have ih := size_ofList_le vs b (fun w hw ↦ h w (List.mem_cons_of_mem _ hw))
    have hv := h v List.mem_cons_self
    simp only [MachineValue.ofList, size_ctor, sizeList_cons, sizeList_nil, List.length_cons,
      Nat.succ_mul]
    generalize vs.length * (b + 1) = A at ih ⊢
    omega

/-- **A list's size**: at most `n` elements of size at most `b`. -/
theorem size_list_le {α : Type} [MachineEncoding α] (l : List α) {n b : ℕ} (hn : l.length ≤ n)
    (h : ∀ x ∈ l, (encodeValue x).size ≤ b) : (encodeValue l).size ≤ n * (b + 1) + 1 := by
  have := size_ofList_le (l.map encodeValue) b (by simpa using h)
  rw [List.length_map] at this
  exact this.trans (by have := Nat.mul_le_mul_right (b + 1) hn; omega)

theorem sizeList_ofFn_le : ∀ {n : ℕ} (f : Fin n → MachineValue) (b : ℕ), (∀ i, (f i).size ≤ b) →
    MachineValue.sizeList (List.ofFn f) ≤ n * b
  | 0, _, _, _ => by simp [sizeList_nil]
  | n + 1, f, b, h => by
    rw [List.ofFn_succ, sizeList_cons, Nat.succ_mul]
    have := sizeList_ofFn_le (fun i ↦ f i.succ) b (fun i ↦ h i.succ)
    have := h 0
    generalize n * b = A at *
    omega

theorem size_arrayOfFn_le {n : ℕ} (f : Fin n → MachineValue) (b : ℕ) (h : ∀ i, (f i).size ≤ b) :
    (MachineValue.array (Array.ofFn f)).size ≤ n * b + 1 := by
  simp only [MachineValue.size, Array.toList_ofFn]
  have := sizeList_ofFn_le f b h
  omega

/-- **A function of a finite domain's size.** -/
theorem size_fun_le {α : Type} [MachineEncoding α] {n : ℕ} (f : Fin n → α) {b : ℕ}
    (h : ∀ x : α, (encodeValue x).size ≤ b) : (encodeValue f).size ≤ n * b + 1 :=
  size_arrayOfFn_le _ b fun i ↦ h (f i)

/-- **A vector's size.** -/
theorem size_vec_le {α : Type} [MachineEncoding α] {n : ℕ} (v : Vector α n) {b : ℕ}
    (h : ∀ x : α, (encodeValue x).size ≤ b) : (encodeValue v).size ≤ n * b + 1 := by
  show (MachineValue.array (v.toArray.map encodeValue)).size ≤ _
  have : v.toArray.map encodeValue = Array.ofFn fun i : Fin n ↦ encodeValue (v.get i) := by
    apply Array.ext
    · simp
    · intro i h1 h2; simp [Vector.get]
  rw [this]
  exact size_arrayOfFn_le _ b fun i ↦ h _

theorem size_pair {α β : Type} [MachineEncoding α] [MachineEncoding β] (p : α × β) :
    (encodeValue p).size = (encodeValue p.1).size + (encodeValue p.2).size + 1 := by
  show (MachineValue.constructor 0 _).size = _
  simp only [size_ctor, sizeList_cons, sizeList_nil]
  omega

/-! ## The fixed-size types -/

theorem size_u64 (x : UInt64) : (encodeValue x).size = 1 := size_nat_of_lt x.toNat_lt_size

theorem size_K (a : K) : (encodeValue a).size = 1 := size_nat_of_lt a.lane.toNat_lt_size

theorem size_E (x : E) : (encodeValue x).size = 4 := by
  show (MachineValue.constructor 0 [encodeValue (x.limb 0), encodeValue (x.limb 1),
    encodeValue (x.limb 2)]).size = 4
  simp only [size_ctor, sizeList_cons, sizeList_nil, size_K]

theorem size_bv {w : ℕ} (v : BitVec w) : (encodeValue v).size ≤ w / 64 + 1 := by
  show limbCount v.toNat ≤ _
  refine limbCount_le_of_lt_two_pow (by omega) (v.isLt.trans_le (Nat.pow_le_pow_right (by norm_num) ?_))
  omega

theorem size_fin {n : ℕ} (hn : n ≤ 2 ^ 64) (i : Fin n) : (encodeValue i).size = 1 :=
  size_nat_of_lt (i.isLt.trans_le hn)

theorem size_digest (d : Digest) : (encodeValue d).size ≤ 5 :=
  (size_vec_le d fun x ↦ (size_u64 x).le).trans (by norm_num)

theorem size_hsDigest (d : HashSig.Digest) : (encodeValue d).size ≤ 3 :=
  (size_bv d).trans (by simp [HashSig.digestBits])

theorem size_message (m : HashSig.Message) : (encodeValue m).size ≤ 5 := (size_bv m).trans (by norm_num)

theorem size_param (p : HashSig.PublicParameter) : (encodeValue p).size ≤ 3 :=
  (size_bv p).trans (by norm_num)

theorem size_xmssKey (k : HashSig.PublicKey) : (encodeValue k).size ≤ 7 := by
  show (MachineValue.constructor 0 [encodeValue k.root, encodeValue k.parameter]).size ≤ 7
  simp only [size_ctor, sizeList_cons, sizeList_nil]
  have := size_hsDigest k.root; have := size_param k.parameter; omega

theorem size_sphincsKey (k : Sphincs.PublicKey) : (encodeValue k).size ≤ 7 := by
  show (MachineValue.constructor 0 [encodeValue k.publicSeed, encodeValue k.root]).size ≤ 7
  simp only [size_ctor, sizeList_cons, sizeList_nil]
  have := size_param k.publicSeed; have := size_hsDigest k.root; omega

theorem size_xmssClaim (c : LeanXmssClaim) : (encodeValue c).size ≤ 13 := by
  rw [size_pair]; have := size_xmssKey c.1; have := size_message c.2; omega

theorem size_sphincsClaim (c : LeanSphincsClaim) : (encodeValue c).size ≤ 13 := by
  rw [size_pair]; have := size_sphincsKey c.1; have := size_message c.2; omega

theorem size_xmssLayer (s : LeanXmss.LayerSignature) : (encodeValue s).size ≤ 228 := by
  show (MachineValue.constructor 0 [encodeValue s.randomizer, encodeValue s.chainValues,
    encodeValue s.authenticationPath]).size ≤ 228
  simp only [size_ctor, sizeList_cons, sizeList_nil]
  have h1 := size_hsDigest s.randomizer
  have h2 := size_fun_le s.chainValues size_hsDigest
  have h3 := size_fun_le s.authenticationPath size_hsDigest
  simp only [LeanXmss.chainCount, LeanXmss.layerHeight] at h2 h3
  omega

theorem size_xmssSig (s : LeanXmss.Signature) : (encodeValue s).size ≤ 459 := by
  show (MachineValue.constructor 0 [encodeValue s.leafIndex, encodeValue s.layers]).size ≤ 459
  simp only [size_ctor, sizeList_cons, sizeList_nil]
  have h1 := size_fin (by simp [LeanXmss.lifetime, LeanXmss.layerCount, LeanXmss.layerHeight]) s.leafIndex
  have h2 := size_fun_le s.layers size_xmssLayer
  simp only [LeanXmss.layerCount] at h2
  omega

theorem size_fors (o : Sphincs.ForsTreeOpening) : (encodeValue o).size ≤ 35 := by
  show (MachineValue.constructor 0 [encodeValue o.secret, encodeValue o.path]).size ≤ 35
  simp only [size_ctor, sizeList_cons, sizeList_nil]
  have h1 := size_hsDigest o.secret
  have h2 := size_fun_le o.path size_hsDigest
  simp only [Sphincs.forsTreeHeight] at h2
  omega

theorem size_spLayer (l : Sphincs.Layer) (s : Sphincs.LayerSignature l) :
    (encodeValue s).size ≤ 226 := by
  show (MachineValue.constructor 0 [encodeValue s.counter, encodeValue s.chainValues,
    encodeValue s.authenticationPath]).size ≤ 226
  simp only [size_ctor, sizeList_cons, sizeList_nil]
  have h1 := size_bv s.counter
  have h2 := size_fun_le s.chainValues size_hsDigest
  have h3 := size_fun_le s.authenticationPath size_hsDigest
  have hl : Sphincs.layerHeight l ≤ 10 := by unfold Sphincs.layerHeight; split <;> omega
  have h4 := Nat.mul_le_mul_right 3 hl
  simp only [Sphincs.chainCount, Sphincs.counterBits] at h1 h2
  omega

theorem size_ctor3 (x y z : MachineValue) :
    (MachineValue.constructor 0 [x, y, z]).size = x.size + y.size + z.size + 1 := by
  simp only [size_ctor, sizeList_cons, sizeList_nil]
  omega

theorem size_sphincsSig (s : Sphincs.Signature) : (encodeValue s).size ≤ 1524 := by
  show (MachineValue.constructor 0 [encodeValue s.randomizer, encodeValue s.forsOpening,
    .array (Array.ofFn fun layer ↦ encodeValue (s.layers layer))]).size ≤ 1524
  rw [size_ctor3]
  have h1 := size_hsDigest s.randomizer
  have h2 := size_fun_le s.forsOpening size_fors
  refine le_trans (Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add h1 h2)
    (size_arrayOfFn_le _ 226 fun layer ↦ size_spLayer layer _)) 1) ?_
  simp only [Sphincs.forsTreeCount, Sphincs.layerCount]
  norm_num

theorem size_bcClaim (c : BytecodeClaim) (hc : c.bytecodePoint.length ≤ 23) :
    (encodeValue c).size ≤ 121 := by
  show (MachineValue.constructor 0 [encodeValue c.bytecodePoint, encodeValue c.bytecodeValue]).size ≤ 121
  simp only [size_ctor, sizeList_cons, sizeList_nil, size_E]
  have := size_list_le c.bytecodePoint hc fun x _ ↦ (size_E x).le
  omega

theorem size_daClaim (c : DaClaim) : (encodeValue c).size ≤ 10 := by
  show (MachineValue.constructor 0 [encodeValue c.daRoot, encodeValue c.membershipChallenge]).size ≤ 10
  simp only [size_ctor, sizeList_cons, sizeList_nil, size_E]
  have := size_digest c.daRoot
  omega

theorem deferOfCells_len (cs : List E) : (Main.deferOfCells cs).bytecodePoint.length ≤ 23 := by
  simp [Main.deferOfCells]

theorem fixedOfCells_len (cs : List E) : (Main.fixedOfCells cs).bytecodePoint.length ≤ 23 := by
  simp [Main.fixedOfCells]

/-! ## Lengths -/

theorem length_flatMap_le {α β : Type} (l : List α) (f : α → List β) {k : ℕ}
    (h : ∀ x ∈ l, (f x).length ≤ k) : (l.flatMap f).length ≤ l.length * k := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul]
    have h1 := h x List.mem_cons_self
    have h2 := ih fun y hy ↦ h y (List.mem_cons_of_mem _ hy)
    omega

/-- The salted dispatches' table's numbers. -/
def tabOkB : Bool :=
  osCallsTabK.all fun r ↦ decide (r.length ≤ 6) && r.all fun c ↦ decide (c.odd ≤ 1) &&
    decide (c.N ≤ 113) && decide (c.pd + c.cd ≤ 28) &&
    ((c.base == 1 && c.I == 64) || (c.base == 0 && c.I == 16))

set_option maxRecDepth 100000 in
theorem tabOkB_true : tabOkB = true := by decide +kernel

theorem tab_row (j : ℕ) : (osCallsTabK.getD j []).length ≤ 6 ∧ ∀ c ∈ osCallsTabK.getD j [],
    c.odd ≤ 1 ∧ c.N ≤ 113 ∧ c.pd + c.cd ≤ 28 ∧ (Oq.R ⟨c.base, c.I, c.pd, c.cd⟩) ≤ 64 := by
  have h := tabOkB_true
  simp only [tabOkB, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true,
    beq_iff_eq] at h
  rw [List.getD_eq_getElem?_getD]
  cases hj : osCallsTabK[j]? with
  | none => simp
  | some r =>
    obtain ⟨h1, h2⟩ := h r (List.mem_of_getElem? hj)
    refine ⟨h1, fun c hc ↦ ?_⟩
    obtain ⟨⟨⟨ho, hN⟩, hpc⟩, hs⟩ := h2 c hc
    refine ⟨ho, hN, hpc, ?_⟩
    unfold Oq.R
    rcases hs with ⟨hb, hI⟩ | ⟨hb, hI⟩ <;> simp [hb, hI]

theorem osWordsTab_le (j : ℕ) : osWordsTab.getD j 0 ≤ 121 := by
  have h : osWordsTab.all (fun x ↦ decide (x ≤ 121)) = true := by decide +kernel
  rw [List.getD_eq_getElem?_getD]
  cases hj : osWordsTab[j]? with
  | none => simp
  | some x =>
    have := (List.all_eq_true.mp h) x (List.mem_of_getElem? hj)
    simpa using this

theorem cursorLen_le (p q : E) : VerifySub.cursorLen p q ≤ 2 ^ 32 := by
  unfold VerifySub.cursorLen
  cases h : (List.range (2 ^ 32 + 1)).find? (fun n ↦ decide (q = p * gen ^ n)) with
  | none => simp
  | some n =>
    have := List.mem_range.mp (List.mem_of_find?_eq_some h)
    simp only [Option.getD_some]
    omega

/-! ## A child's proof -/

/-- What a query's witness is: its position below `2^d`, its row of `R` symbols, its siblings
`pd`. -/
def QWOk (s : Oq) (w : QW) : Prop :=
  w.1 < 2 ^ (s.pd + s.cd) ∧ w.2.1.length = s.R ∧ w.2.2.length = s.pd

theorem oqQueryNK_ok (s : Oq) (walk : ℕ) (rd : Reader) (bp cap flags : E) (b : ℕ) (emit : Bool)
    (σ : Val) (Vn : NFrames) : QWOk s (oqQueryNK s walk rd bp cap flags b emit σ Vn) := by
  refine ⟨?_, ?_, ?_⟩
  · exact LeanVM.Guest.Value.bitsVal_lt _ _
  · simp [oqQueryNK, oqRow]
  · simp [oqQueryNK, oqSibsOf]

theorem oqIterNK_ok (s : Oq) (walk : ℕ) (rd : Reader) (σ : Val) (Vn : NFrames) :
    (oqIterNK s walk rd σ Vn).length ≤ 2 ∧ ∀ w ∈ oqIterNK s walk rd σ Vn, QWOk s w := by
  unfold oqIterNK
  split
  · refine ⟨by simp, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro w (rfl | rfl) <;> exact oqQueryNK_ok _ _ _ _ _ _ _ _ _ _
  · refine ⟨by simp, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro w rfl
    exact oqQueryNK_ok _ _ _ _ _ _ _ _ _ _

theorem oqsOfNK_ok (s : Oq) (odd loop walk N : ℕ) (rd : Reader) (σ : Val) (Vn : NFrames) :
    (oqsOfNK s odd loop walk N rd σ Vn).length ≤ odd + 2 * N ∧
      ∀ w ∈ oqsOfNK s odd loop walk N rd σ Vn, QWOk s w := by
  unfold oqsOfNK
  refine ⟨?_, ?_⟩
  · rw [List.length_append]
    have h1 : (if odd = 1 then [oqQueryNK s walk rd (σ (.n 25)) (σ (.n 0)) (σ (.n 1)) 26 true σ Vn]
        else []).length ≤ odd := by split <;> simp_all
    have h2 := length_flatMap_le (List.range N)
      (fun j ↦ oqIterNK s walk rd (Vn loop (gen ^ j :: oqLoopArgsK σ) []) Vn)
      (k := 2) fun j _ ↦ (oqIterNK_ok _ _ _ _ _).1
    rw [List.length_range] at h2
    omega
  · intro w hw
    rw [List.mem_append] at hw
    rcases hw with hw | hw
    · split at hw
      · rw [List.mem_singleton] at hw; subst hw; exact oqQueryNK_ok _ _ _ _ _ _ _ _ _ _
      · cases hw
    · obtain ⟨j, -, hj⟩ := List.mem_flatMap.mp hw
      exact (oqIterNK_ok _ _ _ _ _).2 w hj

theorem size_opening (o : Opening) (h1 : o.leafIndex < 2 ^ 64) (h2 : o.leaf.length ≤ 64)
    (h3 : o.path.length ≤ 28) : (encodeValue o).size ≤ 300 := by
  show (MachineValue.constructor 0 [encodeValue o.leafIndex, encodeValue o.leaf,
    encodeValue o.path]).size ≤ 300
  rw [size_ctor3]
  have a1 : (encodeValue o.leafIndex).size = 1 := size_nat_of_lt h1
  have a2 := size_list_le o.leaf h2 fun x _ ↦ (size_K x).le
  have a3 := size_list_le o.path h3 fun x _ ↦ size_digest x
  omega

theorem levelOsNK_ok (rd : Reader) (σ : Val) (Vn : NFrames) (c : OsCall) (ho : c.odd ≤ 1)
    (hN : c.N ≤ 113) (hpc : c.pd + c.cd ≤ 28) (hR : Oq.R ⟨c.base, c.I, c.pd, c.cd⟩ ≤ 64) :
    (encodeValue (levelOsNK rd σ Vn c)).size ≤ 68328 := by
  unfold levelOsNK
  dsimp only
  generalize hW : oqsOfNK _ _ _ _ _ _ _ _ = W
  obtain ⟨hl, hw⟩ := oqsOfNK_ok ⟨c.base, c.I, c.pd, c.cd⟩ c.odd c.loop c.walk c.N rd
    (Vn c.fn (c.qargsK.map fun k ↦ (Vn c.lq (c.args.map fun k ↦ σ (.n k))
      (c.rets.map fun k ↦ σ (.n k))) (.n k)) [(Vn c.lq (c.args.map fun k ↦ σ (.n k))
      (c.rets.map fun k ↦ σ (.n k))) (.n (c.pw + 2))]) Vn
  rw [hW] at hl hw
  refine (size_list_le _ (n := 227) (b := 300) (by rw [List.length_map]; omega) ?_).trans
    (by norm_num)
  intro o ho'
  obtain ⟨w, hwW, rfl⟩ := List.mem_map.mp ho'
  obtain ⟨q1, q2, q3⟩ := hw w hwW
  refine size_opening _ ?_ ?_ ?_
  · exact q1.trans_le (Nat.pow_le_pow_right (by norm_num) (by simpa using hpc |>.trans (by norm_num)))
  · show w.2.1.length ≤ 64; rw [q2]; exact hR
  · show (w.2.2 ++ capSibsOf rd _ c.cd _).length ≤ 28
    rw [List.length_append, q3]
    simp [capSibsOf]
    omega

/-- **A child's proof's size**, read off the salted frames by index. -/
theorem size_vsPiOfNK (rd : Reader) (σ : Val) (Vn : NFrames) :
    (encodeValue (vsPiOfNK rd σ Vn VerifySub.cursorLen)).size ≤ 21475247062 := by
  unfold vsPiOfNK
  dsimp only
  generalize logGT (σ (.n 126)) 4 * 11 + logGT (σ (.n 1725)) 11 = j
  generalize Vn _ (VerifySub.vsOsArgsS σ) (VerifySub.vsOsRetsS σ) = fr
  show (MachineValue.constructor 0 [encodeValue (_ : List E), encodeValue (_ : List (List Opening))]).size ≤ _
  simp only [size_ctor, sizeList_cons, sizeList_nil]
  have hs := size_list_le (VerifySub.wordsAt rd (σ (.n 29)) (VerifySub.cursorLen (σ (.n 29)) (σ (.n 683))) ++
      readN rd (fr (.n 9)) (osWordsTab.getD j 0)) (n := 2 ^ 32 + 121) (b := 4)
    (by
      rw [List.length_append]
      simp only [VerifySub.wordsAt, readN, List.length_map, List.length_range]
      have := cursorLen_le (σ (.n 29)) (σ (.n 683)); have := osWordsTab_le j; omega)
    fun x _ ↦ (size_E x).le
  obtain ⟨hr1, hr2⟩ := tab_row j
  have ho := size_list_le ((osCallsTabK.getD j []).map (levelOsNK rd fr Vn)) (n := 6) (b := 68328)
    (by rw [List.length_map]; exact hr1)
    (fun l hl ↦ by
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hl
      obtain ⟨a1, a2, a3, a4⟩ := hr2 c hc
      exact levelOsNK_ok rd fr Vn c a1 a2 a3 a4)
  omega

/-! ## The decoding -/

/-- **The salted decoding's size bound**: about `2^72.9`. -/
def decodingSizeBoundK : ℕ := 8633083319170770143622

theorem size_claims (c : NodeClaims) {n : ℕ} (h : c.xmss.length + c.sphincs.length ≤ n) :
    (encodeValue c).size ≤ 14 * n + 8 := by
  show (MachineValue.constructor 0 [encodeValue c.xmss, encodeValue c.sphincs,
    encodeValue c.daDigest]).size ≤ _
  rw [size_ctor3]
  have a1 := size_list_le c.xmss le_rfl fun x _ ↦ size_xmssClaim x
  have a2 := size_list_le c.sphincs le_rfl fun x _ ↦ size_sphincsClaim x
  have a3 := size_digest c.daDigest
  omega

theorem size_stmt (st : NodeStatement) {n : ℕ}
    (h : st.claims.xmss.length + st.claims.sphincs.length ≤ n)
    (hd : st.deferredClaim.bytecodePoint.length ≤ 23) :
    (encodeValue st).size ≤ 14 * n + 130 := by
  show (MachineValue.constructor 0 [encodeValue st.claims, encodeValue st.deferredClaim]).size ≤ _
  simp only [size_ctor, sizeList_cons, sizeList_nil]
  have a1 := size_claims st.claims h
  have a2 := size_bcClaim st.deferredClaim hd
  omega

theorem size_child (c : Child) (h : c.statement.claims.xmss.length +
      c.statement.claims.sphincs.length ≤ 2 ^ 35 - 2)
    (hd : c.statement.deferredClaim.bytecodePoint.length ≤ 23)
    (hf : c.freshClaim.bytecodePoint.length ≤ 23)
    (hp : (encodeValue c.proof).size ≤ 21475247062) : (encodeValue c).size ≤ 502511584438 := by
  show (MachineValue.constructor 0 [encodeValue c.statement, encodeValue c.freshClaim,
    encodeValue c.proof]).size ≤ _
  rw [size_ctor3]
  have a1 := size_stmt c.statement h hd
  have a2 := size_bcClaim c.freshClaim hf
  omega

theorem size_matrix (m : LeanVM.Da.MatrixWitness) (h1 : m.rows.length ≤ 1024)
    (h2 : ∀ r ∈ m.rows, r.length ≤ 32768) : (encodeValue m).size ≤ 67110914 := by
  show (MachineValue.constructor 0 [encodeValue m.rows]).size ≤ _
  simp only [size_ctor, sizeList_cons, sizeList_nil]
  have := size_list_le m.rows h1 fun r hr ↦ size_list_le r (h2 r hr) fun x _ ↦ (size_K x).le
  omega

theorem size_hints (h : BatchingHints) (hl : h.sumcheckMessages.length ≤ 23) :
    (encodeValue h).size ≤ 236 := by
  show (MachineValue.constructor 0 [encodeValue h.sumcheckMessages,
    encodeValue h.finalBytecodeValue]).size ≤ _
  simp only [size_ctor, sizeList_cons, sizeList_nil, size_E]
  have := size_list_le h.sumcheckMessages hl fun x _ ↦ by rw [size_pair, size_E, size_E]
  omega

theorem dvWitK_ok (σ : Val) (V : End.FrameMap) :
    (Da.dvWitK σ V).rows.length ≤ 1024 ∧ ∀ r ∈ (Da.dvWitK σ V).rows, r.length ≤ 32768 := by
  simp only [Da.dvWitK, LeanVM.Guest.B1.Da.daRows]
  refine ⟨by simp only [List.length_map, List.length_range, Da.dvRowsS]; exact min_le_right _ _,
    fun r hr ↦ ?_⟩
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hr
  refine (length_flatMap_le _ _ (k := 256) fun h _ ↦ ?_).trans (by simp)
  unfold Da.dvSymsPS
  split
  · simp only [Da.dvSymsS, Da.colSymsS, Da.cellSymsOfS, LeanVM.Guest.B1.Da.cellSymsOf,
      List.length_map, List.length_range, le_refl]
  · simp only [List.length_replicate, le_refl]

theorem size_ctor5 (a b c d e : MachineValue) :
    (MachineValue.constructor 0 [a, b, c, d, e]).size = a.size + b.size + c.size + d.size + e.size + 1 := by
  simp only [size_ctor, sizeList_cons, sizeList_nil]
  omega

theorem size_nodeWitness (w : NodeWitness) :
    (encodeValue w).size = (encodeValue w.children).size + (encodeValue w.xmssSignatures).size +
      (encodeValue w.sphincsSignatures).size + (encodeValue w.daMatrix).size +
      (encodeValue w.batchingHints).size + 1 := by
  show (MachineValue.constructor 0 [encodeValue w.children, encodeValue w.xmssSignatures,
    encodeValue w.sphincsSignatures, encodeValue w.daMatrix, encodeValue w.batchingHints]).size = _
  rw [size_ctor5]

theorem size_decoding (d : SeedStatementAndWitness) :
    (encodeValue d).size = (encodeValue d.seed).size + (encodeValue d.statement).size +
      (encodeValue d.witness).size + 1 := by
  show (MachineValue.constructor 0 [encodeValue d.seed, encodeValue d.statement,
    encodeValue d.witness]).size = _
  rw [size_ctor3]

theorem size_daOption (o : Option (DaClaim × LeanVM.Da.MatrixWitness))
    (h : ∀ c m, o = some (c, m) → m.rows.length ≤ 1024 ∧ ∀ row ∈ m.rows, row.length ≤ 32768) :
    (encodeValue o).size ≤ 67110926 := by
  cases o with
  | none =>
    show (MachineValue.constructor 0 []).size ≤ _
    simp [size_ctor, sizeList_nil]
  | some p =>
    obtain ⟨c, m⟩ := p
    show (MachineValue.constructor 1 [encodeValue (c, m)]).size ≤ _
    simp only [size_ctor, sizeList_cons, sizeList_nil]
    rw [size_pair]
    obtain ⟨d1, d2⟩ := h c m rfl
    have := size_daClaim c
    have := size_matrix m d1 d2
    simp only at this ⊢
    omega

theorem decKid_deferred_len (rd : Reader) (σ : Val) (wV : List E → Proof) (c : ℕ) :
    (LeanVM.Guest.B1.Main.decKid rd σ wV c).statement.deferredClaim.bytecodePoint.length ≤ 23 := by
  unfold LeanVM.Guest.B1.Main.decKid LeanVM.Guest.B1.Main.kidStmt
  exact deferOfCells_len _

theorem decKid_fresh_len (rd : Reader) (σ : Val) (wV : List E → Proof) (c : ℕ) :
    (LeanVM.Guest.B1.Main.decKid rd σ wV c).freshClaim.bytecodePoint.length ≤ 23 := by
  unfold LeanVM.Guest.B1.Main.decKid
  exact fixedOfCells_len _

theorem decKid_proof (rd : Reader) (σ : Val) (wV : List E → Proof) (c : ℕ) :
    (LeanVM.Guest.B1.Main.decKid rd σ wV c).proof = wV (LeanVM.Guest.B1.Main.subArgs rd σ c) := by
  unfold LeanVM.Guest.B1.Main.decKid
  rfl

/-- **The witness's size**, its callees' witnesses bounded. -/
theorem size_decWit (σ : Val) (rd : Reader) (wX : List E → LeanXmss.Signature)
    (wS : E → Sphincs.Signature) (wD : List E → List E → LeanVM.Da.MatrixWitness)
    (wV : List E → Proof) (wA : List E → BatchingHints)
    (hV : ∀ a, (encodeValue (wV a)).size ≤ 21475247062)
    (hD : ∀ a r, (wD a r).rows.length ≤ 1024 ∧ ∀ row ∈ (wD a r).rows, row.length ≤ 32768)
    (hA : ∀ a, (wA a).sumcheckMessages.length ≤ 23)
    (hK : ∀ child ∈ (LeanVM.Guest.B1.Main.decWit σ rd wX wS wD wV wA).children,
      child.statement.claims.xmss.length + child.statement.claims.sphincs.length ≤ 2 ^ 35 - 2) :
    (encodeValue (LeanVM.Guest.B1.Main.decWit σ rd wX wS wD wV wA)).size ≤
      8633083318689733806334 := by
  rw [size_nodeWitness]
  generalize hW : LeanVM.Guest.B1.Main.decWit σ rd wX wS wD wV wA = W at hK
  have e1 : W.children = (List.range (LeanVM.Guest.B1.Main.nKids σ)).map
      (LeanVM.Guest.B1.Main.decKid rd σ wV) := by rw [← hW]; rfl
  have e2 : W.xmssSignatures = (List.range (LeanVM.Guest.B1.Main.nRawX σ)).map
      (LeanVM.Guest.B1.Main.rawXmss rd σ wX) := by rw [← hW]; rfl
  have e3 : W.sphincsSignatures = (List.range (LeanVM.Guest.B1.Main.nRawS σ)).map
      (LeanVM.Guest.B1.Main.rawSphincs rd σ wS) := by rw [← hW]; rfl
  have e4 : ∀ c m, W.daMatrix = some (c, m) →
      m = wD [σ (.n 28)] [σ (.n 369), σ (.n 370), σ (.n 371), σ (.n 372)] := by
    intro c m h
    rw [← hW] at h
    simp only [LeanVM.Guest.B1.Main.decWit] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      exact h.2.symm
    · cases h
  have e5 : W.batchingHints = wA [σ (.n 6), σ (.n 384), σ (.n 390), σ (.n 396), σ (.n 417)] := by rw [← hW]; rfl
  have h1 := size_list_le W.children (n := 2 ^ 34) (b := 502511584438)
    (by rw [e1]; simp only [List.length_map, List.length_range, LeanVM.Guest.B1.Main.nKids]
        exact (Main.gLog_lt _).le)
    (fun child hc ↦ by
      have hcl := hK child hc
      rw [e1] at hc
      obtain ⟨c, -, rfl⟩ := List.mem_map.mp hc
      refine size_child _ hcl (decKid_deferred_len _ _ _ _) (decKid_fresh_len _ _ _ _) ?_
      rw [decKid_proof]
      exact hV _)
  have h2 := size_list_le W.xmssSignatures (n := 2 ^ 34) (b := 473)
    (by rw [e2]; simp only [List.length_map, List.length_range, LeanVM.Guest.B1.Main.nRawX]
        exact (Main.gLog_lt _).le)
    (fun x _ ↦ by rw [size_pair]; have := size_xmssClaim x.1; have := size_xmssSig x.2; omega)
  have h3 := size_list_le W.sphincsSignatures (n := 2 ^ 34) (b := 1538)
    (by rw [e3]; simp only [List.length_map, List.length_range, LeanVM.Guest.B1.Main.nRawS]
        exact (Main.gLog_lt _).le)
    (fun x _ ↦ by rw [size_pair]; have := size_sphincsClaim x.1; have := size_sphincsSig x.2; omega)
  have h4 := size_daOption W.daMatrix fun c m h ↦ by rw [e4 c m h]; exact hD _ _
  have h5 := size_hints W.batchingHints (by rw [e5]; exact hA _)
  omega

/-- The salted witness is the deployed `decWit` at the salted readers. -/
theorem decWitK_eq (σ : Val) (rd : Reader) (V : End.FrameMap) :
    Main.decWitK VerifySub.vsPiOfK σ rd V =
      LeanVM.Guest.B1.Main.decWit (Main.mainVal σ) rd
        (fun args => Sig.xmssSigOf (toDV V "__loop2" args []))
        (fun p => Sig.sphincsSigOf (toDV V "verify_sig_lean_sphincs" [p, Main.mainVal σ (.n 47)] [])
          (toDV V))
        (fun args rets => Da.dvWitK (V "da_verify" (args ++ [σ (.n 34)]) rets) V)
        (fun args => VerifySub.vsPiOfK rd (V "verify_sub" args []) V)
        (fun args => Main.aggHintsS rd
          (V "aggregate_claims" ([Main.mainVal σ (.n 26), Main.mainVal σ (.n 27)] ++ args) [])) := by
  unfold Main.decWitK
  rfl

/-- **The salted decoding's size**, at the frame map by name of a frame map by index. -/
theorem size_decK (σ : Val) (rd : Reader) (Vn : NFrames) :
    (encodeValue (Main.decK VerifySub.vsPiOfK σ rd (byName Vn))).size ≤ decodingSizeBoundK := by
  have hkids := Main.decK_child_claims VerifySub.vsPiOfK σ rd (byName Vn)
  rw [size_decoding]
  generalize hDd : Main.decK VerifySub.vsPiOfK σ rd (byName Vn) = D at hkids
  have e1 : D.seed = LeanVM.Guest.B1.Main.decSeed (Main.mainVal σ) := by rw [← hDd]; rfl
  have e2 : D.statement = LeanVM.Guest.B1.Main.decStmt (Main.mainVal σ) rd := by rw [← hDd]; rfl
  have e3 : D.witness = Main.decWitK VerifySub.vsPiOfK σ rd (byName Vn) := by rw [← hDd]; rfl
  have hseed := size_digest D.seed
  have hstmt : (encodeValue D.statement).size ≤ 14 * (2 ^ 34 + 2 ^ 34) + 130 := by
    rw [e2]
    refine size_stmt _ ?_ (deferOfCells_len _)
    simp only [LeanVM.Guest.B1.Main.decStmt, List.length_map, List.length_range]
    have := Main.gLog_lt (Main.mainVal σ (.n 0)); have := Main.gLog_lt (Main.mainVal σ (.n 3))
    omega
  have hwit : (encodeValue D.witness).size ≤ 8633083318689733806334 := by
    rw [e3, decWitK_eq]
    rw [e3, decWitK_eq] at hkids
    apply size_decWit _ _ _ _ _ _ _ _ _ _ hkids
    · intro a
      show (encodeValue (VerifySub.vsPiOfK rd (byName Vn "verify_sub" a []) (byName Vn))).size ≤ _
      rw [← vsPiOfNK_eq]
      exact size_vsPiOfNK _ _ _
    · intro a r
      exact dvWitK_ok _ _
    · intro a
      show (Main.aggHintsS rd _).sumcheckMessages.length ≤ 23
      simp only [Main.aggHintsS, Main.aggRoundsS, List.length_map, List.length_range, le_refl]
  unfold decodingSizeBoundK
  omega

/-! ## The program's output -/

/-- **The compiled top's decoding's size**, on every input. -/
theorem size_decTopK (prog : LeanIsaProgram) (κ : ℕ) (mem : Vector E (2 ^ κ)) :
    (encodeValue (decTopK prog κ mem)).size ≤ decodingSizeBoundK := by
  unfold decTopK decTopTablesK decTopStatesK
  rw [mainValDK_eq, decTopFramesK_eq]
  exact size_decK _ _ _

/-- **On every execution, the salted decoder program outputs its top's decoding**, within its own
size and price. -/
theorem outputWithin_saltedDecoder_any (t : Execution guestProgram) :
    outputWithin saltedDecoder saltedDecoder.size (saltedDecoderPrice t)
        (encodeGuestWitnessDecoderInput guestProgram t) =
      some (encodeValue (decTopK guestProgram t.logMemorySize (memoryVector t.memory))) :=
  outputWithin_decoderEntry le_rfl saltedDecoder_entry guestProgram t
    (decTopKC.costSpec saltedDecoder saltedDecoder_includes guestProgram t.logMemorySize
      (memoryVector t.memory)) le_rfl

/-- **The salted decoder's output's size**: on every execution of the salted guest, the output
within the decoder's size and price is of size at most `decodingSizeBoundK`. -/
theorem saltedDecoder_output_size (t : Execution guestProgram) {output : MachineValue}
    (h : outputWithin saltedDecoder saltedDecoder.size (saltedDecoderPrice t)
      (encodeGuestWitnessDecoderInput guestProgram t) = some output) :
    output.size ≤ decodingSizeBoundK := by
  rw [outputWithin_saltedDecoder_any] at h
  obtain rfl := Option.some.inj h
  exact size_decTopK _ _ _

/-- **The salted decoder's decodings are bounded** (the form of `SaltedGuest.DecodingsBounded`):
on every execution, every decoding its output decodes to has an encoding of size at most
`decodingSizeBoundK`. -/
theorem saltedDecoder_decodings_bounded (t : Execution guestProgram) (output : MachineValue)
    (decoding : SeedStatementAndWitness)
    (h : outputWithin saltedDecoder saltedDecoder.size (saltedDecoderPrice t)
      (encodeGuestWitnessDecoderInput guestProgram t) = some output)
    (hd : decodeDecoded output = some decoding) :
    (encodeValue decoding).size ≤ decodingSizeBoundK := by
  rw [outputWithin_saltedDecoder_any] at h
  obtain rfl := Option.some.inj h
  rw [decodeDecoded_enc] at hd
  obtain rfl := Option.some.inj hd
  exact size_decTopK _ _ _

end

end LeanVM.SaltedGuest.Decoder
