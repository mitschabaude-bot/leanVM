/-
  LeanVM.SaltedGuest.B1.Main.SoundVK

  The salted `main`'s obligation (`End.MainSound`), its witness decoded from the frame map, from
  `verify_sub`'s soundness with its proof named.
-/

module

public import LeanVM.SaltedGuest.B1.Main.FinalK
public import LeanVM.SaltedGuest.EndKnow
public import LeanVM.Guest.B1.Sig.SphincsSound
public import LeanVM.SaltedGuest.Start

/-!
# The salted `main`'s obligation, from `verify_sub`'s

`SubSoundWK piOf`: the salted `verify_sub`'s statement, its proof named by `piOf` (a function of the
memory, its valuation and the frame map): on a memory image of at most `2^32` words, under a call
relation that unfolds at a frame map and lies below the salted core IR's, a run of its body whose
arguments hold the exponent tables and whose seed's cells are memory words `2` and `3`
(`SeedAtWords`, where the salted `level_queries` reads the key's seed) returns nothing, and its proof is accepted by the deferring
verifier with a second public digest, with the IV the seed of its arguments and the keyed hash
under it, for the public input of its arguments (`VerifySubOutK`).

`decK piOf`: the decoding of the salted `main`'s run, `dec` of `End.MainSound`: the deployed
decoders (`decSeed`, `decStmt`, `decWit`) at `mainVal σ`, the salted values read at the deployed
numbers, the node's and the children's counts off the memory (`nodeCountOf`, `childCountsOf`), with
the witnesses read off the frame map: the signatures off the deployed signature
checks' frames (`toDV V`), the matrix off `da_verify`'s (`Da.dvWitK`), a child proof by `piOf` off
`verify_sub`'s, the batching's hints off `aggregate_claims`' (`aggHintsS`). It mentions no hash
and no verifier.

`mainSound_of_sub`: `End.MainSound (decK piOf)` from `SubSoundWK piOf` (`main_sound_CK` with the
callees' contracts: the deployed signature statements through the frame-map transfer, the salted
DA check `Da.da_verify_sound_wK`, `verify_sub` by `SubSoundWK`, `aggregate_claims_valK`).
-/

namespace LeanVM.SaltedGuest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Guest.B1 LeanVM.Guest.B1.Digest
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node LeanVM.Guest.B1.Main LeanVM.SaltedGuest.B1 Recursion.Salted

@[expose] public section

theorem find_verify_subS : SaltedGuest.coreProgram.find? "verify_sub" =
    some LeanVM.SaltedGuest.Data.core18 :=
  Program.find?_of_indexOf? (j := 18) (by decide +kernel) rfl

theorem find_aggregate_claimsS : SaltedGuest.coreProgram.find? "aggregate_claims" =
    some LeanVM.SaltedGuest.Data.core35 :=
  Program.find?_of_indexOf? (j := 35) (by decide +kernel) rfl

/-- **The seed's cells of a `verify_sub` call are memory words `2` and `3`**, where the salted
`level_queries` reads the key's seed. -/
def SeedAtWords (rd : Reader) : List E → Prop
  | [_, _, s0, s1, _, _] => LoadHolds rd 1 2 s0 ∧ LoadHolds rd 1 3 s1
  | _ => False

/-- **The salted `verify_sub`'s statement, its proof named by `piOf`.** -/
def SubSoundWK (piOf : Reader → Val → End.FrameMap → Proof) : Prop :=
  ∀ {κ : ℕ} (L : MemoryImage κ), κ ≤ 32 → ∀ (C : CallRel) (V : End.FrameMap),
    End.UnfoldsV L.read C V → CallRel.Le C (SaltedGuest.coreProgram.Rel L.read) →
    ∀ (σ : Val) (rets : List E),
      Stmt.HoldsList C L.read σ (Fn.body LeanVM.SaltedGuest.Data.core18) False (fun rs ↦ rs = rets) →
      VerifySub.VerifySubPre L.read (LeanVM.SaltedGuest.Data.core18.params.map σ) →
      SeedAtWords L.read (LeanVM.SaltedGuest.Data.core18.params.map σ) →
        rets = [] ∧ VerifySubOutK End.bytecode L.read (LeanVM.SaltedGuest.Data.core18.params.map σ)
          (piOf L.read σ V)

/-- **The salted `main`'s witness, decoded from the frame map `V`.** -/
noncomputable def decWitK (piOf : Reader → Val → End.FrameMap → Proof) (σ : Val) (rd : Reader)
    (V : End.FrameMap) : NodeWitness :=
  decWit (mainVal σ) rd (fun args => Sig.xmssSigOf (toDV V "__loop2" args []))
    (fun p => Sig.sphincsSigOf (toDV V "verify_sig_lean_sphincs" [p, mainVal σ (.n 47)] []) (toDV V))
    (fun args rets => Da.dvWitK (V "da_verify" (args ++ [σ (.n 55)]) rets) V)
    (fun args => piOf rd (V "verify_sub" args []) V)
    (fun args => aggHintsS rd
      (V "aggregate_claims" ([mainVal σ (.n 26), mainVal σ (.n 27)] ++ args) []))

/-- **The decoding of the salted `main`'s run**: the seed, the statement, the node's count, the
witness and the children's counts. -/
noncomputable def decK (piOf : Reader → Val → End.FrameMap → Proof) (σ : Val) (rd : Reader)
    (V : End.FrameMap) : SaltedDecoding :=
  ⟨decSeed (mainVal σ), decStmt (mainVal σ) rd, nodeCountOf (mainVal σ), decWitK piOf σ rd V,
    childCountsOf rd (mainVal σ)⟩

/-- **The salted `main`'s obligation**, from `verify_sub`'s statement with its proof named. -/
theorem mainSound_of_sub {piOf : Reader → Val → End.FrameMap → Proof} (hv : SubSoundWK piOf) :
    End.MainSound (decK piOf) := by
  intro rd hm C V hV hle D S σ hp0 hp1 hS2 hS3 hb
  obtain ⟨κ, -, hκ, L, rfl⟩ := id hm
  have MF := main_factsK hV hle hm hS2 hS3 hb
  have hVd := unfoldsV_toD hV
  have hseed := MF.seed
  simp only [Prod.ext_iff] at hseed
  have cw : CalleesWCK End.bytecode C L.read (mainVal σ (.n 47)) (σ (.n 55)) S
      (fun args => Sig.xmssSigOf (toDV V "__loop2" args []))
      (fun p => Sig.sphincsSigOf (toDV V "verify_sig_lean_sphincs" [p, mainVal σ (.n 47)] [])
        (toDV V))
      (fun args rets => Da.dvWitK (V "da_verify" (args ++ [σ (.n 55)]) rets) V)
      (fun args => piOf L.read (V "verify_sub" args []) V)
      (fun args => aggHintsS L.read
        (V "aggregate_claims" ([mainVal σ (.n 26), mainVal σ (.n 27)] ++ args) [])) := by
    refine ⟨fun args h => ?_, fun p h hbb => ?_, fun gsq rets h hsq => ?_,
      fun pi0 pi1 s0 s1 gsq out h hexp hl2 hl3 => ?_, fun ncg cpi cfresh ccarried dst h m hm1 hm16 hN => ?_⟩
    · obtain ⟨hp, hbx⟩ := body_ofV hVd find_loop2 h
      exact loop2Out_of_body Sig.verify_lean_xmss_sound_holds hp hbx
    · obtain ⟨hp, hbs⟩ := body_ofV hVd Sig.find_verify_sig_lean_sphincs h
      obtain ⟨-, ho⟩ := Sig.verify_sig_lean_sphincs_sound_holds (toDC C) (toDV V) L hκ hVd _ _ hbs
      rw [Sig.core20_params] at hp
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hp
      obtain ⟨e0, e1⟩ := hp
      rw [e0, e1] at ho
      exact ho hbb
    · obtain ⟨hp, hbd⟩ := body_ofVS hV Da.find_da_verifyS h
      exact Da.da_verify_sound_wK hV hle hm hp hbd hsq MF.keyIs
    · obtain ⟨hp, hbv⟩ := body_ofVS hV find_verify_subS h
      obtain ⟨-, ho⟩ := hv L hκ C V hV hle _ _ hbv (by rw [hp]; exact hexp)
        (by rw [hp]; exact ⟨hl2, hl3⟩)
      rw [hp] at ho
      exact ho
    · obtain ⟨hp, hba⟩ := body_ofVS hV find_aggregate_claimsS h
      have hval := aggregate_claims_valK hle hp hba
      have e : [mainVal σ (.n 26), mainVal σ (.n 27)] ++ [ncg, cpi, cfresh, ccarried, dst] =
          [(digestHalves S).1, (digestHalves S).2, ncg, cpi, cfresh, ccarried, dst] := by
        rw [← hseed.1, ← hseed.2]; rfl
      show ∃ out, _ ∧ _ ∧ ∀ cs, _ → _ → batchFrom (batchingSeed S) cs (aggHintsS L.read
        (V "aggregate_claims" ([mainVal σ (.n 26), mainVal σ (.n 27)] ++
          [ncg, cpi, cfresh, ccarried, dst]) [])) = some _
      rw [e]
      exact (hval S rfl m hm1 hm16 hN).2
  obtain ⟨hdig, hrel, hlen⟩ := main_sound_CK End.bytecode_length hm hV hle hS2 hS3 cw hp0 hp1 hb
  have hs : decSeed (mainVal σ) = S := decSeed_eqK MF
  refine ⟨hs, ?_, ?_, hlen⟩
  · show saltedStatementDigest (decSeed (mainVal σ)) (decStmt (mainVal σ) L.read)
      (nodeCountOf (mainVal σ)) = D
    rw [hs]; exact hdig
  · show SaltedNodeRelation (bytecodeWords guestProgram) (decSeed (mainVal σ))
      (decStmt (mainVal σ) L.read) (nodeCountOf (mainVal σ)) (decWitK piOf σ L.read V)
      (childCountsOf L.read (mainVal σ))
    rw [hs]; exact hrel

end
end LeanVM.SaltedGuest.B1.Main
