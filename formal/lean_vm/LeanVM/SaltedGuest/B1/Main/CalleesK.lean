/-
  LeanVM.SaltedGuest.B1.Main.CalleesK

  What the salted `main` asks of its callees with a witness.
-/

module

public import LeanVM.SaltedGuest.B1.Main.FactsK
public import LeanVM.Salted.Node

/-!
# The salted `main`'s callees' contracts

`CalleesWCK bytecode C rd bb0 key S wX wS wD wV wA`: the deployed `Main.CalleesWC` for the salted
`main`, under the seed `S` and its key `key`: the signature checks are the deployed ones at their
deployed names (`toDC C`); the DA check takes the key and its matrix opens the claim under `S`
(`OpensUnder`); a child proof's check is accepted by the deferring verifier with a second public
digest and the keyed hash (`VerifySubOutK`); the batching runs from the batching's seed call under
`S` (`batchFrom (batchingSeed S)`).
-/

namespace LeanVM.SaltedGuest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Guest.B1 LeanVM.Guest.B1.Digest
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node LeanVM.Guest.B1.Main LeanVM.SaltedGuest.B1 Recursion.Salted

@[expose] public section

/-- **What a salted `verify_sub` call establishes for the proof `π`**: its first four cells hold
a public input and a seed, its sixth argument the child proof's claim on the bytecode, and the
deferring verifier with a second public digest, with the IV the seed, the keyed hash under it and
Keccak-f[1600], accepts `π` for the public input and the seed. -/
def VerifySubOutK (bytecode : List K) (rd : Reader) (args : List E) (π : Proof) : Prop :=
  ∃ pi0 pi1 s0 s1 gsq out, args = [pi0, pi1, s0, s1, gsq, out] ∧
    ∃ (seed pi : Digest) (fresh : BytecodeClaim), (s0, s1) = digestHalves seed ∧
      (pi0, pi1) = digestHalves pi ∧ fresh.bytecodePoint.length = bytecodeVars ∧
      ReadsAt rd out (DeferredClaim.cells fresh) ∧
      Id.run (Recursion.SecondDigest.verifyDeferredWithHash₂ (m := Id) keccakF1600 (keyedHash seed) bytecode
        seed pi seed fresh π) = true

/-- **The salted `main`'s callees' contracts with witness functions**, under the seed `S`. -/
structure CalleesWCK (bytecode : List K) (C : CallRel) (rd : Reader) (bb0 key : E) (S : Digest)
    (wX : List E → LeanXmss.Signature) (wS : E → Sphincs.Signature)
    (wD : List E → List E → LeanVM.Da.MatrixWitness)
    (wV : List E → Proof) (wA : List E → BatchingHints) : Prop where
  /-- A raw leanXMSS iteration, at the deployed name. -/
  xmss : ∀ args, toDC C "__loop2" args [] → Loop2Out (toDC C) rd args (wX args)
  /-- A leanSPHINCS check with the byte table `bb0`, at the deployed name. -/
  sphincs : ∀ p, toDC C "verify_sig_lean_sphincs" [p, bb0] [] →
    Sig.ByteBits rd bb0 → Sig.SphincsOut rd p (wS p)
  /-- The DA check with the exponent table and the key: the matrix `wD [gsq] rets` opens the
  returned claim under `S`. -/
  da : ∀ gsq rets, C "da_verify" [gsq, key] rets → Da.SquaresAt rd gsq →
    ∃ (root : Digest) (z c2 : E), OpensUnder S root z (wD [gsq] rets) ∧ IsInK c2 ∧
      rets = digestCells root ++ [z + y * y * c2, c2 + y * eOfNat 0]
  /-- A child proof's check with the exponent table: the proof `wV args`. -/
  sub : ∀ pi0 pi1 s0 s1 gsq out,
    C "verify_sub" [pi0, pi1, s0, s1, gsq, out] [] → ExpTables rd gsq →
    VerifySubOutK bytecode rd [pi0, pi1, s0, s1, gsq, out] (wV [pi0, pi1, s0, s1, gsq, out])
  /-- The batching from the seed's cells, for `n_children_g = g^m`, `1 ≤ m ≤ 16`, with the hints
  `wA args`. -/
  agg : ∀ ncg cpi cfresh ccarried dst, C "aggregate_claims"
    [(digestHalves S).1, (digestHalves S).2, ncg, cpi, cfresh, ccarried, dst] [] →
    ∀ m, 1 ≤ m → m ≤ 16 → ncg = gen ^ m →
      ∃ out : DeferredClaim, out.bytecodePoint.length = bytecodeVars ∧ ReadsAt rd dst out.cells ∧
        ∀ cs : List ChildClaims, cs.length = m →
          (∀ c (hc : c < cs.length), ChildWordsAt rd cpi cfresh ccarried c cs[c]) →
          batchFrom (batchingSeed S) cs (wA [ncg, cpi, cfresh, ccarried, dst]) = some out

end
end LeanVM.SaltedGuest.B1.Main
