/-
  LeanVM.SaltedGuest.B1.VerifySub.DispatchS

  The salted `verify_sub`'s dispatch to `open_stacked`, at the keyed hash, and the child proof it
  reads.
-/

module

public import LeanVM.SaltedGuest.B1.Whir.OqSoundK
public import LeanVM.Guest.B1.VerifySub.Dispatch
public import LeanVM.Guest.B1.VerifySub.Proof

/-!
# The salted dispatch to `open_stacked`

* `OsSoundWK C rd S osW`: the deployed `OsSoundW` at `OpenOutWK S` (the run at `keyedHash S`).
* `osSoundWK_of`: the salted witness `vsOsWK` (the frame map's `open_stacked_osWK lvWK`) is sound
  for the seed `S` of memory words `2` and `3` (`open_stacked_sound_wK_lvWK`).
* `vs_dispatchS`: the deployed `vs_dispatch` at the salted values (the size's selector `1725`, the
  rate's `126`, the arguments `vsOsArgsS`, the returns `vsOsRetsS`).
* `vsPiOfK`: the child proof the salted `verify_sub` checks, read off its valuation, the memory and
  the frame map (the deployed `vsPiOf` at the salted values: the cursor from `29` to `683`).
-/

namespace LeanVM.SaltedGuest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub LeanVM.SaltedGuest.B1 LeanVM.SaltedGuest.B1.Whir

@[expose] public section

/-- **The salted `open_stacked`'s calls are sound with the witness `osW`** at the keyed hash of
`S`. -/
def OsSoundWK (C : CallRel) (rd : Reader) (S : Digest) (osW : OsWit) : Prop :=
  ∀ μ r, LeanVM.Guest.B1.Whir.minOpenLog ≤ μ → μ ≤ 30 → 1 ≤ r → r ≤ 4 → ∀ (root : Digest) (fs : List E)
    (target root0 root1 cur : E) (rets : List E), fs.length = 5 →
    (root0, root1) = digestHalves root →
    C (LeanVM.Guest.B1.Whir.openName μ) (LeanVM.Guest.B1.Whir.rateSel r :: fs ++ [target, root0, root1, cur]) rets →
    OpenOutWK S rd μ r root fs target cur rets
      (osW (μ - LeanVM.Guest.B1.Whir.minOpenLog) r (LeanVM.Guest.B1.Whir.rateSel r :: fs ++ [target, root0, root1, cur])
        rets).1
      (osW (μ - LeanVM.Guest.B1.Whir.minOpenLog) r (LeanVM.Guest.B1.Whir.rateSel r :: fs ++ [target, root0, root1, cur])
        rets).2

/-- The salted `open_stacked`'s witness function at the frame map `V`. -/
def vsOsWK (rd : Reader) (V : SaltedGuest.End.FrameMap) : OsWit :=
  fun m r args rets ↦ open_stacked_osWK lvWK rd m r (V (LeanVM.Guest.B1.Whir.openNames.getD m "") args rets) V

/-- **The salted `open_stacked`'s calls are sound** for the seed of memory words `2` and `3`. -/
theorem osSoundWK_of {κ : ℕ} (hκ : κ ≤ 32) {L : MemoryImage κ} {C : CallRel}
    {V : SaltedGuest.End.FrameMap} (hU : SaltedGuest.End.UnfoldsV L.read C V)
    (hLe : CallRel.Le C (SaltedGuest.coreProgram.Rel L.read)) {S : Digest}
    (hS2 : LoadHolds L.read 1 2 (digestHalves S).1) (hS3 : LoadHolds L.read 1 3 (digestHalves S).2) :
    OsSoundWK C L.read S (vsOsWK L.read V) := by
  intro μ r hμ1 hμ2 hr1 hr2 root fs target root0 root1 cur rets hfs hroot hc
  obtain ⟨fn, hfind, hpar, hbody⟩ := hU _ _ _ hc
  exact open_stacked_sound_wK_lvWK hκ L C V hU hLe S hS2 hS3 μ r hμ1 hμ2 hr1 hr2 root fs target
    root0 root1 cur rets fn _ hfs hroot hfind hpar hbody

/-- `open_stacked`'s argument words in the salted `verify_sub`. -/
def vsOsArgsS (σ : Val) : List E :=
  [σ (.n 126), σ (.n 1127), σ (.n 1128), σ (.n 1129), σ (.n 1130), σ (.n 1131), σ (.n 1720),
    σ (.n 334), σ (.n 344), σ (.n 683)]

/-- `open_stacked`'s return words in the salted `verify_sub`. -/
def vsOsRetsS (σ : Val) : List E := [σ (.n 1730), σ (.n 1731), σ (.n 1732), σ (.n 1733), σ (.n 1734)]

/-- **The salted dispatch**: the `match` on `g^(μ - 20)` calls the size's specialization of
`open_stacked` on the rate's selector, whose returns are `OpenOutWK S` at the witness. -/
theorem vs_dispatchS {C : CallRel} {rd : Reader} {σ : Val} {S : Digest} {osW : OsWit}
    (hos : OsSoundWK C rd S osW) {μ r : ℕ} (hμ1 : LeanVM.Guest.B1.Whir.minOpenLog ≤ μ) (hμ2 : μ ≤ 30)
    (hr1 : 1 ≤ r) (hr2 : r ≤ 4)
    (h1725 : σ (.n 1725) = gen ^ (μ - LeanVM.Guest.B1.Whir.minOpenLog)) (h126 : σ (.n 126) = LeanVM.Guest.B1.Whir.rateSel r)
    (hd : ∃ (j : ℕ) (hj : j < vsOpenNames.length), σ (.n 1725) = ofK (addressOfIndex j) ∧
      C vsOpenNames[j] (vsOsArgsS σ) (vsOsRetsS σ))
    {root : Digest} (hroot : (σ (.n 334), σ (.n 344)) = digestHalves root) :
    OpenOutWK S rd μ r root [σ (.n 1127), σ (.n 1128), σ (.n 1129), σ (.n 1130), σ (.n 1131)]
      (σ (.n 1720)) (σ (.n 683)) (vsOsRetsS σ)
      (osW (μ - LeanVM.Guest.B1.Whir.minOpenLog) r (vsOsArgsS σ) (vsOsRetsS σ)).1
      (osW (μ - LeanVM.Guest.B1.Whir.minOpenLog) r (vsOsArgsS σ) (vsOsRetsS σ)).2 := by
  obtain ⟨j, hj, hj1725, hc⟩ := hd
  have hj11 : j < 11 := vsOpenNames_length ▸ hj
  have hjc : j = μ - LeanVM.Guest.B1.Whir.minOpenLog := by
    rw [h1725, gen_pow_eq_ofK] at hj1725
    exact (gen_pow_inj (by omega) (by omega)
      (by rw [gen_pow_eq_ofK, gen_pow_eq_ofK]; exact hj1725.symm))
  have hname : vsOpenNames[j] = LeanVM.Guest.B1.Whir.openName μ := by
    rw [LeanVM.Guest.B1.Whir.openName, List.getD_eq_getElem _ _ (by rw [← vsOpenNames_eq, vsOpenNames_length]; omega)]
    simp only [vsOpenNames_eq, hjc]
  replace hc := (congrArg (fun n ↦ C n _ _) hname).mp hc
  subst hjc
  simp only [vsOsArgsS] at hc ⊢
  rw [h126] at hc ⊢
  exact hos μ r hμ1 hμ2 hr1 hr2 root [σ (.n 1127), σ (.n 1128), σ (.n 1129), σ (.n 1130),
    σ (.n 1131)] (σ (.n 1720)) (σ (.n 334)) (σ (.n 344)) (σ (.n 683)) _ rfl hroot hc

/-- **The child proof the salted `verify_sub` checks**, given `open_stacked`'s witness function
`osW`: the words from the cursor `29` to `683`, then the opening's words and openings. -/
def piOfWS (osW : OsWit) (rd : Reader) (σ : Val) : Proof :=
  let w := osW (dispatchIdx (σ (.n 1725))) (rateOf (σ (.n 126))) (vsOsArgsS σ) (vsOsRetsS σ)
  ⟨wordsAt rd (σ (.n 29)) (cursorLen (σ (.n 29)) (σ (.n 683))) ++ w.1, w.2⟩

/-- **The child proof the salted `verify_sub` checks**, read off its valuation, the memory and the
frame map. -/
def vsPiOfK (rd : Reader) (σ : Val) (V : SaltedGuest.End.FrameMap) : Proof :=
  piOfWS (vsOsWK rd V) rd σ

end
end LeanVM.SaltedGuest.B1.VerifySub
