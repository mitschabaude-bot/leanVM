/-
  LeanVM.SaltedGuest.B1.Merkle.CapAll

  The salted `verify_merkle_cap` at the seven cap depths its callers reach, soundly.
-/

module

public import LeanVM.SaltedGuest.B1.Merkle.Cap
public import LeanVM.SaltedGuest.KernelRfl

/-!
# `verify_merkle_cap`, every deployed depth

The specializations `verify_merkle_cap__L{D}`, `D = 2 .. 8`, are functions `991, 979, 981, 983,
985, 1000, 1193` of the salted core IR; each body is `mcBodyS (2^D)` by the kernel's `rfl`.
`verify_merkle_cap_sound_holds`: their relations give `MeaningCapK`.
-/

namespace LeanVM.SaltedGuest.B1

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.B1

@[expose] public section

/-- A function of the salted core IR is found by its name. -/
theorem find_of_getElem? {j : ℕ} {f : Fn} (h : SaltedGuest.coreProgram[j]? = some f) :
    SaltedGuest.coreProgram.find? f.name = some f := by
  obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.mp h
  exact SaltedGuest.coreProgram_find_getElem hj

set_option maxRecDepth 100000

kernel_rfl mc_idx991 : SaltedGuest.coreProgram[991]? = some LeanVM.SaltedGuest.Data.core991
kernel_rfl mc_idx979 : SaltedGuest.coreProgram[979]? = some LeanVM.SaltedGuest.Data.core979
kernel_rfl mc_idx981 : SaltedGuest.coreProgram[981]? = some LeanVM.SaltedGuest.Data.core981
kernel_rfl mc_idx983 : SaltedGuest.coreProgram[983]? = some LeanVM.SaltedGuest.Data.core983
kernel_rfl mc_idx985 : SaltedGuest.coreProgram[985]? = some LeanVM.SaltedGuest.Data.core985
kernel_rfl mc_idx1000 : SaltedGuest.coreProgram[1000]? = some LeanVM.SaltedGuest.Data.core1000
kernel_rfl mc_idx1193 : SaltedGuest.coreProgram[1193]? = some LeanVM.SaltedGuest.Data.core1193

kernel_rfl mc_body991 : LeanVM.SaltedGuest.Data.core991.body = mcBodyS 4
kernel_rfl mc_body979 : LeanVM.SaltedGuest.Data.core979.body = mcBodyS 8
kernel_rfl mc_body981 : LeanVM.SaltedGuest.Data.core981.body = mcBodyS 16
kernel_rfl mc_body983 : LeanVM.SaltedGuest.Data.core983.body = mcBodyS 32
kernel_rfl mc_body985 : LeanVM.SaltedGuest.Data.core985.body = mcBodyS 64
kernel_rfl mc_body1000 : LeanVM.SaltedGuest.Data.core1000.body = mcBodyS 128
kernel_rfl mc_body1193 : LeanVM.SaltedGuest.Data.core1193.body = mcBodyS 256

/-- **The salted `verify_merkle_cap`, soundly**, at the seven deployed depths. -/
theorem verify_merkle_cap_sound_holds : verify_merkle_cap_sound_Spec := by
  intro p hp rd args rets
  simp only [merkleCapNames, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact merkle_cap_soundL 4 (by norm_num) (find_of_getElem? mc_idx991) rfl mc_body991 rd args rets
  · exact merkle_cap_soundL 8 (by norm_num) (find_of_getElem? mc_idx979) rfl mc_body979 rd args rets
  · exact merkle_cap_soundL 16 (by norm_num) (find_of_getElem? mc_idx981) rfl mc_body981 rd args
      rets
  · exact merkle_cap_soundL 32 (by norm_num) (find_of_getElem? mc_idx983) rfl mc_body983 rd args
      rets
  · exact merkle_cap_soundL 64 (by norm_num) (find_of_getElem? mc_idx985) rfl mc_body985 rd args
      rets
  · exact merkle_cap_soundL 128 (by norm_num) (find_of_getElem? mc_idx1000) rfl mc_body1000 rd
      args rets
  · exact merkle_cap_soundL 256 (by norm_num) (find_of_getElem? mc_idx1193) rfl mc_body1193 rd
      args rets

end
end LeanVM.SaltedGuest.B1
