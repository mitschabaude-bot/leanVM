/-
  LeanVM.SaltedGuest.CertName

  The certificate of a guest function by its name.
-/

module

public import LeanVM.SaltedGuest.Glob
public import LeanVM.SaltedGuest.NameIndex
public import LeanVM.SaltedGuest.CheckSound

/-!
# Certificates by name

The located call relation (`Check.RL`) reads a callee's values off its frame through the callee's
certificate, which it finds by the callee's name: `certByName f` is the certificate of the first
function of `coreProgram` named `f` (`certOf (nameIndex f)`, `NameIndex.lean`), and, the names
being distinct (`coreProgram_names_nodup`), `certByName (coreOf j).name = certOf j`
(`certByName_coreOf`).
-/

namespace LeanVM.SaltedGuest

open LeanVM.SaltedGuest LeanVM.Guest

open LeanVM.SaltedGuest.Check LeanVM.Guest.Check

@[expose] public section

/-- The certificate of the function named `f`: `certOf` at its index (`nameIndex`: one past its
position in `coreProgram`, `main` is function `1`). -/
noncomputable def certByName (f : String) : Cert := certOf (nameIndex f)

theorem certByName_coreOf {j : ℕ} (h1 : 1 ≤ j) (h2 : j < nFns) :
    certByName (coreOf j).name = certOf j := by
  have hl : j - 1 < coreProgram.length := by
    have : coreProgram.length = 1538 := coreProgram_length
    simp only [nFns] at h2
    omega
  unfold certByName nameIndex coreOf
  rw [nth_eq hl, findIdx_name_of_nodup coreProgram_names_nodup hl]
  congr 1
  omega

end
end LeanVM.SaltedGuest
