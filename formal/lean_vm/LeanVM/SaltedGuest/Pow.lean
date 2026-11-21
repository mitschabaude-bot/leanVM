/-
  LeanVM.SaltedGuest.Pow

  The powers of `g` the salted guest's certificates cite: `LeanVM.Guest.Pow` with the salted
  certificates' power table.
-/

module

public import LeanVM.Guest.Pow
public import LeanVM.SaltedGuest.Data.Pows

/-!
# The salted guest's powers

`LeanVM.Guest.Pow` is generic: its words `g^(d·16^w)` come from a table of powers of `g`
(`Data.gtab`) that is the same for both guests. The powers the salted certificates cite are the
salted `Data.powTree` (`LeanVM/SaltedGuest/Data/Pows.lean`); modules of the salted guest import
this module where the deployed guest's import `LeanVM.Guest.Pow`, and read `Data.powTree` as the
salted one, inside `LeanVM.SaltedGuest`.
-/
