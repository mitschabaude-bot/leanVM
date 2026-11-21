import LeanVM.SaltedGuest.Data.Source
import LeanVM.Guest.Expand
import LeanVM.Guest.Renumber
open LeanVM.Guest LeanVM.Guest.Core

def idx? (b : List Stmt) (p : Stmt → Bool) : Option Nat := b.findIdx? p

def showA : Atom → String
  | .mul (.mk [] 0 d) (.mk [] 0 a) (.mk [] 0 c) => s!"mul {d} {a} {c}"
  | .load (.mk [] 0 d) (.mk [] 0 p) off => s!"load {d} {p} {off}"
  | .const (.mk [] 0 d) _ => s!"const {d}"
  | _ => "?"

/-! Prints, for each salted function named, its key atoms by index (`oqparse.py` reads them). -/

def main (args : List String) : IO Unit := do
  let .ok S := Expand.expandProgram LeanVM.SaltedGuest.Data.guest | IO.println "fail"
  let S := S.map Fn.renumber
  let names := args
  for (f, j) in S.zipIdx do
    if names.contains f.name then
      let b := f.body
      let ci := (idx? b fun s => match s with | .callIf .. => true | _ => false).getD 0
      let atoms := b.zipIdx.filterMap fun (s, i) => match s with
        | .atom a => if i < 20 || i + 3 > ci || (showA a).startsWith "load" then some s!"{i}:{showA a}" else none
        | _ => none
      -- loads from the second window pointer base: any load (_ b (odd+1))
      IO.println s!"{j+1}\t{f.name}\tcallIf={ci}\tlen={b.length}\t{atoms}"
