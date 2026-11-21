import LeanVM.Guest.Data.Source
import LeanVM.SaltedGuest.Data.Source
import LeanVM.Guest.Expand
import LeanVM.Guest.Renumber
open LeanVM.Guest LeanVM.Guest.Core

partial def callsS : Stmt → List String
  | .atom _ => []
  | .ite _ z n => (z.flatMap callsS) ++ (n.flatMap callsS)
  | .match_ _ arms => arms.flatMap (·.flatMap callsS)
  | .call f _ _ => [f]
  | .callIf _ f _ => [f]
  | .dispatch _ fs _ _ => fs
  | .ret _ => []

partial def mapS (ρ : String → String) : Stmt → Stmt
  | .atom a => .atom a
  | .ite c z n => .ite c (z.map (mapS ρ)) (n.map (mapS ρ))
  | .match_ x arms => .match_ x (arms.map (·.map (mapS ρ)))
  | .call f a r => .call (ρ f) a r
  | .callIf c f a => .callIf c (ρ f) a
  | .dispatch x fs a r => .dispatch x (fs.map ρ) a r
  | .ret v => .ret v

/-! Pairs the salted guest's core IR functions with the deployed guest's by canonical name (loop helpers
by their first caller and order); writes `WORK/compare.tsv` (salted index, deployed index, `SAME` or
`DIFF`, name, canonical name). Run from lean_vm/: `lake env lean --run scripts/salted-walks/Compare.lean WORK`. -/

def main (args : List String) : IO Unit := do
  let work : System.FilePath := args.headD "."
  let .ok D := Expand.expandProgram Data.guest | IO.println "fail D"
  let .ok S := Expand.expandProgram LeanVM.SaltedGuest.Data.guest | IO.println "fail S"
  let D := D.map Fn.renumber
  let S := S.map Fn.renumber
  IO.println s!"D {D.length} S {S.length}"
  -- canonical names: loop helpers named by first caller and order
  let canon (P : Program) : Std.HashMap String String := Id.run do
    let mut m : Std.HashMap String String := {}
    for f in P do
      if !f.name.startsWith "__loop" then m := m.insert f.name f.name
    let mut changed := true
    while changed do
      changed := false
      for f in P do
        if let some cn := m[f.name]? then
          let cs := (f.body.flatMap callsS).eraseDups.filter (·.startsWith "__loop")
          for (c, k) in cs.zipIdx do
            if !m.contains c then
              m := m.insert c s!"{cn}#L{k}"
              changed := true
    return m
  let mD := canon D
  let mS := canon S
  let ρD := fun n => mD.getD n n
  let ρS := fun n => mS.getD n n
  let dByC : Std.HashMap String (Nat × Fn) := Id.run do
    let mut h := {}
    for (f, j) in D.zipIdx do h := h.insert (ρD f.name) (j, {f with name := ρD f.name, body := f.body.map (mapS ρD)})
    return h
  let mut same := 0
  let mut out : Array String := #[]
  for (f, j) in S.zipIdx do
    let c := ρS f.name
    let fS : Fn := {f with name := c, body := f.body.map (mapS ρS)}
    match dByC[c]? with
    | none => out := out.push s!"{j}\t-\tNEW\t{f.name}\t{c}"
    | some (jd, fD) =>
      if fS == fD then
        same := same + 1
        out := out.push s!"{j}\t{jd}\tSAME\t{f.name}\t{c}"
      else out := out.push s!"{j}\t{jd}\tDIFF\t{f.name}\t{c}"
  IO.println s!"same {same}"
  IO.FS.writeFile (work / "compare.tsv") ("\n".intercalate out.toList ++ "\n")
