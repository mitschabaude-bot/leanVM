"""The salted `opening_queries` walk modules: `WalkOqDefs.lean` (the lemmas) and `WalkOqK*.lean`
(the instances), from `WORK/oqinst.json` (`oqparse.py`).

Run from lean_vm/: python3 -I scripts/salted-walks/oqgen.py WORK, WORK the directory holding
`compare.tsv` (`lake env lean --run scripts/salted-walks/Compare.lean WORK`). The modules it
writes are checked by the kernel; they are not trusted.
"""
import sys
from pathlib import Path
LEAN_VM = Path(__file__).resolve().parent.parent.parent
WORK = Path(sys.argv[1])
import json
inst=json.load(open(WORK / 'oqinst.json'))
OUT=str(LEAN_VM / 'LeanVM/SaltedGuest') + '/'
lemmas = r'''/-
  LeanVM.SaltedGuest.WalkOqDefs

  The cut obligations of the salted `opening_queries` and its loops, from the statements of their
  bodies that load the window pointers and pass the walk on.
-/

module

public import LeanVM.SaltedGuest.WalkKnown
public import LeanVM.SaltedGuest.B1.Extract
public import LeanVM.SaltedGuest.KernelRfl

/-!
# `opening_queries`' walk obligations, by statements

The deployed proofs (`QueriesWalk.lean`) read, of each loop's body, the atoms computing and
loading its queries' window pointers (`x·qptrs` and its load, at level `0` twice) and the atoms of
its tail call's argument `x·g`; of a specialization's body, an odd count's first window pointer.
Here they are stated at their indices in the salted core IR (`body[i]? = some (.atom …)`, by the
kernel's `rfl`) with the body's statements before the tail call free of `ret`:

* `loop1_cutsKnownK`: a level-0 loop (`WinWalk2`, two queries an iteration);
* `loop0_cutsKnownK`: a deeper loop (`WinWalk`, one query);
* `main_cutsKnownK`: a specialization (`OqMainWins`).
-/

namespace LeanVM.SaltedGuest.End

open LeanVM.SaltedGuest LeanVM.Guest

open LeanVM.Parameters LeanVM.Semantics LeanVM.SaltedGuest LeanVM.Guest LeanVM.Guest.Core LeanVM.SaltedGuest.Check LeanVM.Guest.Check
open LeanVM.Guest.B1 LeanVM.Guest.Value LeanVM.Protocol.Verifier

@[expose] public section

theorem noRetList_take : ∀ (l : List Stmt) (i : ℕ), Stmt.noRetList l = true →
    Stmt.noRetList (l.take i) = true
  | [], i, _ => by cases i <;> rfl
  | s :: l, 0, _ => rfl
  | s :: l, i + 1, h => by
      simp only [Stmt.noRetList, Bool.and_eq_true] at h
      simp only [List.take_succ_cons, Stmt.noRetList, h.1, noRetList_take l i h.2, Bool.and_self]

theorem noRet_le {body : List Stmt} {i ci : ℕ} (hnr : Stmt.noRetList (body.take ci) = true)
    (hi : i ≤ ci) : Stmt.noRetList (body.take i) = true := by
  have := noRetList_take (body.take ci) i hnr
  rwa [List.take_take, min_eq_left hi] at this

variable {j : ℕ}

/-- **A level-0 loop's cut obligations**, from the atoms of its body. -/
theorem loop1_cutsKnownK {odd d cd a b w1 k2 w2 ci c x : ℕ} (ho : odd < 2) (hc : cd < 64)
    (hlt : walkTag 1 odd d cd < 2 ^ 21) (hltw : winsTag d cd < 2 ^ 21)
    (h0 : (coreOf j).body[0]? = some (.atom (.mul (.n a) (.n 2) (.n 0))))
    (h1 : (coreOf j).body[1]? = some (.atom (.mul (.n b) (.n a) (.n 0))))
    (h2 : (coreOf j).body[2]? = some (.atom (.load (.n w1) (.n b) odd)))
    (h3 : (coreOf j).body[k2]? = some (.atom (.load (.n w2) (.n b) (odd + 1))))
    (hc1 : (coreOf j).body[ci - 2]? = some (.atom (.const (.n c) (word 2 0 0))))
    (hc2 : (coreOf j).body[ci - 1]? = some (.atom (.mul (.n x) (.n 0) (.n c))))
    (hk2 : 2 < k2) (hci : k2 + 2 < ci) (hnr : Stmt.noRetList ((coreOf j).body.take ci) = true)
    (hok : loopOk (certOf j) (walkTag 1 odd d cd) d cd [(w1, 3), (w2, k2 + 1)] x ci = true) :
    CutsKnown j := by
  refine loop_cutsKnown hc hltw hok (fun rd t x N ↦ WinWalk2 rd d cd odd t x N)
    (semRel_w1 ho hc hlt) (fun L σ n hl hw hne v hv hle ↦ ?_) (fun L σ n hle hl hw hne ↦ ?_)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    have p0 := atom_of_take hl (by rcases hv with rfl | rfl <;> simp at hle <;> omega) h0
      (noRet_le hnr (by omega))
    have p1 := atom_of_take hl (by rcases hv with rfl | rfl <;> simp at hle <;> omega) h1
      (noRet_le hnr (by omega))
    simp only [Atom.Holds] at p0 p1
    rcases hv with rfl | rfl
    · have p2 := atom_of_take hl (by simp at hle; omega) h2 (noRet_le hnr (by omega))
      simp only [Atom.Holds] at p2
      rw [p1, p0] at p2
      exact winsAt_of_walk2 hw hne le_rfl (by omega) p2
    · have p3 := atom_of_take hl (by simp at hle; omega) h3 (noRet_le hnr (by omega))
      simp only [Atom.Holds] at p3
      rw [p1, p0] at p3
      exact winsAt_of_walk2 hw hne (by omega) le_rfl p3
  · have q1 := atom_of_take hl (by omega) hc1 (noRet_le hnr (by omega))
    have q2 := atom_of_take hl (by omega) hc2 (noRet_le hnr (by omega))
    simp only [Atom.Holds] at q1 q2
    rw [q2, q1, word_gen]
    exact winWalk2_succ hw hne

/-- **A deeper loop's cut obligations**, from the atoms of its body. -/
theorem loop0_cutsKnownK {d cd a w ci c x : ℕ} (hc : cd < 64)
    (hlt : walkTag 0 0 d cd < 2 ^ 21) (hltw : winsTag d cd < 2 ^ 21)
    (h0 : (coreOf j).body[0]? = some (.atom (.mul (.n a) (.n 2) (.n 0))))
    (h1 : (coreOf j).body[1]? = some (.atom (.load (.n w) (.n a) 0)))
    (hc1 : (coreOf j).body[ci - 2]? = some (.atom (.const (.n c) (word 2 0 0))))
    (hc2 : (coreOf j).body[ci - 1]? = some (.atom (.mul (.n x) (.n 0) (.n c))))
    (hci : 3 < ci) (hnr : Stmt.noRetList ((coreOf j).body.take ci) = true)
    (hok : loopOk (certOf j) (walkTag 0 0 d cd) d cd [(w, 2)] x ci = true) :
    CutsKnown j := by
  refine loop_cutsKnown hc hltw hok (fun rd t x N ↦ WinWalk rd d cd t x N)
    (semRel_w0 hc hlt) (fun L σ n hl hw hne v hv hle ↦ ?_) (fun L σ n hle hl hw hne ↦ ?_)
  · simp only [List.mem_singleton] at hv
    subst hv
    have p0 := atom_of_take hl (by simp at hle; omega) h0 (noRet_le hnr (by omega))
    have p1 := atom_of_take hl (by simp at hle; omega) h1 (noRet_le hnr (by omega))
    simp only [Atom.Holds] at p0 p1
    rw [p0] at p1
    exact winsAt_of_walk hw hne p1
  · have q1 := atom_of_take hl (by omega) hc1 (noRet_le hnr (by omega))
    have q2 := atom_of_take hl (by omega) hc2 (noRet_le hnr (by omega))
    simp only [Atom.Holds] at q1 q2
    rw [q2, q1, word_gen]
    exact winWalk_succ hw hne

/-- **A specialization's cut obligations**, an odd count's first window pointer loaded at `i`. -/
theorem main_cutsKnownK1 {d cd base i w : ℕ} (hc : cd < 64) (hbase : base = 1)
    (hlt : walkTag (2 + base) 1 d cd < tagGkr)
    (hltW : walkTag (if base = 1 then 1 else 0) 1 d cd < 2 ^ 21)
    (hltw : winsTag d cd < 2 ^ 21)
    (hld : (coreOf j).body[i]? = some (.atom (.load (.n w) (.n 4) 0)))
    (hnr : Stmt.noRetList ((coreOf j).body.take i) = true)
    (hok : mainOk (certOf j) (walkTag (2 + base) 1 d cd) (walkTag (if base = 1 then 1 else 0) 1 d cd)
      d cd [(w, i + 1)] = true) :
    CutsKnown j :=
  main_cutsKnownG (by decide) (fun _ ↦ hbase) hc (by omega) hlt hltW hltw hok
    fun L σ n hl hW v hv hle ↦ by
      simp only [List.mem_singleton] at hv
      subst hv
      have p := atom_of_take hl (by simp at hle; omega) hld hnr
      exact hW.1 rfl _ p

/-- **A specialization's cut obligations**, an even count. -/
theorem main_cutsKnownK0 {d cd base : ℕ} (hc : cd < 64) (hbase : base < 2)
    (hlt : walkTag (2 + base) 0 d cd < tagGkr)
    (hltW : walkTag (if base = 1 then 1 else 0) 0 d cd < 2 ^ 21)
    (hltw : winsTag d cd < 2 ^ 21)
    (hok : mainOk (certOf j) (walkTag (2 + base) 0 d cd) (walkTag (if base = 1 then 1 else 0) 0 d cd)
      d cd [] = true) :
    CutsKnown j :=
  main_cutsKnownG (by decide) (fun h ↦ absurd h (by decide)) hc hbase hlt hltW hltw hok
    fun _ _ _ _ _ _ hv _ ↦ absurd hv (by simp)

end
end LeanVM.SaltedGuest.End
'''
open(OUT+'WalkOqDefs.lean','w').write(lemmas)
def hdr(k):
    return f'''/-
  LeanVM.SaltedGuest.WalkOqK{k}

  Generated by `scripts/salted-walks/oqgen.py`; do not edit.
  The cut obligations of a part of the salted `opening_queries`' specializations and loops.
-/

module

public import LeanVM.SaltedGuest.WalkOqDefs

namespace LeanVM.SaltedGuest.End

open LeanVM.SaltedGuest LeanVM.Guest

open LeanVM.Parameters LeanVM.Semantics LeanVM.SaltedGuest LeanVM.Guest LeanVM.Guest.Core LeanVM.SaltedGuest.Check LeanVM.Guest.Check

@[expose] public section

set_option maxRecDepth 100000

'''
def item(d):
    j=d['js']; D=d['pd']+d['cd']; cd=d['cd']; n=d['name']
    if d['kind']=='mainOkS':
        if d['odd']==1:
            i,w=d['load']
            return f'''kernel_rfl oq_ld{j} : (coreOf {j}).body[{i}]? = some (.atom (.load (.n {w}) (.n 4) 0))

/-- `{n}`. -/
theorem walk_{j} : CutsKnown {j} :=
  main_cutsKnownK1 (j := {j}) (d := {D}) (cd := {cd}) (base := {d['base']}) (by decide) rfl (by decide)
    (by decide) (by decide) oq_ld{j} (by decide +kernel) (by decide +kernel)

'''
        return f'''/-- `{n}`. -/
theorem walk_{j} : CutsKnown {j} :=
  main_cutsKnownK0 (j := {j}) (d := {D}) (cd := {cd}) (base := {d['base']}) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)

'''
    ci,c,x=d['tail']
    tails=f'''kernel_rfl oq_c{j} : (coreOf {j}).body[{ci-2}]? = some (.atom (.const (.n {c}) (word 2 0 0)))

kernel_rfl oq_x{j} : (coreOf {j}).body[{ci-1}]? = some (.atom (.mul (.n {x}) (.n 0) (.n {c})))

'''
    if d['kind']=='loop1Ok':
        a,b,w1,k2,w2=d['atoms']; o=d['odd']
        return f'''kernel_rfl oq_a{j} : (coreOf {j}).body[0]? = some (.atom (.mul (.n {a}) (.n 2) (.n 0)))

kernel_rfl oq_b{j} : (coreOf {j}).body[1]? = some (.atom (.mul (.n {b}) (.n {a}) (.n 0)))

kernel_rfl oq_w{j} : (coreOf {j}).body[2]? = some (.atom (.load (.n {w1}) (.n {b}) {o}))

kernel_rfl oq_v{j} : (coreOf {j}).body[{k2}]? = some (.atom (.load (.n {w2}) (.n {b}) ({o} + 1)))

{tails}/-- `{n}`. -/
theorem walk_{j} : CutsKnown {j} :=
  loop1_cutsKnownK (j := {j}) (d := {D}) (cd := {cd}) (ci := {ci}) (c := {c}) (x := {x}) (by decide) (by decide) (by decide) (by decide)
    oq_a{j} oq_b{j} oq_w{j} oq_v{j} oq_c{j} oq_x{j} (by decide) (by decide) (by decide +kernel)
    (by decide +kernel)

'''
    a,w=d['atoms']
    return f'''kernel_rfl oq_a{j} : (coreOf {j}).body[0]? = some (.atom (.mul (.n {a}) (.n 2) (.n 0)))

kernel_rfl oq_w{j} : (coreOf {j}).body[1]? = some (.atom (.load (.n {w}) (.n {a}) 0))

{tails}/-- `{n}`. -/
theorem walk_{j} : CutsKnown {j} :=
  loop0_cutsKnownK (j := {j}) (d := {D}) (cd := {cd}) (ci := {ci}) (c := {c}) (x := {x}) (by decide) (by decide) (by decide)
    oq_a{j} oq_w{j} oq_c{j} oq_x{j} (by decide) (by decide +kernel) (by decide +kernel)

'''
chunks=[inst[i:i+22] for i in range(0,len(inst),22)]
for k,ch in enumerate(chunks):
    open(OUT+f'WalkOqK{k}.lean','w').write(hdr(k)+''.join(item(d) for d in ch)+'end\nend LeanVM.SaltedGuest.End\n')
print(len(chunks))
