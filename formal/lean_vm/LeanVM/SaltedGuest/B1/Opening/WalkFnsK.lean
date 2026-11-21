/-
  LeanVM.SaltedGuest.B1.Opening.WalkFnsK

  Every salted `walk_path` specialization is its keyed template (`WalkFnK`), so a sound walk under
  the key.
-/

module

public import LeanVM.SaltedGuest.B1.Opening.WalkK
public import LeanVM.SaltedGuest.B1.Merkle.CapAll

/-!
# The salted `walk_path` specializations

Each body is `wpBodyK` by the kernel's `rfl`; `walkSoundK_all`: every specialization of
`walkPathNames` is `WalkSoundK`.
-/

namespace LeanVM.SaltedGuest.B1

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.B1

@[expose] public section

set_option maxRecDepth 100000

kernel_rfl wp_idx1536 : SaltedGuest.coreProgram[1536]? = some LeanVM.SaltedGuest.Data.core1536

kernel_rfl wp_body1536 : LeanVM.SaltedGuest.Data.core1536.body = wpBodyK ⟨0, 0, 6, 6⟩

/-- `walk_path__L6_L6` is its keyed template. -/
theorem wpFnK_1536 : WalkFnK "walk_path__L6_L6" 6 6 :=
  ⟨_, find_of_getElem? wp_idx1536, rfl, wp_body1536⟩

kernel_rfl wp_idx1535 : SaltedGuest.coreProgram[1535]? = some LeanVM.SaltedGuest.Data.core1535

kernel_rfl wp_body1535 : LeanVM.SaltedGuest.Data.core1535.body = wpBodyK ⟨0, 0, 6, 7⟩

/-- `walk_path__L6_L7` is its keyed template. -/
theorem wpFnK_1535 : WalkFnK "walk_path__L6_L7" 6 7 :=
  ⟨_, find_of_getElem? wp_idx1535, rfl, wp_body1535⟩

kernel_rfl wp_idx1534 : SaltedGuest.coreProgram[1534]? = some LeanVM.SaltedGuest.Data.core1534

kernel_rfl wp_body1534 : LeanVM.SaltedGuest.Data.core1534.body = wpBodyK ⟨0, 0, 12, 2⟩

/-- `walk_path__L12_L2` is its keyed template. -/
theorem wpFnK_1534 : WalkFnK "walk_path__L12_L2" 12 2 :=
  ⟨_, find_of_getElem? wp_idx1534, rfl, wp_body1534⟩

kernel_rfl wp_idx1441 : SaltedGuest.coreProgram[1441]? = some LeanVM.SaltedGuest.Data.core1441

kernel_rfl wp_body1441 : LeanVM.SaltedGuest.Data.core1441.body = wpBodyK ⟨0, 0, 12, 3⟩

/-- `walk_path__L12_L3` is its keyed template. -/
theorem wpFnK_1441 : WalkFnK "walk_path__L12_L3" 12 3 :=
  ⟨_, find_of_getElem? wp_idx1441, rfl, wp_body1441⟩

kernel_rfl wp_idx1461 : SaltedGuest.coreProgram[1461]? = some LeanVM.SaltedGuest.Data.core1461

kernel_rfl wp_body1461 : LeanVM.SaltedGuest.Data.core1461.body = wpBodyK ⟨0, 0, 12, 4⟩

/-- `walk_path__L12_L4` is its keyed template. -/
theorem wpFnK_1461 : WalkFnK "walk_path__L12_L4" 12 4 :=
  ⟨_, find_of_getElem? wp_idx1461, rfl, wp_body1461⟩

kernel_rfl wp_idx1444 : SaltedGuest.coreProgram[1444]? = some LeanVM.SaltedGuest.Data.core1444

kernel_rfl wp_body1444 : LeanVM.SaltedGuest.Data.core1444.body = wpBodyK ⟨0, 0, 12, 5⟩

/-- `walk_path__L12_L5` is its keyed template. -/
theorem wpFnK_1444 : WalkFnK "walk_path__L12_L5" 12 5 :=
  ⟨_, find_of_getElem? wp_idx1444, rfl, wp_body1444⟩

kernel_rfl wp_idx1464 : SaltedGuest.coreProgram[1464]? = some LeanVM.SaltedGuest.Data.core1464

kernel_rfl wp_body1464 : LeanVM.SaltedGuest.Data.core1464.body = wpBodyK ⟨0, 0, 12, 6⟩

/-- `walk_path__L12_L6` is its keyed template. -/
theorem wpFnK_1464 : WalkFnK "walk_path__L12_L6" 12 6 :=
  ⟨_, find_of_getElem? wp_idx1464, rfl, wp_body1464⟩

kernel_rfl wp_idx1473 : SaltedGuest.coreProgram[1473]? = some LeanVM.SaltedGuest.Data.core1473

kernel_rfl wp_body1473 : LeanVM.SaltedGuest.Data.core1473.body = wpBodyK ⟨0, 0, 12, 7⟩

/-- `walk_path__L12_L7` is its keyed template. -/
theorem wpFnK_1473 : WalkFnK "walk_path__L12_L7" 12 7 :=
  ⟨_, find_of_getElem? wp_idx1473, rfl, wp_body1473⟩

kernel_rfl wp_idx1537 : SaltedGuest.coreProgram[1537]? = some LeanVM.SaltedGuest.Data.core1537

kernel_rfl wp_body1537 : LeanVM.SaltedGuest.Data.core1537.body = wpBodyK ⟨0, 0, 12, 8⟩

/-- `walk_path__L12_L8` is its keyed template. -/
theorem wpFnK_1537 : WalkFnK "walk_path__L12_L8" 12 8 :=
  ⟨_, find_of_getElem? wp_idx1537, rfl, wp_body1537⟩

kernel_rfl wp_idx1482 : SaltedGuest.coreProgram[1482]? = some LeanVM.SaltedGuest.Data.core1482

kernel_rfl wp_body1482 : LeanVM.SaltedGuest.Data.core1482.body = wpBodyK ⟨0, 0, 18, 2⟩

/-- `walk_path__L18_L2` is its keyed template. -/
theorem wpFnK_1482 : WalkFnK "walk_path__L18_L2" 18 2 :=
  ⟨_, find_of_getElem? wp_idx1482, rfl, wp_body1482⟩

kernel_rfl wp_idx1491 : SaltedGuest.coreProgram[1491]? = some LeanVM.SaltedGuest.Data.core1491

kernel_rfl wp_body1491 : LeanVM.SaltedGuest.Data.core1491.body = wpBodyK ⟨0, 0, 18, 3⟩

/-- `walk_path__L18_L3` is its keyed template. -/
theorem wpFnK_1491 : WalkFnK "walk_path__L18_L3" 18 3 :=
  ⟨_, find_of_getElem? wp_idx1491, rfl, wp_body1491⟩

kernel_rfl wp_idx1499 : SaltedGuest.coreProgram[1499]? = some LeanVM.SaltedGuest.Data.core1499

kernel_rfl wp_body1499 : LeanVM.SaltedGuest.Data.core1499.body = wpBodyK ⟨0, 0, 18, 4⟩

/-- `walk_path__L18_L4` is its keyed template. -/
theorem wpFnK_1499 : WalkFnK "walk_path__L18_L4" 18 4 :=
  ⟨_, find_of_getElem? wp_idx1499, rfl, wp_body1499⟩

kernel_rfl wp_idx1505 : SaltedGuest.coreProgram[1505]? = some LeanVM.SaltedGuest.Data.core1505

kernel_rfl wp_body1505 : LeanVM.SaltedGuest.Data.core1505.body = wpBodyK ⟨0, 0, 18, 5⟩

/-- `walk_path__L18_L5` is its keyed template. -/
theorem wpFnK_1505 : WalkFnK "walk_path__L18_L5" 18 5 :=
  ⟨_, find_of_getElem? wp_idx1505, rfl, wp_body1505⟩

kernel_rfl wp_idx1511 : SaltedGuest.coreProgram[1511]? = some LeanVM.SaltedGuest.Data.core1511

kernel_rfl wp_body1511 : LeanVM.SaltedGuest.Data.core1511.body = wpBodyK ⟨0, 0, 18, 6⟩

/-- `walk_path__L18_L6` is its keyed template. -/
theorem wpFnK_1511 : WalkFnK "walk_path__L18_L6" 18 6 :=
  ⟨_, find_of_getElem? wp_idx1511, rfl, wp_body1511⟩

kernel_rfl wp_idx1517 : SaltedGuest.coreProgram[1517]? = some LeanVM.SaltedGuest.Data.core1517

kernel_rfl wp_body1517 : LeanVM.SaltedGuest.Data.core1517.body = wpBodyK ⟨0, 0, 18, 7⟩

/-- `walk_path__L18_L7` is its keyed template. -/
theorem wpFnK_1517 : WalkFnK "walk_path__L18_L7" 18 7 :=
  ⟨_, find_of_getElem? wp_idx1517, rfl, wp_body1517⟩

kernel_rfl wp_idx1523 : SaltedGuest.coreProgram[1523]? = some LeanVM.SaltedGuest.Data.core1523

kernel_rfl wp_body1523 : LeanVM.SaltedGuest.Data.core1523.body = wpBodyK ⟨0, 0, 24, 2⟩

/-- `walk_path__L24_L2` is its keyed template. -/
theorem wpFnK_1523 : WalkFnK "walk_path__L24_L2" 24 2 :=
  ⟨_, find_of_getElem? wp_idx1523, rfl, wp_body1523⟩

kernel_rfl wp_idx1525 : SaltedGuest.coreProgram[1525]? = some LeanVM.SaltedGuest.Data.core1525

kernel_rfl wp_body1525 : LeanVM.SaltedGuest.Data.core1525.body = wpBodyK ⟨0, 0, 24, 3⟩

/-- `walk_path__L24_L3` is its keyed template. -/
theorem wpFnK_1525 : WalkFnK "walk_path__L24_L3" 24 3 :=
  ⟨_, find_of_getElem? wp_idx1525, rfl, wp_body1525⟩

kernel_rfl wp_idx1530 : SaltedGuest.coreProgram[1530]? = some LeanVM.SaltedGuest.Data.core1530

kernel_rfl wp_body1530 : LeanVM.SaltedGuest.Data.core1530.body = wpBodyK ⟨0, 0, 24, 4⟩

/-- `walk_path__L24_L4` is its keyed template. -/
theorem wpFnK_1530 : WalkFnK "walk_path__L24_L4" 24 4 :=
  ⟨_, find_of_getElem? wp_idx1530, rfl, wp_body1530⟩

/-- **Every salted `walk_path` specialization is a sound walk under the key.** -/
theorem walkSoundK_all : ∀ p ∈ walkPathNames, WalkSoundK p.2.2 p.1 p.2.1 := by
  intro p hp
  simp only [walkPathNames, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (wpFnK_1536).sound (by norm_num)
  · exact (wpFnK_1535).sound (by norm_num)
  · exact (wpFnK_1534).sound (by norm_num)
  · exact (wpFnK_1441).sound (by norm_num)
  · exact (wpFnK_1461).sound (by norm_num)
  · exact (wpFnK_1444).sound (by norm_num)
  · exact (wpFnK_1464).sound (by norm_num)
  · exact (wpFnK_1473).sound (by norm_num)
  · exact (wpFnK_1537).sound (by norm_num)
  · exact (wpFnK_1482).sound (by norm_num)
  · exact (wpFnK_1491).sound (by norm_num)
  · exact (wpFnK_1499).sound (by norm_num)
  · exact (wpFnK_1505).sound (by norm_num)
  · exact (wpFnK_1511).sound (by norm_num)
  · exact (wpFnK_1517).sound (by norm_num)
  · exact (wpFnK_1523).sound (by norm_num)
  · exact (wpFnK_1525).sound (by norm_num)
  · exact (wpFnK_1530).sound (by norm_num)

end
end LeanVM.SaltedGuest.B1
