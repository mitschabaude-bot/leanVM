/-
  LeanVM.SaltedGuest.WalkKnownAll

  The salted guest's walks' obligations, proved.
-/

module

public import LeanVM.SaltedGuest.WalkGkrK
public import LeanVM.SaltedGuest.WalkLqK0
public import LeanVM.SaltedGuest.WalkLqK1
public import LeanVM.SaltedGuest.WalkLqK2
public import LeanVM.SaltedGuest.WalkOqK0
public import LeanVM.SaltedGuest.WalkOqK1
public import LeanVM.SaltedGuest.WalkOqK2
public import LeanVM.SaltedGuest.WalkOqK3
public import LeanVM.SaltedGuest.WalkOsK
public import LeanVM.SaltedGuest.WalkWpK

/-!
# `WalkKnown`, proved

`walkKnown_proved : WalkKnown`: the cut obligations (`CutsKnown`) of every function of the salted
`Checked.oblFns` but `main` (`1`) and `verify_sub` (`19`): `level_queries`' specializations
(`WalkLqK*.lean`), `walk_path`'s (`WalkWpK.lean`), `open_stacked`'s (`WalkOsK.lean`),
`opening_queries`' and their loops (`WalkOqK*.lean`), `verify_bus_gkr` (`10`) and its layer loop
`__loop6` (`92`, `WalkGkrK.lean`).
-/

namespace LeanVM.SaltedGuest.End

@[expose] public section

set_option maxRecDepth 4000 in
/-- **The walks' obligations, proved.** -/
theorem walkKnown_proved : WalkKnown := by
  -- One conjunct per function of `Checked.oblFns`, in order.
  have key : List.Forall (fun j ↦ j ≠ 1 → j ≠ 19 → CutsKnown j) Checked.oblFns :=
    ⟨fun h _ ↦ absurd rfl h, fun _ _ ↦ gkrBus_cutsKnown, fun _ h ↦ absurd rfl h,
      fun _ _ ↦ gkrLoop_cutsKnown, fun _ _ ↦ walk_310, fun _ _ ↦ walk_311, fun _ _ ↦ walk_312,
      fun _ _ ↦ walk_313, fun _ _ ↦ walk_314, fun _ _ ↦ walk_315, fun _ _ ↦ walk_316,
      fun _ _ ↦ walk_317, fun _ _ ↦ walk_318, fun _ _ ↦ walk_319, fun _ _ ↦ walk_320,
      fun _ _ ↦ walk_427, fun _ _ ↦ walk_428, fun _ _ ↦ walk_429, fun _ _ ↦ walk_430,
      fun _ _ ↦ walk_437, fun _ _ ↦ walk_438, fun _ _ ↦ walk_439, fun _ _ ↦ walk_440,
      fun _ _ ↦ walk_446, fun _ _ ↦ walk_447, fun _ _ ↦ walk_448, fun _ _ ↦ walk_449,
      fun _ _ ↦ walk_455, fun _ _ ↦ walk_456, fun _ _ ↦ walk_457, fun _ _ ↦ walk_458,
      fun _ _ ↦ walk_481, fun _ _ ↦ walk_482, fun _ _ ↦ walk_483, fun _ _ ↦ walk_484,
      fun _ _ ↦ walk_489, fun _ _ ↦ walk_490, fun _ _ ↦ walk_491, fun _ _ ↦ walk_492,
      fun _ _ ↦ walk_495, fun _ _ ↦ walk_496, fun _ _ ↦ walk_497, fun _ _ ↦ walk_498,
      fun _ _ ↦ walk_500, fun _ _ ↦ walk_501, fun _ _ ↦ walk_502, fun _ _ ↦ walk_503,
      fun _ _ ↦ walk_526, fun _ _ ↦ walk_527, fun _ _ ↦ walk_528, fun _ _ ↦ walk_529,
      fun _ _ ↦ walk_534, fun _ _ ↦ walk_535, fun _ _ ↦ walk_536, fun _ _ ↦ walk_537,
      fun _ _ ↦ walk_540, fun _ _ ↦ walk_541, fun _ _ ↦ walk_542, fun _ _ ↦ walk_543,
      fun _ _ ↦ walk_546, fun _ _ ↦ walk_547, fun _ _ ↦ walk_548, fun _ _ ↦ walk_549,
      fun _ _ ↦ walk_572, fun _ _ ↦ walk_573, fun _ _ ↦ walk_574, fun _ _ ↦ walk_575,
      fun _ _ ↦ walk_580, fun _ _ ↦ walk_581, fun _ _ ↦ walk_582, fun _ _ ↦ walk_583,
      fun _ _ ↦ walk_586, fun _ _ ↦ walk_587, fun _ _ ↦ walk_588, fun _ _ ↦ walk_589,
      fun _ _ ↦ walk_592, fun _ _ ↦ walk_593, fun _ _ ↦ walk_594, fun _ _ ↦ walk_595,
      fun _ _ ↦ walk_618, fun _ _ ↦ walk_619, fun _ _ ↦ walk_620, fun _ _ ↦ walk_621,
      fun _ _ ↦ walk_625, fun _ _ ↦ walk_626, fun _ _ ↦ walk_627, fun _ _ ↦ walk_628,
      fun _ _ ↦ walk_630, fun _ _ ↦ walk_631, fun _ _ ↦ walk_632, fun _ _ ↦ walk_634,
      fun _ _ ↦ walk_635, fun _ _ ↦ walk_636, fun _ _ ↦ walk_637, fun _ _ ↦ walk_638,
      fun _ _ ↦ walk_639, fun _ _ ↦ walk_661, fun _ _ ↦ walk_662, fun _ _ ↦ walk_663,
      fun _ _ ↦ walk_664, fun _ _ ↦ walk_667, fun _ _ ↦ walk_668, fun _ _ ↦ walk_669,
      fun _ _ ↦ walk_670, fun _ _ ↦ walk_672, fun _ _ ↦ walk_673, fun _ _ ↦ walk_674,
      fun _ _ ↦ walk_676, fun _ _ ↦ walk_677, fun _ _ ↦ walk_678, fun _ _ ↦ walk_679,
      fun _ _ ↦ walk_680, fun _ _ ↦ walk_681, fun _ _ ↦ walk_703, fun _ _ ↦ walk_704,
      fun _ _ ↦ walk_705, fun _ _ ↦ walk_706, fun _ _ ↦ walk_709, fun _ _ ↦ walk_710,
      fun _ _ ↦ walk_711, fun _ _ ↦ walk_712, fun _ _ ↦ walk_714, fun _ _ ↦ walk_715,
      fun _ _ ↦ walk_716, fun _ _ ↦ walk_718, fun _ _ ↦ walk_719, fun _ _ ↦ walk_720,
      fun _ _ ↦ walk_721, fun _ _ ↦ walk_722, fun _ _ ↦ walk_723, fun _ _ ↦ walk_745,
      fun _ _ ↦ walk_746, fun _ _ ↦ walk_747, fun _ _ ↦ walk_748, fun _ _ ↦ walk_752,
      fun _ _ ↦ walk_753, fun _ _ ↦ walk_754, fun _ _ ↦ walk_755, fun _ _ ↦ walk_757,
      fun _ _ ↦ walk_758, fun _ _ ↦ walk_759, fun _ _ ↦ walk_760, fun _ _ ↦ walk_761,
      fun _ _ ↦ walk_762, fun _ _ ↦ walk_763, fun _ _ ↦ walk_764, fun _ _ ↦ walk_765,
      fun _ _ ↦ walk_786, fun _ _ ↦ walk_787, fun _ _ ↦ walk_788, fun _ _ ↦ walk_789,
      fun _ _ ↦ walk_793, fun _ _ ↦ walk_794, fun _ _ ↦ walk_795, fun _ _ ↦ walk_796,
      fun _ _ ↦ walk_798, fun _ _ ↦ walk_799, fun _ _ ↦ walk_800, fun _ _ ↦ walk_801,
      fun _ _ ↦ walk_802, fun _ _ ↦ walk_803, fun _ _ ↦ walk_805, fun _ _ ↦ walk_806,
      fun _ _ ↦ walk_807, fun _ _ ↦ walk_808, fun _ _ ↦ walk_809, fun _ _ ↦ walk_832,
      fun _ _ ↦ walk_833, fun _ _ ↦ walk_834, fun _ _ ↦ walk_835, fun _ _ ↦ walk_839,
      fun _ _ ↦ walk_840, fun _ _ ↦ walk_841, fun _ _ ↦ walk_842, fun _ _ ↦ walk_844,
      fun _ _ ↦ walk_845, fun _ _ ↦ walk_846, fun _ _ ↦ walk_847, fun _ _ ↦ walk_848,
      fun _ _ ↦ walk_849, fun _ _ ↦ walk_851, fun _ _ ↦ walk_852, fun _ _ ↦ walk_853,
      fun _ _ ↦ walk_854, fun _ _ ↦ walk_877, fun _ _ ↦ walk_878, fun _ _ ↦ walk_879,
      fun _ _ ↦ walk_880, fun _ _ ↦ walk_884, fun _ _ ↦ walk_885, fun _ _ ↦ walk_886,
      fun _ _ ↦ walk_887, fun _ _ ↦ walk_889, fun _ _ ↦ walk_890, fun _ _ ↦ walk_891,
      fun _ _ ↦ walk_893, fun _ _ ↦ walk_894, fun _ _ ↦ walk_895, fun _ _ ↦ walk_897,
      fun _ _ ↦ walk_898, fun _ _ ↦ walk_899, fun _ _ ↦ walk_900, fun _ _ ↦ walk_901,
      fun _ _ ↦ walk_902, fun _ _ ↦ walk_981, fun _ _ ↦ walk_983, fun _ _ ↦ walk_985,
      fun _ _ ↦ walk_987, fun _ _ ↦ walk_993, fun _ _ ↦ walk_994, fun _ _ ↦ walk_995,
      fun _ _ ↦ walk_996, fun _ _ ↦ walk_1002, fun _ _ ↦ walk_1007, fun _ _ ↦ walk_1039,
      fun _ _ ↦ walk_1040, fun _ _ ↦ walk_1041, fun _ _ ↦ walk_1042, fun _ _ ↦ walk_1046,
      fun _ _ ↦ walk_1079, fun _ _ ↦ walk_1080, fun _ _ ↦ walk_1084, fun _ _ ↦ walk_1117,
      fun _ _ ↦ walk_1118, fun _ _ ↦ walk_1122, fun _ _ ↦ walk_1155, fun _ _ ↦ walk_1156,
      fun _ _ ↦ walk_1160, fun _ _ ↦ walk_1195, fun _ _ ↦ walk_1196, fun _ _ ↦ walk_1197,
      fun _ _ ↦ walk_1200, fun _ _ ↦ walk_1234, fun _ _ ↦ walk_1235, fun _ _ ↦ walk_1238,
      fun _ _ ↦ walk_1272, fun _ _ ↦ walk_1273, fun _ _ ↦ walk_1277, fun _ _ ↦ walk_1309,
      fun _ _ ↦ walk_1310, fun _ _ ↦ walk_1314, fun _ _ ↦ walk_1351, fun _ _ ↦ walk_1352,
      fun _ _ ↦ walk_1356, fun _ _ ↦ walk_1395, fun _ _ ↦ walk_1399, fun _ _ ↦ walk_1442,
      fun _ _ ↦ walk_1443, fun _ _ ↦ walk_1444, fun _ _ ↦ walk_1445, fun _ _ ↦ walk_1446,
      fun _ _ ↦ walk_1447, fun _ _ ↦ walk_1449, fun _ _ ↦ walk_1450, fun _ _ ↦ walk_1451,
      fun _ _ ↦ walk_1452, fun _ _ ↦ walk_1454, fun _ _ ↦ walk_1456, fun _ _ ↦ walk_1462,
      fun _ _ ↦ walk_1463, fun _ _ ↦ walk_1464, fun _ _ ↦ walk_1465, fun _ _ ↦ walk_1466,
      fun _ _ ↦ walk_1467, fun _ _ ↦ walk_1468, fun _ _ ↦ walk_1474, fun _ _ ↦ walk_1475,
      fun _ _ ↦ walk_1476, fun _ _ ↦ walk_1477, fun _ _ ↦ walk_1483, fun _ _ ↦ walk_1484,
      fun _ _ ↦ walk_1485, fun _ _ ↦ walk_1486, fun _ _ ↦ walk_1492, fun _ _ ↦ walk_1493,
      fun _ _ ↦ walk_1494, fun _ _ ↦ walk_1495, fun _ _ ↦ walk_1499, fun _ _ ↦ walk_1500,
      fun _ _ ↦ walk_1501, fun _ _ ↦ walk_1502, fun _ _ ↦ walk_1503, fun _ _ ↦ walk_1506,
      fun _ _ ↦ walk_1507, fun _ _ ↦ walk_1508, fun _ _ ↦ walk_1509, fun _ _ ↦ walk_1512,
      fun _ _ ↦ walk_1513, fun _ _ ↦ walk_1514, fun _ _ ↦ walk_1515, fun _ _ ↦ walk_1518,
      fun _ _ ↦ walk_1519, fun _ _ ↦ walk_1520, fun _ _ ↦ walk_1521, fun _ _ ↦ walk_1524,
      fun _ _ ↦ walk_1525, fun _ _ ↦ walk_1526, fun _ _ ↦ walk_1527, fun _ _ ↦ walk_1528,
      fun _ _ ↦ walk_1531, fun _ _ ↦ walk_1532, fun _ _ ↦ walk_1533, fun _ _ ↦ walk_1535,
      fun _ _ ↦ walk_1536, fun _ _ ↦ walk_1537, fun _ _ ↦ walk_1538⟩
  exact List.forall_iff_forall_mem.mp key

end
end LeanVM.SaltedGuest.End
