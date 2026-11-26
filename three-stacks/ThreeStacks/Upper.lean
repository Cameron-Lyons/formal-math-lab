import ThreeStacks.OneStack
import ThreeStacks.Machine
import ThreeStacks.Certificate

namespace ThreeStacks

theorem published_isDeck : IsDeck 21 published := by
  unfold IsDeck target published
  decide +kernel

/-- An actual sorting run would yield two intermediate orders rejected by the certificate. -/
theorem published_unsortable : ¬ Sortable 21 published := by
  rintro ⟨A, B, first, middle, last⟩
  have hB := pass_perm last
  have hA := (pass_perm middle).trans hB
  have hp : published.Nodup := published_isDeck.nodup_iff.mpr (List.nodup_range' 1)
  exact noWitnessOrders A B hA hB (pass_respects first hp)
    (pass_respects middle ((pass_perm first).nodup hp))
    (pass_respects last (hB.nodup_iff.mpr (List.nodup_range' 1)))

theorem published_no_physical_run : ¬ Run published [] [] [] (target 21) :=
  fun run => published_unsortable ((run_iff_sortsTo _ _).mp run)

end ThreeStacks
