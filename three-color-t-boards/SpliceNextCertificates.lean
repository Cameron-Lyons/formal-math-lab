import SpliceRanges
import SpliceNextPrefixData

-- Generated from five splice certificates by prepare_splice_next.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards
open Splice

private theorem firstLayerSize : (SpliceData.groups.map Group.size).sum = 29080 := by
  decide +kernel

private def nextGroups : List Group :=
  ((((SpliceData.groups ++ SpliceExtensionData.groups) ++ SpliceFurtherData.groups) ++ SpliceTransferData.groups) ++ SpliceNextData.groups)

private theorem nextChecked : ∀ g ∈ nextGroups, g.Checked :=
  List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨SpliceData.checked, SpliceExtensionData.checked⟩, SpliceFurtherData.checked⟩, SpliceTransferData.checked⟩, SpliceNextData.checked⟩

private theorem nextCut : ∀ g ∈ nextGroups, g.k = 5 := by decide +kernel

private theorem nextDistinct : (nextGroups.flatMap Group.boards).Nodup := by
  apply groups_nodup_of_separated 5 nextGroups nextChecked nextCut
  decide +kernel

/-- Distinct labeled boards certified by five row-five splice layers. -/
theorem at_least_32155680 :
    ∃ f : Fin 32155680 → Board, (∀ i, Valid (f i)) ∧
      (∀ i j, f i = f j → i = j) := by
  apply prefix_orbit_lower_bound_of_nodup 5 nextGroups SpliceNextPrefixData.classify 32155680
    nextChecked nextCut nextDistinct SpliceNextPrefixData.classified
  simp only [nextGroups, List.map_append, List.sum_append, firstLayerSize,
      SpliceExtensionData.size_sum,
      SpliceFurtherData.size_sum,
      SpliceTransferData.size_sum,
      SpliceNextData.size_sum] <;> decide

end TBoards

#print axioms TBoards.at_least_32155680
