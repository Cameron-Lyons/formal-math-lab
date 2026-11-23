import SpliceRanges
import SpliceSixthPrefixData

-- Generated from six splice certificates by prepare_splice_next.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards
open Splice

private theorem firstLayerSize : (SpliceData.groups.map Group.size).sum = 29080 := by
  decide +kernel

def sixthGroups : List Group :=
  (((((SpliceData.groups ++ SpliceExtensionData.groups) ++ SpliceFurtherData.groups) ++ SpliceTransferData.groups) ++ SpliceNextData.groups) ++ SpliceSixthData.groups)

theorem sixthChecked : ∀ g ∈ sixthGroups, g.Checked :=
  List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨SpliceData.checked, SpliceExtensionData.checked⟩, SpliceFurtherData.checked⟩, SpliceTransferData.checked⟩, SpliceNextData.checked⟩, SpliceSixthData.checked⟩

theorem sixthCut : ∀ g ∈ sixthGroups, g.k = 5 := by decide +kernel

theorem sixthDistinct : (sixthGroups.flatMap Group.boards).Nodup := by
  apply groups_nodup_of_separated 5 sixthGroups sixthChecked sixthCut
  decide +kernel

theorem sixthSize : (sixthGroups.map Group.size).sum = 3735918 := by
  simp only [sixthGroups, List.map_append, List.sum_append, firstLayerSize,
      SpliceExtensionData.size_sum,
      SpliceFurtherData.size_sum,
      SpliceTransferData.size_sum,
      SpliceNextData.size_sum,
      SpliceSixthData.size_sum] <;> decide

/-- Distinct labeled boards certified by six row-five splice layers. -/
theorem at_least_44831016 :
    ∃ f : Fin 44831016 → Board, (∀ i, Valid (f i)) ∧
      (∀ i j, f i = f j → i = j) := by
  apply prefix_orbit_lower_bound_of_nodup 5 sixthGroups SpliceSixthPrefixData.classify 44831016
    sixthChecked sixthCut sixthDistinct SpliceSixthPrefixData.classified
  simp only [sixthGroups, List.map_append, List.sum_append, firstLayerSize,
      SpliceExtensionData.size_sum,
      SpliceFurtherData.size_sum,
      SpliceTransferData.size_sum,
      SpliceNextData.size_sum,
      SpliceSixthData.size_sum] <;> decide

end TBoards

#print axioms TBoards.at_least_44831016
