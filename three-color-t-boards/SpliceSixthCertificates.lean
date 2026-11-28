import SpliceRanges
import SpliceSixthPrefixData

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

end TBoards
