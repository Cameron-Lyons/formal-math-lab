import SplicePrefixData

-- Generated from the four splice certificates by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards
open Splice

private theorem firstLayerSize : (SpliceData.groups.map Group.size).sum = 29080 := by
  decide +kernel

/-- At least 21,158,736 distinct valid labeled T boards arise from the four splice certificates. -/
theorem at_least_21158736 :
    ∃ f : Fin 21158736 → Board, (∀ i, Valid (f i)) ∧
      (∀ i j, f i = f j → i = j) := by
  apply prefix_orbit_lower_bound 5
    (((SpliceData.groups ++ SpliceExtensionData.groups) ++ SpliceFurtherData.groups) ++
      SpliceTransferData.groups) SplicePrefixData.classify 21158736
  · exact List.forall_mem_append.mpr
      ⟨List.forall_mem_append.mpr
        ⟨List.forall_mem_append.mpr ⟨SpliceData.checked, SpliceExtensionData.checked⟩,
          SpliceFurtherData.checked⟩, SpliceTransferData.checked⟩
  · decide +kernel
  · decide +kernel
  · exact SplicePrefixData.classified
  · simp only [List.map_append, List.sum_append, firstLayerSize, SpliceExtensionData.size_sum,
      SpliceFurtherData.size_sum, SpliceTransferData.size_sum] <;> decide

end TBoards

#print axioms TBoards.at_least_21158736
