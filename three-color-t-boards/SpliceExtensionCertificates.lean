import SpliceData
import SpliceExtensionData
import SpliceSymmetry

-- Generated from the two splice certificates by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards
open Splice

/-- At least 10,485,708 distinct labeled T boards arise from the two splice certificates. -/
theorem at_least_10485708 :
    ∃ f : Fin 10485708 → Board, (∀ i, Valid (f i)) ∧
      (∀ i j, f i = f j → i = j) := by
  apply orbit_lower_bound 5 (SpliceData.groups ++ SpliceExtensionData.groups)
    SpliceExtensionData.markers 10485708
  · exact List.forall_mem_append.mpr ⟨SpliceData.checked, SpliceExtensionData.checked⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · rw [List.map_append, List.sum_append, SpliceExtensionData.size_sum]
    decide +kernel

end TBoards

#print axioms TBoards.at_least_10485708
