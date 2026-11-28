import SplicePal
import SplicePalData
import SpliceSixthCertificates

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards
open Splice

/-- Count the six palette images of the palindromic-prefix products alongside the six earlier layers. -/
theorem at_least_45083592 :
    ∃ f : Fin 45083592 → Board, (∀ i, Valid (f i)) ∧
      (∀ i j, f i = f j → i = j) := by
  apply pal_supplement_lower_bound 5 sixthGroups SplicePalData.groups SpliceSixthPrefixData.classify 45083592
    sixthChecked sixthCut sixthDistinct SpliceSixthPrefixData.classified SplicePalData.checked
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · rw [sixthSize, SplicePalData.size_sum]
    decide

end TBoards

#print axioms TBoards.at_least_45083592
