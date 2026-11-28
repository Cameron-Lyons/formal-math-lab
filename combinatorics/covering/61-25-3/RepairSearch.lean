import Covering
import RepairCount

namespace Covering61.RepairSearch

/-- All 296,010 choices of six published groups to replace by five fail the counting test. -/
theorem published_six_for_five_screen : remainingCases published 6 5 = [] := by native_decide

/-- The same test covers the smaller local repairs. -/
theorem published_five_for_four_screen : remainingCases published 5 4 = [] := by native_decide

theorem published_four_for_three_screen : remainingCases published 4 3 = [] := by native_decide

theorem candidate_three_group_screen : remainingCases candidate 3 3 = [] := by native_decide

end Covering61.RepairSearch
