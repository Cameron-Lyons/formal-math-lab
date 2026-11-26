import Height14.Graph
import Height14.Refinement

namespace Height14.Cert

theorem goodRows : ∀ r, GoodRow graph r := checkedRows (by native_decide)
theorem goodEnds : GoodEnds graph := by native_decide

end Height14.Cert
