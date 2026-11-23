import StripSearch

namespace Grid75.StripSearch

set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option Elab.async false

/- Every consecutive band of 32 original rows has a verified refutation. -/
refute_strips certificates 32 43

end Grid75.StripSearch
