module

public import UCBound.Cert2DMem
public import UCBound.CertFRTrees

@[expose] public section

namespace UCBound.Cert2D
open UCBound.Iv UCBound.Cert UCBound.FastIv

set_option maxRecDepth 200000 in set_option maxHeartbeats 16000000 in
lemma chk_FR_b0 : check2DW okFR p01_FR p68_FR p01_FR p68_FR treeFR_b0 = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 16000000 in
lemma chk_FR_b1 : check2DW okFR p01_FR p68_FR p68_FR p70_FR treeFR_b1 = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 16000000 in
lemma chk_FR_b2 : check2DW okFR p01_FR p68_FR p70_FR p999_FR treeFR_b2 = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 16000000 in
lemma chk_FR_b3 : check2DW okFRHess p68_FR p70_FR p68_FR p70_FR treeFR_b3 = true := by decide +kernel

end UCBound.Cert2D
