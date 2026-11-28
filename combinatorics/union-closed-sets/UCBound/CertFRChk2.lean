module

public import UCBound.Cert2DMem
public import UCBound.CertFRTrees

@[expose] public section

namespace UCBound.Cert2D
open UCBound.Iv UCBound.Cert UCBound.FastIv

set_option maxRecDepth 200000 in set_option maxHeartbeats 16000000 in
lemma chk_FR_b4 : check2DW okFR p68_FR p70_FR p70_FR p999_FR treeFR_b4 = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 16000000 in
lemma chk_FR_b5 : check2DW okFR p70_FR p999_FR p70_FR p999_FR treeFR_b5 = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 16000000 in
lemma chk_FR_b6 : check2DW okFR p01_FR p999_FR p999_FR p99999_FR treeFR_b6 = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 16000000 in
lemma chk_FR_b7 : check2DW okFR p999_FR p99999_FR p999_FR p99999_FR treeFR_b7 = true := by decide +kernel

end UCBound.Cert2D
