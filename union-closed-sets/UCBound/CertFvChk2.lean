module

public import UCBound.Cert2DMem
public import UCBound.CertFvTrees

@[expose] public section

namespace UCBound.Cert2D
open UCBound.Iv UCBound.Cert UCBound.FastIv

set_option maxRecDepth 200000 in set_option maxHeartbeats 16000000 in
lemma chk_Fv_b4 : check2DW okFv p68_Fv p70_Fv p70_Fv p999_Fv treeFv_b4 = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 16000000 in
lemma chk_Fv_b5 : check2DW okFv p70_Fv p999_Fv p70_Fv p999_Fv treeFv_b5 = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 16000000 in
lemma chk_Fv_b6 : check2DW okFv p01_Fv p999_Fv p999_Fv p99999_Fv treeFv_b6 = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 16000000 in
lemma chk_Fv_b7 : check2DW okFv p999_Fv p99999_Fv p999_Fv p99999_Fv treeFv_b7 = true := by decide +kernel

end UCBound.Cert2D
