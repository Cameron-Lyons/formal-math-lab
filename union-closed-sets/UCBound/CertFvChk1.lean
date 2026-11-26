module

public import UCBound.Cert2DMem
public import UCBound.CertFvTrees

@[expose] public section

namespace UCBound.Cert2D
open UCBound.Iv UCBound.Cert UCBound.FastIv

set_option maxRecDepth 200000 in set_option maxHeartbeats 16000000 in
lemma chk_Fv_b0 : check2DW okFv p01_Fv p68_Fv p01_Fv p68_Fv treeFv_b0 = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 16000000 in
lemma chk_Fv_b1 : check2DW okFv p01_Fv p68_Fv p68_Fv p70_Fv treeFv_b1 = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 16000000 in
lemma chk_Fv_b2 : check2DW okFv p01_Fv p68_Fv p70_Fv p999_Fv treeFv_b2 = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 16000000 in
lemma chk_Fv_b3 : check2DW okFvHess p68_Fv p70_Fv p68_Fv p70_Fv treeFv_b3 = true := by decide +kernel

end UCBound.Cert2D
