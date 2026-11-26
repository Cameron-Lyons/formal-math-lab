module

public import UCBound.Cert2DMem
public import UCBound.CertFsimTrees

@[expose] public section

namespace UCBound.Cert2D
open UCBound.Iv UCBound.Cert UCBound.FastIv

set_option maxRecDepth 200000 in set_option maxHeartbeats 16000000 in
lemma chk_Fsim_b0 : check2DW okFsim p01_Fsim p68_Fsim p01_Fsim p68_Fsim treeFsim_b0 = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 16000000 in
lemma chk_Fsim_b1 : check2DW okFsim p01_Fsim p68_Fsim p68_Fsim p70_Fsim treeFsim_b1 = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 16000000 in
lemma chk_Fsim_b2 : check2DW okFsim p01_Fsim p68_Fsim p70_Fsim p999_Fsim treeFsim_b2 = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 16000000 in
lemma chk_Fsim_b3 : check2DW okFsimHess p68_Fsim p70_Fsim p68_Fsim p70_Fsim treeFsim_b3 = true := by decide +kernel

end UCBound.Cert2D
