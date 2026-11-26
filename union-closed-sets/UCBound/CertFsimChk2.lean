module

public import UCBound.Cert2DMem
public import UCBound.CertFsimTrees

@[expose] public section

namespace UCBound.Cert2D
open UCBound.Iv UCBound.Cert UCBound.FastIv

set_option maxRecDepth 200000 in set_option maxHeartbeats 16000000 in
lemma chk_Fsim_b4 : check2DW okFsim p68_Fsim p70_Fsim p70_Fsim p999_Fsim treeFsim_b4 = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 16000000 in
lemma chk_Fsim_b5 : check2DW okFsim p70_Fsim p999_Fsim p70_Fsim p999_Fsim treeFsim_b5 = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 16000000 in
lemma chk_Fsim_b6 : check2DW okFsim p01_Fsim p999_Fsim p999_Fsim p99999_Fsim treeFsim_b6 = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 16000000 in
lemma chk_Fsim_b7 : check2DW okFsim p999_Fsim p99999_Fsim p999_Fsim p99999_Fsim treeFsim_b7 = true := by decide +kernel

end UCBound.Cert2D
