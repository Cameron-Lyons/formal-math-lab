import SplicePacked

-- Generated from splice_sixth.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceSixthData
open Splice

def template11 : Group where
  k := 5
  pivot := [2, 0, 1, 1, 0, 2, 0, 1, 1, 0, 2]
  caps := []
  tails := []
  upperMask := 75228774484696161946
  lowerMask := 2417776410454773653250405

private def cap11_0Codes : List Nat := [
  14336866554, 14336984646, 104993379072]

def cap11_0 : Group.Batch template11.capOK :=
  Packed.capBatch template11 127370 rfl (by decide) cap11_0Codes
    (by decide +kernel)

end TBoards.SpliceSixthData
