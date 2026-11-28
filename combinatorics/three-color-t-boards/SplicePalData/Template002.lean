import SplicePacked

-- Generated from splice_pal.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SplicePalData
open Splice

def template2 : Group where
  k := 5
  pivot := [2, 0, 1, 1, 0, 2, 0, 1, 1, 0, 2]
  caps := []
  tails := []
  upperMask := 75228774484696161946
  lowerMask := 2417776410454773653250405

private def cap2_0Codes : List Nat := [
  104993260980, 105002940636]

def cap2_0 : Group.Batch template2.capOK :=
  Packed.capBatch template2 127370 rfl (by decide) cap2_0Codes
    (by decide +kernel)

end TBoards.SplicePalData
