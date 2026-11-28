import SplicePacked

-- Generated from splice_further.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceFurtherData
open Splice

def template79 : Group where
  k := 5
  pivot := [2, 2, 0, 1, 2, 2, 2, 1, 0, 2, 2]
  caps := []
  tails := []
  upperMask := 11559959674764859
  lowerMask := 2417851627669298674647492

private def cap79_0Codes : List Nat := [
  409675827799]

def cap79_0 : Group.Batch template79.capOK :=
  Packed.capBatch template79 161792 rfl (by decide) cap79_0Codes
    (by decide +kernel)

end TBoards.SpliceFurtherData
