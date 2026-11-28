import SplicePacked

-- Generated from splice_further.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceFurtherData
open Splice

def template70 : Group where
  k := 5
  pivot := [2, 2, 0, 1, 2, 2, 2, 1, 0, 2, 2]
  caps := []
  tails := []
  upperMask := 2341658551139867
  lowerMask := 2417851636887599798272484

private def cap70_0Codes : List Nat := [
  324664953625]

def cap70_0 : Group.Batch template70.capOK :=
  Packed.capBatch template70 161792 rfl (by decide) cap70_0Codes
    (by decide +kernel)

end TBoards.SpliceFurtherData
