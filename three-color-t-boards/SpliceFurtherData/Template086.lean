import SplicePacked

-- Generated from splice_further.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceFurtherData
open Splice

def template86 : Group where
  k := 5
  pivot := [2, 2, 0, 1, 2, 2, 2, 1, 0, 2, 2]
  caps := []
  tails := []
  upperMask := 11331540430763547
  lowerMask := 2417851627897717918648804

private def cap86_0Codes : List Nat := [
  422417659882]

def cap86_0 : Group.Batch template86.capOK :=
  Packed.capBatch template86 161792 rfl (by decide) cap86_0Codes
    (by decide +kernel)

end TBoards.SpliceFurtherData
