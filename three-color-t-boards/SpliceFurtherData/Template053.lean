import SplicePacked

-- Generated from splice_further.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceFurtherData
open Splice

def template53 : Group where
  k := 5
  pivot := [2, 2, 0, 1, 2, 2, 2, 1, 0, 2, 2]
  caps := []
  tails := []
  upperMask := 9308159877856827
  lowerMask := 2417851629921098471555524

private def cap53_0Codes : List Nat := [
  137153781856]

def cap53_0 : Group.Batch template53.capOK :=
  Packed.capBatch template53 161792 rfl (by decide) cap53_0Codes
    (by decide +kernel)

end TBoards.SpliceFurtherData
