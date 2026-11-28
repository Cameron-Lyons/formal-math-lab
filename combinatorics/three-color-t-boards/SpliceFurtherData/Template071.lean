import SplicePacked

-- Generated from splice_further.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceFurtherData
open Splice

def template71 : Group where
  k := 5
  pivot := [2, 2, 0, 1, 2, 2, 2, 1, 0, 2, 2]
  caps := []
  tails := []
  upperMask := 9308129813085979
  lowerMask := 2417851629921128536326372

private def cap71_0Codes : List Nat := [
  329352057756]

def cap71_0 : Group.Batch template71.capOK :=
  Packed.capBatch template71 161792 rfl (by decide) cap71_0Codes
    (by decide +kernel)

end TBoards.SpliceFurtherData
