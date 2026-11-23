import SplicePacked

-- Generated from splice_further.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceFurtherData
open Splice

def template46 : Group where
  k := 5
  pivot := [2, 2, 0, 1, 2, 2, 2, 1, 0, 2, 2]
  caps := []
  tails := []
  upperMask := 4593423988309787
  lowerMask := 2417851634635834361102564

private def cap46_0Codes : List Nat := [
  42292629090]

def cap46_0 : Group.Batch template46.capOK :=
  Packed.capBatch template46 161792 rfl (by decide) cap46_0Codes
    (by decide +kernel)

end TBoards.SpliceFurtherData
