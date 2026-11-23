import SplicePacked

-- Generated from splice_further.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceFurtherData
open Splice

def template67 : Group where
  k := 5
  pivot := [2, 2, 0, 1, 2, 2, 2, 1, 0, 2, 2]
  caps := []
  tails := []
  upperMask := 11331265552858651
  lowerMask := 2417851627897992796553700

private def cap67_0Codes : List Nat := [
  294231256327]

def cap67_0 : Group.Batch template67.capOK :=
  Packed.capBatch template67 161792 rfl (by decide) cap67_0Codes
    (by decide +kernel)

end TBoards.SpliceFurtherData
