import SplicePacked

-- Generated from splice_further.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceFurtherData
open Splice

def template84 : Group where
  k := 5
  pivot := [2, 2, 0, 1, 2, 2, 2, 1, 0, 2, 2]
  caps := []
  tails := []
  upperMask := 371333728845339
  lowerMask := 2417851638857924620567012

private def cap84_0Codes : List Nat := [
  420007391407]

def cap84_0 : Group.Batch template84.capOK :=
  Packed.capBatch template84 161792 rfl (by decide) cap84_0Codes
    (by decide +kernel)

end TBoards.SpliceFurtherData
