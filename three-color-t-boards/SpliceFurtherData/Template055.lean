import SplicePacked

-- Generated from splice_further.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceFurtherData
open Splice

def template55 : Group where
  k := 5
  pivot := [2, 2, 0, 1, 2, 2, 2, 1, 0, 2, 2]
  caps := []
  tails := []
  upperMask := 11559925315026747
  lowerMask := 2417851627669333034385604

private def cap55_0Codes : List Nat := [
  137663617482]

def cap55_0 : Group.Batch template55.capOK :=
  Packed.capBatch template55 161792 rfl (by decide) cap55_0Codes
    (by decide +kernel)

end TBoards.SpliceFurtherData
