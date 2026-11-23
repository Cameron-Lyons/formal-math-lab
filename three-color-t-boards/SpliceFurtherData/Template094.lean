import SplicePacked

-- Generated from splice_further.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceFurtherData
open Splice

def template94 : Group where
  k := 5
  pivot := [2, 2, 0, 2, 2, 1, 2, 2, 0, 2, 2]
  caps := []
  tails := []
  upperMask := 6898030365259547
  lowerMask := 2417851632331227984152804

private def cap94_0Codes : List Nat := [
  3635851296, 5056208662, 11643958578,
  282622649562]

def cap94_0 : Group.Batch template94.capOK :=
  Packed.capBatch template94 163763 rfl (by decide) cap94_0Codes
    (by decide +kernel)

end TBoards.SpliceFurtherData
