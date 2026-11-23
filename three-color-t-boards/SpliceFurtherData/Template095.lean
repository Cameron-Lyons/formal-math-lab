import SplicePacked

-- Generated from splice_further.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceFurtherData
open Splice

def template95 : Group where
  k := 5
  pivot := [2, 2, 0, 2, 2, 1, 2, 2, 0, 2, 2]
  caps := []
  tails := []
  upperMask := 3520330669897499
  lowerMask := 2417851635708927679514852

private def cap95_0Codes : List Nat := [
  11801739528, 14513190876, 31957170894]

def cap95_0 : Group.Batch template95.capOK :=
  Packed.capBatch template95 163763 rfl (by decide) cap95_0Codes
    (by decide +kernel)

end TBoards.SpliceFurtherData
