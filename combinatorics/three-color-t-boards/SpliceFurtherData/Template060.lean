import SplicePacked

-- Generated from splice_further.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceFurtherData
open Splice

def template60 : Group where
  k := 5
  pivot := [2, 2, 0, 1, 2, 2, 2, 1, 0, 2, 2]
  caps := []
  tails := []
  upperMask := 371299369107227
  lowerMask := 2417851638857958980305124

private def cap60_0Codes : List Nat := [
  282622649562]

def cap60_0 : Group.Batch template60.capOK :=
  Packed.capBatch template60 161792 rfl (by decide) cap60_0Codes
    (by decide +kernel)

end TBoards.SpliceFurtherData
