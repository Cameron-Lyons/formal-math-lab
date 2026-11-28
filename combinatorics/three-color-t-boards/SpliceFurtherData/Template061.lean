import SplicePacked

-- Generated from splice_further.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceFurtherData
open Splice

def template61 : Group where
  k := 5
  pivot := [2, 2, 0, 1, 2, 2, 2, 1, 0, 2, 2]
  caps := []
  tails := []
  upperMask := 9009097012297243
  lowerMask := 2417851630220161337115108

private def cap61_0Codes : List Nat := [
  284125011229]

def cap61_0 : Group.Batch template61.capOK :=
  Packed.capBatch template61 161792 rfl (by decide) cap61_0Codes
    (by decide +kernel)

end TBoards.SpliceFurtherData
