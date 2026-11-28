import SplicePacked

-- Generated from splice_further.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceFurtherData
open Splice

def template39 : Group where
  k := 5
  pivot := [2, 2, 0, 1, 2, 2, 2, 1, 0, 2, 2]
  caps := []
  tails := []
  upperMask := 11278450340413243
  lowerMask := 2417851627950808008999108

private def cap39_0Codes : List Nat := [
  31818639267]

def cap39_0 : Group.Batch template39.capOK :=
  Packed.capBatch template39 161792 rfl (by decide) cap39_0Codes
    (by decide +kernel)

end TBoards.SpliceFurtherData
