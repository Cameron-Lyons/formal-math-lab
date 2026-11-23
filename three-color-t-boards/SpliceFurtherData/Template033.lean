import SplicePacked

-- Generated from splice_further.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceFurtherData
open Splice

def template33 : Group where
  k := 5
  pivot := [2, 2, 0, 1, 2, 2, 2, 1, 0, 2, 2]
  caps := []
  tails := []
  upperMask := 19730528745243
  lowerMask := 2417851639209527820667108

private def cap33_0Codes : List Nat := [
  4067296095]

def cap33_0 : Group.Batch template33.capOK :=
  Packed.capBatch template33 161792 rfl (by decide) cap33_0Codes
    (by decide +kernel)

end TBoards.SpliceFurtherData
