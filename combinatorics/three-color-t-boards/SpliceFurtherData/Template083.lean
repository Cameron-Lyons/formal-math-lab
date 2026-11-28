import SplicePacked

-- Generated from splice_further.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceFurtherData
open Splice

def template83 : Group where
  k := 5
  pivot := [2, 2, 0, 1, 2, 2, 2, 1, 0, 2, 2]
  caps := []
  tails := []
  upperMask := 371574247012123
  lowerMask := 2417851638857684102400228

private def cap83_0Codes : List Nat := [
  418860541731]

def cap83_0 : Group.Batch template83.capOK :=
  Packed.capBatch template83 161792 rfl (by decide) cap83_0Codes
    (by decide +kernel)

end TBoards.SpliceFurtherData
