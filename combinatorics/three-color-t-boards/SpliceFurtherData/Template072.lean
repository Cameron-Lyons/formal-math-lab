import SplicePacked

-- Generated from splice_further.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceFurtherData
open Splice

def template72 : Group where
  k := 5
  pivot := [2, 2, 0, 1, 2, 2, 2, 1, 0, 2, 2]
  caps := []
  tails := []
  upperMask := 11278729513285403
  lowerMask := 2417851627950528836126948

private def cap72_0Codes : List Nat := [
  329352064311, 422417657937]

def cap72_0 : Group.Batch template72.capOK :=
  Packed.capBatch template72 161792 rfl (by decide) cap72_0Codes
    (by decide +kernel)

end TBoards.SpliceFurtherData
