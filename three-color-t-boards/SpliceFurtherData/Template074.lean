import SplicePacked

-- Generated from splice_further.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceFurtherData
open Splice

def template74 : Group where
  k := 5
  pivot := [2, 2, 0, 1, 2, 2, 2, 1, 0, 2, 2]
  caps := []
  tails := []
  upperMask := 2623374043920155
  lowerMask := 2417851636605884305492196

private def cap74_0Codes : List Nat := [
  388372329246]

def cap74_0 : Group.Batch template74.capOK :=
  Packed.capBatch template74 161792 rfl (by decide) cap74_0Codes
    (by decide +kernel)

end TBoards.SpliceFurtherData
