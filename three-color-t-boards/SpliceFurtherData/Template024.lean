import SplicePacked

-- Generated from splice_further.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceFurtherData
open Splice

def template24 : Group where
  k := 5
  pivot := [2, 2, 0, 0, 2, 0, 2, 0, 0, 2, 2]
  caps := []
  tails := []
  upperMask := 177790054053727
  lowerMask := 2417851639051468295358624

private def cap24_0Codes : List Nat := [
  15286923288, 329352057756]

def cap24_0 : Group.Batch template24.capOK :=
  Packed.capBatch template24 159092 rfl (by decide) cap24_0Codes
    (by decide +kernel)

end TBoards.SpliceFurtherData
