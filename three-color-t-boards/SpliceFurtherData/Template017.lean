import SplicePacked

-- Generated from splice_further.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceFurtherData
open Splice

def template17 : Group where
  k := 5
  pivot := [2, 2, 0, 0, 2, 0, 2, 0, 0, 2, 2]
  caps := []
  tails := []
  upperMask := 2288886723393119
  lowerMask := 2417851636940371626019232

private def cap17_0Codes : List Nat := [
  11643960037, 324664953625]

def cap17_0 : Group.Batch template17.capOK :=
  Packed.capBatch template17 159092 rfl (by decide) cap17_0Codes
    (by decide +kernel)

end TBoards.SpliceFurtherData
