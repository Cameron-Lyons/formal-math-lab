import SplicePacked

-- Generated from splice_further.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceFurtherData
open Splice

def template52 : Group where
  k := 5
  pivot := [2, 2, 0, 1, 2, 2, 2, 1, 0, 2, 2]
  caps := []
  tails := []
  upperMask := 11348853443804731
  lowerMask := 2417851627880404905607620

private def cap52_0Codes : List Nat := [
  136549522495]

def cap52_0 : Group.Batch template52.capOK :=
  Packed.capBatch template52 161792 rfl (by decide) cap52_0Codes
    (by decide +kernel)

end TBoards.SpliceFurtherData
