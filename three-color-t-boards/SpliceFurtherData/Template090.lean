import SplicePacked

-- Generated from splice_further.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceFurtherData
open Splice

def template90 : Group where
  k := 5
  pivot := [1, 2, 0, 0, 2, 0, 0, 0, 0, 2, 1]
  caps := []
  tails := []
  upperMask := 5315131427330278589167
  lowerMask := 2412536507801928070823184

private def cap90_0Codes : List Nat := [
  283669410632, 290614281620, 294086717114,
  301031588102]

def cap90_0 : Group.Batch template90.capOK :=
  Packed.capBatch template90 99880 rfl (by decide) cap90_0Codes
    (by decide +kernel)

end TBoards.SpliceFurtherData
