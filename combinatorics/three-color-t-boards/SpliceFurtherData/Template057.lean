import SplicePacked

-- Generated from splice_further.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceFurtherData
open Splice

def template57 : Group where
  k := 5
  pivot := [2, 2, 0, 1, 2, 2, 2, 1, 0, 2, 2]
  caps := []
  tails := []
  upperMask := 4593733225952795
  lowerMask := 2417851634635525123459556

private def cap57_0Codes : List Nat := [
  139533616876]

def cap57_0 : Group.Batch template57.capOK :=
  Packed.capBatch template57 161792 rfl (by decide) cap57_0Codes
    (by decide +kernel)

end TBoards.SpliceFurtherData
