import SplicePacked

-- Generated from splice_further.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceFurtherData
open Splice

def template48 : Group where
  k := 5
  pivot := [2, 2, 0, 1, 2, 2, 2, 1, 0, 2, 2]
  caps := []
  tails := []
  upperMask := 9290567691943483
  lowerMask := 2417851629938690657468868

private def cap48_0Codes : List Nat := [
  95828929453]

def cap48_0 : Group.Batch template48.capOK :=
  Packed.capBatch template48 161792 rfl (by decide) cap48_0Codes
    (by decide +kernel)

end TBoards.SpliceFurtherData
