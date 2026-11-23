import SplicePacked

-- Generated from splice_further.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceFurtherData
open Splice

def template80 : Group where
  k := 5
  pivot := [2, 2, 0, 1, 2, 2, 2, 1, 0, 2, 2]
  caps := []
  tails := []
  upperMask := 4875203905599035
  lowerMask := 2417851634354054443813316

private def cap80_0Codes : List Nat := [
  411490005484]

def cap80_0 : Group.Batch template80.capOK :=
  Packed.capBatch template80 161792 rfl (by decide) cap80_0Codes
    (by decide +kernel)

end TBoards.SpliceFurtherData
