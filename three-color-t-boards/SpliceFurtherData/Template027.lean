import SplicePacked

-- Generated from splice_further.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceFurtherData
open Splice

def template27 : Group where
  k := 5
  pivot := [2, 2, 0, 1, 2, 2, 2, 1, 0, 2, 2]
  caps := []
  tails := []
  upperMask := 9308125518118715
  lowerMask := 2417851629921132831293636

private def cap27_0Codes : List Nat := [
  1226290599, 3637261269]

def cap27_0 : Group.Batch template27.capOK :=
  Packed.capBatch template27 161792 rfl (by decide) cap27_0Codes
    (by decide +kernel)

end TBoards.SpliceFurtherData
