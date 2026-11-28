import SplicePacked

-- Generated from splice_further.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceFurtherData
open Splice

def template87 : Group where
  k := 5
  pivot := [2, 2, 0, 1, 2, 2, 2, 1, 0, 2, 2]
  caps := []
  tails := []
  upperMask := 9308434755761723
  lowerMask := 2417851629920823593650628

private def cap87_0Codes : List Nat := [
  423064945795]

def cap87_0 : Group.Batch template87.capOK :=
  Packed.capBatch template87 161792 rfl (by decide) cap87_0Codes
    (by decide +kernel)

end TBoards.SpliceFurtherData
