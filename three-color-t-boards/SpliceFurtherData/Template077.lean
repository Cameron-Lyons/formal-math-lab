import SplicePacked

-- Generated from splice_further.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceFurtherData
open Splice

def template77 : Group where
  k := 5
  pivot := [2, 2, 0, 1, 2, 2, 2, 1, 0, 2, 2]
  caps := []
  tails := []
  upperMask := 11349093961971515
  lowerMask := 2417851627880164387440836

private def cap77_0Codes : List Nat := [
  388755477867]

def cap77_0 : Group.Batch template77.capOK :=
  Packed.capBatch template77 161792 rfl (by decide) cap77_0Codes
    (by decide +kernel)

end TBoards.SpliceFurtherData
