import SplicePacked

-- Generated from splice_further.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceFurtherData
open Splice

def template50 : Group where
  k := 5
  pivot := [2, 2, 0, 1, 2, 2, 2, 1, 0, 2, 2]
  caps := []
  tails := []
  upperMask := 9290846864815643
  lowerMask := 2417851629938411484596708

private def cap50_0Codes : List Nat := [
  129030411415, 287097970927, 423065300575]

def cap50_0 : Group.Batch template50.capOK :=
  Packed.capBatch template50 161792 rfl (by decide) cap50_0Codes
    (by decide +kernel)

end TBoards.SpliceFurtherData
