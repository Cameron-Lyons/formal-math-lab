import SplicePacked

-- Generated from splice_further.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceFurtherData
open Splice

def template16 : Group where
  k := 5
  pivot := [2, 2, 0, 0, 2, 0, 2, 0, 0, 2, 2]
  caps := []
  tails := []
  upperMask := 2288852363655007
  lowerMask := 2417851636940405985757344

private def cap16_0Codes : List Nat := [
  579358926, 31444032852, 31445095950,
  125927864634, 282578603166]

def cap16_0 : Group.Batch template16.capOK :=
  Packed.capBatch template16 159092 rfl (by decide) cap16_0Codes
    (by decide +kernel)

end TBoards.SpliceFurtherData
