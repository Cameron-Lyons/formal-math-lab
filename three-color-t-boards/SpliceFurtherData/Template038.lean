import SplicePacked

-- Generated from splice_further.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceFurtherData
open Splice

def template38 : Group where
  k := 5
  pivot := [2, 2, 0, 1, 2, 2, 2, 1, 0, 2, 2]
  caps := []
  tails := []
  upperMask := 2552730422361883
  lowerMask := 2417851636676527927050468

private def cap38_0Codes : List Nat := [
  31445095950]

def cap38_0 : Group.Batch template38.capOK :=
  Packed.capBatch template38 161792 rfl (by decide) cap38_0Codes
    (by decide +kernel)

end TBoards.SpliceFurtherData
