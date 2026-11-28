import SplicePacked

-- Generated from splice_further.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceFurtherData
open Splice

def template3 : Group where
  k := 5
  pivot := [2, 2, 1, 0, 1, 1, 1, 0, 0, 2, 2]
  caps := []
  tails := []
  upperMask := 9462344670477825887
  lowerMask := 2417842176884587871586464

private def cap3_0Codes : List Nat := [
  283669410229, 290614281217, 294086716711,
  301031587699]

def cap3_0 : Group.Batch template3.capOK :=
  Packed.capBatch template3 165086 rfl (by decide) cap3_0Codes
    (by decide +kernel)

end TBoards.SpliceFurtherData
