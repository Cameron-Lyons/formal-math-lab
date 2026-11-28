import SplicePacked

-- Generated from splice_next.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceNextData
open Splice

def template11 : Group where
  k := 5
  pivot := [2, 2, 1, 0, 1, 1, 1, 0, 0, 2, 2]
  caps := []
  tails := []
  upperMask := 9462344670477825887
  lowerMask := 2417842176884587871586464

private def cap11_0Codes : List Nat := [
  283669410229, 290614281217, 294086716711,
  301031587699]

def cap11_0 : Group.Batch template11.capOK :=
  Packed.capBatch template11 165086 rfl (by decide) cap11_0Codes
    (by decide +kernel)

end TBoards.SpliceNextData
