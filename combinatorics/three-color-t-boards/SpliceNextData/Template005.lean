import SplicePacked

-- Generated from splice_next.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceNextData
open Splice

def template5 : Group where
  k := 5
  pivot := [2, 2, 1, 0, 1, 0, 0, 0, 0, 2, 1]
  caps := []
  tails := []
  upperMask := 76336295641455267675
  lowerMask := 2417775302933616894144676

private def cap5_0Codes : List Nat := [
  283669410554, 290614281542, 294086717036,
  301031588024]

def cap5_0 : Group.Batch template5.capOK :=
  Packed.capBatch template5 164761 rfl (by decide) cap5_0Codes
    (by decide +kernel)

end TBoards.SpliceNextData
