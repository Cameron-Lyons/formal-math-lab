import SplicePacked

-- Generated from splice_next.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceNextData
open Splice

def template8 : Group where
  k := 5
  pivot := [0, 2, 1, 0, 1, 1, 0, 0, 0, 0, 2]
  caps := []
  tails := []
  upperMask := 147736364702299856603
  lowerMask := 2417703902864556049555748

private def cap8_0Codes : List Nat := [
  283669410562, 290614281550, 294086717044,
  301031588032]

def cap8_0 : Group.Batch template8.capOK :=
  Packed.capBatch template8 46901 rfl (by decide) cap8_0Codes
    (by decide +kernel)

end TBoards.SpliceNextData
