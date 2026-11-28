import SplicePacked

-- Generated from splice_next.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceNextData
open Splice

def template27 : Group where
  k := 5
  pivot := [2, 0, 1, 2, 1, 2, 1, 2, 0, 0, 1]
  caps := []
  tails := []
  upperMask := 37199441233032763
  lowerMask := 2417851602029817116379588

private def cap27_0Codes : List Nat := [
  34927427615, 36432485159, 46922522729,
  55848134019, 129570809657, 137577500411,
  137578916939, 139988116355, 139988471081,
  285966338333, 296382226991, 376622732327,
  388197517955, 388712070293, 388713487253]

def cap27_0 : Group.Batch template27.capOK :=
  Packed.capBatch template27 130384 rfl (by decide) cap27_0Codes
    (by decide +kernel)

end TBoards.SpliceNextData
