import SplicePacked

-- Generated from splice_sixth.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceSixthData
open Splice

def template3 : Group where
  k := 5
  pivot := [2, 2, 2, 2, 1, 2, 2, 0, 0, 1, 0]
  caps := []
  tails := []
  upperMask := 4722578152397333726031
  lowerMask := 2413129061076861015686320

private def cap3_0Codes : List Nat := [
  39565808719, 220878597571, 283669410229,
  290614281217, 294086716711, 301031587699]

def cap3_0 : Group.Batch template3.capOK :=
  Packed.capBatch template3 176340 rfl (by decide) cap3_0Codes
    (by decide +kernel)

end TBoards.SpliceSixthData
