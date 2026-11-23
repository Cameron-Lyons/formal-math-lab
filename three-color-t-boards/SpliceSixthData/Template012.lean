import SplicePacked

-- Generated from splice_sixth.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceSixthData
open Splice

def template12 : Group where
  k := 5
  pivot := [1, 1, 1, 1, 0, 2, 1, 2, 0, 0, 2]
  caps := []
  tails := []
  upperMask := 5312828927858622872527
  lowerMask := 2412538810301399726539824

private def cap12_0Codes : List Nat := [
  39565808719, 220878597571, 283669410229,
  290614281217, 294086716711, 301031587699]

def cap12_0 : Group.Batch template12.capOK :=
  Packed.capBatch template12 88103 rfl (by decide) cap12_0Codes
    (by decide +kernel)

end TBoards.SpliceSixthData
