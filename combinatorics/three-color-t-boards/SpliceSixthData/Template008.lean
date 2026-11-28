import SplicePacked

-- Generated from splice_sixth.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceSixthData
open Splice

def template8 : Group where
  k := 5
  pivot := [2, 2, 2, 2, 1, 1, 1, 2, 1, 2, 2]
  caps := []
  tails := []
  upperMask := 152296494730867818914639
  lowerMask := 2265555144498390530497712

private def cap8_0Codes : List Nat := [
  39565808719, 220878597571, 283669410229,
  290614281217, 294086716711, 301031587699]

def cap8_0 : Group.Batch template8.capOK :=
  Packed.capBatch template8 176084 rfl (by decide) cap8_0Codes
    (by decide +kernel)

end TBoards.SpliceSixthData
