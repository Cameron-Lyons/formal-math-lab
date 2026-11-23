import SplicePacked

-- Generated from splice_sixth.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceSixthData
open Splice

def template4 : Group where
  k := 5
  pivot := [2, 2, 2, 2, 0, 1, 2, 2, 1, 2, 2]
  caps := []
  tails := []
  upperMask := 755578812917464974623599
  lowerMask := 1662272826311793374788752

private def cap4_0Codes : List Nat := [
  39565808719, 220878597571, 283669410229,
  290614281217, 294086716711, 301031587699]

def cap4_0 : Group.Batch template4.capOK :=
  Packed.capBatch template4 175436 rfl (by decide) cap4_0Codes
    (by decide +kernel)

end TBoards.SpliceSixthData
