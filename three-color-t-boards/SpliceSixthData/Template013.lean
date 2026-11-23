import SplicePacked

-- Generated from splice_sixth.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceSixthData
open Splice

def template13 : Group where
  k := 5
  pivot := [2, 2, 2, 2, 0, 1, 2, 0, 2, 0, 2]
  caps := []
  tails := []
  upperMask := 18890794634450230346607
  lowerMask := 2398960844594808119065744

private def cap13_0Codes : List Nat := [
  39565808719, 220878597571, 283669410229,
  290614281217, 294086716711, 301031587699]

def cap13_0 : Group.Batch template13.capOK :=
  Packed.capBatch template13 175385 rfl (by decide) cap13_0Codes
    (by decide +kernel)

end TBoards.SpliceSixthData
