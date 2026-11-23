import SplicePacked

-- Generated from splice_sixth.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceSixthData
open Splice

def template28 : Group where
  k := 5
  pivot := [1, 0, 1, 0, 2, 1, 1, 0, 2, 1, 0]
  caps := []
  tails := []
  upperMask := 39366246162902556623
  lowerMask := 2417812272983095446855728

private def cap28_0Codes : List Nat := [
  283669410229, 290614281217, 294086716711,
  301031587699]

def cap28_0 : Group.Batch template28.capOK :=
  Packed.capBatch template28 67413 rfl (by decide) cap28_0Codes
    (by decide +kernel)

end TBoards.SpliceSixthData
