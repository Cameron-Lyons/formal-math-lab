import SplicePacked

-- Generated from splice_sixth.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceSixthData
open Splice

def template30 : Group where
  k := 5
  pivot := [2, 2, 0, 2, 1, 1, 1, 0, 0, 2, 2]
  caps := []
  tails := []
  upperMask := 9462203932976886735
  lowerMask := 2417842177025325372525616

private def cap30_0Codes : List Nat := [
  283669410229, 290614281217, 294086716711,
  301031587699]

def cap30_0 : Group.Batch template30.capOK :=
  Packed.capBatch template30 162899 rfl (by decide) cap30_0Codes
    (by decide +kernel)

end TBoards.SpliceSixthData
