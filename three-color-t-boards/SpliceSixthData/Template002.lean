import SplicePacked

-- Generated from splice_sixth.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceSixthData
open Splice

def template2 : Group where
  k := 5
  pivot := [2, 2, 2, 2, 0, 1, 2, 2, 2, 1, 1]
  caps := []
  tails := []
  upperMask := 1813388905625623269868399
  lowerMask := 604462733603635079543952

private def cap2_0Codes : List Nat := [
  39565808719, 220878597571, 283669410229,
  290614281217, 294086716711, 301031587699]

def cap2_0 : Group.Batch template2.capOK :=
  Packed.capBatch template2 175441 rfl (by decide) cap2_0Codes
    (by decide +kernel)

end TBoards.SpliceSixthData
