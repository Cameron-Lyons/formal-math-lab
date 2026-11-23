import SplicePacked

-- Generated from splice_further.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceFurtherData
open Splice

def template21 : Group where
  k := 5
  pivot := [2, 2, 2, 0, 2, 1, 1, 0, 0, 2, 2]
  caps := []
  tails := []
  upperMask := 9464314995353588687
  lowerMask := 2417842174914262995823664

private def cap21_0Codes : List Nat := [
  283669410229, 290614281217, 294086716711,
  301031587699]

def cap21_0 : Group.Batch template21.capOK :=
  Packed.capBatch template21 172376 rfl (by decide) cap21_0Codes
    (by decide +kernel)

end TBoards.SpliceFurtherData
