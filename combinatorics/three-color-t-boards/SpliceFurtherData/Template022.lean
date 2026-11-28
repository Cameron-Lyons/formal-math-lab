import SplicePacked

-- Generated from splice_further.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceFurtherData
open Splice

def template22 : Group where
  k := 5
  pivot := [0, 2, 1, 1, 1, 0, 1, 1, 0, 0, 2]
  caps := []
  tails := []
  upperMask := 83177544812398393311
  lowerMask := 2417768461684445951019040

private def cap22_0Codes : List Nat := [
  283669410229, 290614281217, 294086716711,
  301031587699]

def cap22_0 : Group.Batch template22.capOK :=
  Packed.capBatch template22 48953 rfl (by decide) cap22_0Codes
    (by decide +kernel)

end TBoards.SpliceFurtherData
