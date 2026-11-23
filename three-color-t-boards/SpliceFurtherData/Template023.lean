import SplicePacked

-- Generated from splice_further.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceFurtherData
open Splice

def template23 : Group where
  k := 5
  pivot := [0, 2, 1, 1, 0, 1, 1, 1, 0, 0, 2]
  caps := []
  tails := []
  upperMask := 83177544812398393311
  lowerMask := 2417768461684445951019040

private def cap23_0Codes : List Nat := [
  283669410229, 290614281217, 294086716711,
  301031587699]

def cap23_0 : Group.Batch template23.capOK :=
  Packed.capBatch template23 48467 rfl (by decide) cap23_0Codes
    (by decide +kernel)

end TBoards.SpliceFurtherData
