import SplicePacked

-- Generated from splice_sixth.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceSixthData
open Splice

def template10 : Group where
  k := 5
  pivot := [2, 0, 1, 1, 0, 2, 0, 1, 1, 0, 2]
  caps := []
  tails := []
  upperMask := 75228774485769910930
  lowerMask := 2417776410454772579501421

private def cap10_0Codes : List Nat := [
  136374438681]

def cap10_0 : Group.Batch template10.capOK :=
  Packed.capBatch template10 127370 rfl (by decide) cap10_0Codes
    (by decide +kernel)

end TBoards.SpliceSixthData
