import SplicePacked

-- Generated from splice_pal.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SplicePalData
open Splice

def template8 : Group where
  k := 5
  pivot := [0, 2, 1, 1, 2, 2, 2, 1, 1, 2, 0]
  caps := []
  tails := []
  upperMask := 85482226427452117805184
  lowerMask := 2332369412801806231607167

private def cap8_0Codes : List Nat := [
  137694993679, 138081882727]

def cap8_0 : Group.Batch template8.capOK :=
  Packed.capBatch template8 50262 rfl (by decide) cap8_0Codes
    (by decide +kernel)

end TBoards.SplicePalData
