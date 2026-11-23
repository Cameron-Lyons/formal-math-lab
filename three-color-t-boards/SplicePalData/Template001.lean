import SplicePacked

-- Generated from splice_pal.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SplicePalData
open Splice

def template1 : Group where
  k := 5
  pivot := [0, 2, 1, 1, 0, 0, 0, 1, 1, 2, 0]
  caps := []
  tails := []
  upperMask := 9703276474707485452416
  lowerMask := 2408148362754550863959935

private def cap1_0Codes : List Nat := [
  137694993679, 138081882727]

def cap1_0 : Group.Batch template1.capOK :=
  Packed.capBatch template1 48156 rfl (by decide) cap1_0Codes
    (by decide +kernel)

end TBoards.SplicePalData
