import SplicePacked

-- Generated from splice_pal.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SplicePalData
open Splice

def template0 : Group where
  k := 5
  pivot := [2, 0, 1, 1, 0, 2, 0, 1, 1, 0, 2]
  caps := []
  tails := []
  upperMask := 75228774485769910930
  lowerMask := 2417776410454772579501421

private def cap0_0Codes : List Nat := [
  136374320589, 136384000245]

def cap0_0 : Group.Batch template0.capOK :=
  Packed.capBatch template0 127370 rfl (by decide) cap0_0Codes
    (by decide +kernel)

end TBoards.SplicePalData
