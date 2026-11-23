import SplicePacked

-- Generated from splice_pal.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SplicePalData
open Splice

def template6 : Group where
  k := 5
  pivot := [0, 0, 1, 2, 2, 0, 2, 2, 1, 0, 0]
  caps := []
  tails := []
  upperMask := 20226898534621776517682
  lowerMask := 2397624740694636572894669

private def cap6_0Codes : List Nat := [
  169047322013, 169076046069, 169434211061,
  169462935117]

def cap6_0 : Group.Batch template6.capOK :=
  Packed.capBatch template6 12618 rfl (by decide) cap6_0Codes
    (by decide +kernel)

end TBoards.SplicePalData
