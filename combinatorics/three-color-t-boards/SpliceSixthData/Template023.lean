import SplicePacked

-- Generated from splice_sixth.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceSixthData
open Splice

def template23 : Group where
  k := 5
  pivot := [0, 0, 1, 2, 2, 0, 2, 2, 1, 0, 0]
  caps := []
  tails := []
  upperMask := 20226898534621776517682
  lowerMask := 2397624740694636572894669

private def cap23_0Codes : List Nat := [
  169047361377, 169434250425]

def cap23_0 : Group.Batch template23.capOK :=
  Packed.capBatch template23 12618 rfl (by decide) cap23_0Codes
    (by decide +kernel)

end TBoards.SpliceSixthData
