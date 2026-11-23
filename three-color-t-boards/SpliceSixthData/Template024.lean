import SplicePacked

-- Generated from splice_sixth.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceSixthData
open Splice

def template24 : Group where
  k := 5
  pivot := [2, 2, 2, 2, 1, 2, 1, 0, 0, 2, 2]
  caps := []
  tails := []
  upperMask := 13863205898675360463
  lowerMask := 2417837776023359674051888

private def cap24_0Codes : List Nat := [
  36079024316, 126735418742, 129157722446,
  283655061320, 287127496814, 294072367802,
  297544803296]

def cap24_0 : Group.Batch template24.capOK :=
  Packed.capBatch template24 176264 rfl (by decide) cap24_0Codes
    (by decide +kernel)

end TBoards.SpliceSixthData
