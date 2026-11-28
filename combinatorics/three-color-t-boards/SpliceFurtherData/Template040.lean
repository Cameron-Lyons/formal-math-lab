import SplicePacked

-- Generated from splice_further.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceFurtherData
open Splice

def template40 : Group where
  k := 5
  pivot := [2, 2, 0, 1, 2, 2, 2, 1, 0, 2, 2]
  caps := []
  tails := []
  upperMask := 300964985191963
  lowerMask := 2417851638928293364220388

private def cap40_0Codes : List Nat := [
  34889181364, 283613135302]

def cap40_0 : Group.Batch template40.capOK :=
  Packed.capBatch template40 161792 rfl (by decide) cap40_0Codes
    (by decide +kernel)

end TBoards.SpliceFurtherData
