import SplicePacked

-- Generated from splice_further.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceFurtherData
open Splice

def template68 : Group where
  k := 5
  pivot := [2, 2, 0, 1, 2, 2, 2, 1, 0, 2, 2]
  caps := []
  tails := []
  upperMask := 9097057941863963
  lowerMask := 2417851630132200407548388

private def cap68_0Codes : List Nat := [
  297716440087]

def cap68_0 : Group.Batch template68.capOK :=
  Packed.capBatch template68 161792 rfl (by decide) cap68_0Codes
    (by decide +kernel)

end TBoards.SpliceFurtherData
