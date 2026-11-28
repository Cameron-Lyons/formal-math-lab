import SplicePacked

-- Generated from splice_further.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceFurtherData
open Splice

def template93 : Group where
  k := 5
  pivot := [2, 1, 2, 0, 2, 1, 2, 0, 2, 2, 1]
  caps := []
  tails := []
  upperMask := 5776511308183323
  lowerMask := 2417851633452747041229028

private def cap93_0Codes : List Nat := [
  297716440087, 324664953625, 329437094095,
  329437094815, 409676182039, 409676182759,
  418550184577, 419577164065]

def cap93_0 : Group.Batch template93.capOK :=
  Packed.capBatch template93 152791 rfl (by decide) cap93_0Codes
    (by decide +kernel)

end TBoards.SpliceFurtherData
