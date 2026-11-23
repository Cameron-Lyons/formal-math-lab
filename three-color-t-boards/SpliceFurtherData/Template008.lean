import SplicePacked

-- Generated from splice_further.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceFurtherData
open Splice

def template8 : Group where
  k := 5
  pivot := [1, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2]
  caps := []
  tails := []
  upperMask := 1719296250181147
  lowerMask := 2417851637509962099231204

private def cap8_0Codes : List Nat := [
  287515448977, 324664953625, 329437094095,
  329437094815, 391687133827, 409131113845,
  409676182039, 409676182759, 411842565193,
  418550184577, 419577164065]

def cap8_0 : Group.Batch template8.capOK :=
  Packed.capBatch template8 109238 rfl (by decide) cap8_0Codes
    (by decide +kernel)

end TBoards.SpliceFurtherData
