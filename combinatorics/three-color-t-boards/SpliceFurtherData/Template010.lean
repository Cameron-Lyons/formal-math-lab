import SplicePacked

-- Generated from splice_further.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceFurtherData
open Splice

def template10 : Group where
  k := 5
  pivot := [1, 2, 2, 2, 1, 1, 2, 2, 1, 1, 2]
  caps := []
  tails := []
  upperMask := 14095399132493339
  lowerMask := 2417851625133859216919012

private def cap10_0Codes : List Nat := [
  34930753105, 136517282149, 137536073509,
  285966010335, 285980687239, 324664953625,
  418559746141, 420007037131]

def cap10_0 : Group.Batch template10.capOK :=
  Packed.capBatch template10 117113 rfl (by decide) cap10_0Codes
    (by decide +kernel)

end TBoards.SpliceFurtherData
