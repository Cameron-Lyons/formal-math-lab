import SplicePacked

-- Generated from splice_sixth.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceSixthData
open Splice

def template35 : Group where
  k := 5
  pivot := [0, 0, 0, 0, 1, 2, 0, 0, 1, 0, 0]
  caps := []
  tails := []
  upperMask := 113788831506076855771146
  lowerMask := 2304062807723181493641205

private def cap35_0Codes : List Nat := [
  362091771452, 452748165878, 703796638376,
  707269073870, 714213944858, 717686380352]

def cap35_0 : Group.Batch template35.capOK :=
  Packed.capBatch template35 1224 rfl (by decide) cap35_0Codes
    (by decide +kernel)

end TBoards.SpliceSixthData
