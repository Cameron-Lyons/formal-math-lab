import SplicePacked

-- Generated from splice_next.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceNextData
open Splice

def template24 : Group where
  k := 5
  pivot := [0, 1, 0, 2, 1, 2, 1, 2, 1, 0, 2]
  caps := []
  tails := []
  upperMask := 145532393479028379
  lowerMask := 2417851493696864870383972

private def cap24_0Codes : List Nat := [
  31960365615, 34916417319, 46922535849,
  129570822777, 137577867321, 137578930059,
  139988129475, 139989546579, 285964933773,
  296382240111, 376622745447, 387167715579,
  387196400271, 388712083413, 388713500373]

def cap24_0 : Group.Batch template24.capOK :=
  Packed.capBatch template24 25418 rfl (by decide) cap24_0Codes
    (by decide +kernel)

end TBoards.SpliceNextData
