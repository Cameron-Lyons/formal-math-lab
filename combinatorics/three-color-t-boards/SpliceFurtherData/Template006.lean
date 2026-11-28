import SplicePacked

-- Generated from splice_further.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceFurtherData
open Splice

def template6 : Group where
  k := 5
  pivot := [2, 2, 2, 2, 0, 0, 2, 2, 0, 2, 2]
  caps := []
  tails := []
  upperMask := 11436814422259487
  lowerMask := 2417851627792443927152864

private def cap6_0Codes : List Nat := [
  34932214957, 283656168895, 287515448977,
  419577124701, 422419074339]

def cap6_0 : Group.Batch template6.capOK :=
  Packed.capBatch template6 175184 rfl (by decide) cap6_0Codes
    (by decide +kernel)

end TBoards.SpliceFurtherData
