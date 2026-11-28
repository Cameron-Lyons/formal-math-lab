import SplicePacked

-- Generated from splice_further.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceFurtherData
open Splice

def template25 : Group where
  k := 5
  pivot := [2, 2, 0, 0, 2, 0, 2, 0, 0, 2, 2]
  caps := []
  tails := []
  upperMask := 2429589850961759
  lowerMask := 2417851636799668498450592

private def cap25_0Codes : List Nat := [
  140031169419, 381394545231, 388755123357,
  388755477867, 418588096059]

def cap25_0 : Group.Batch template25.capOK :=
  Packed.capBatch template25 159092 rfl (by decide) cap25_0Codes
    (by decide +kernel)

end TBoards.SpliceFurtherData
