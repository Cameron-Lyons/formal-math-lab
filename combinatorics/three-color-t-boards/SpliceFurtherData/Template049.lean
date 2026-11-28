import SplicePacked

-- Generated from splice_further.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceFurtherData
open Splice

def template49 : Group where
  k := 5
  pivot := [2, 2, 0, 1, 2, 2, 2, 1, 0, 2, 2]
  caps := []
  tails := []
  upperMask := 13530250137321275
  lowerMask := 2417851625699008212091076

private def cap49_0Codes : List Nat := [
  106287688593]

def cap49_0 : Group.Batch template49.capOK :=
  Packed.capBatch template49 161792 rfl (by decide) cap49_0Codes
    (by decide +kernel)

end TBoards.SpliceFurtherData
