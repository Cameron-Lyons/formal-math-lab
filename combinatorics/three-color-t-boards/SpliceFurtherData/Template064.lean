import SplicePacked

-- Generated from splice_further.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceFurtherData
open Splice

def template64 : Group where
  k := 5
  pivot := [2, 2, 0, 1, 2, 2, 2, 1, 0, 2, 2]
  caps := []
  tails := []
  upperMask := 13530254432288539
  lowerMask := 2417851625699003917123812

private def cap64_0Codes : List Nat := [
  286108231212]

def cap64_0 : Group.Batch template64.capOK :=
  Packed.capBatch template64 161792 rfl (by decide) cap64_0Codes
    (by decide +kernel)

end TBoards.SpliceFurtherData
