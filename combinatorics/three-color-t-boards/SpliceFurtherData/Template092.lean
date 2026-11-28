import SplicePacked

-- Generated from splice_further.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceFurtherData
open Splice

def template92 : Group where
  k := 5
  pivot := [2, 2, 1, 0, 2, 2, 1, 2, 1, 2, 2]
  caps := []
  tails := []
  upperMask := 5631667865859611
  lowerMask := 2417851633597590483552740

private def cap92_0Codes : List Nat := [
  3635851296, 11643958578, 137593264602,
  137663972442, 286108231212, 388727834916]

def cap92_0 : Group.Batch template92.capOK :=
  Packed.capBatch template92 166121 rfl (by decide) cap92_0Codes
    (by decide +kernel)

end TBoards.SpliceFurtherData
