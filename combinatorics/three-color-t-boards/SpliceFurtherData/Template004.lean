import SplicePacked

-- Generated from splice_further.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceFurtherData
open Splice

def template4 : Group where
  k := 5
  pivot := [2, 0, 1, 0, 1, 1, 0, 0, 0, 2, 0]
  caps := []
  tails := []
  upperMask := 147790126431978921563
  lowerMask := 2417703849102826370490788

private def cap4_0Codes : List Nat := [
  283669410562, 290614281550, 294086717044,
  301031588032]

def cap4_0 : Group.Batch template4.capOK :=
  Packed.capBatch template4 125637 rfl (by decide) cap4_0Codes
    (by decide +kernel)

end TBoards.SpliceFurtherData
