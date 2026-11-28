import SplicePacked

-- Generated from splice_further.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceFurtherData
open Splice

def template11 : Group where
  k := 5
  pivot := [2, 0, 1, 0, 1, 1, 0, 0, 0, 2, 1]
  caps := []
  tails := []
  upperMask := 147790126414799052507
  lowerMask := 2417703849102843550359844

private def cap11_0Codes : List Nat := [
  283669410561, 290614281549, 294086717043,
  301031588031]

def cap11_0 : Group.Batch template11.capOK :=
  Packed.capBatch template11 125638 rfl (by decide) cap11_0Codes
    (by decide +kernel)

end TBoards.SpliceFurtherData
