import SplicePacked

-- Generated from splice_further.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceFurtherData
open Splice

def template18 : Group where
  k := 5
  pivot := [2, 2, 2, 2, 0, 1, 1, 0, 0, 2, 2]
  caps := []
  tails := []
  upperMask := 9471070394806702943
  lowerMask := 2417842168158863542709408

private def cap18_0Codes : List Nat := [
  39565808719, 220878597571, 283669410229,
  290614281217, 294086716711, 301031587699]

def cap18_0 : Group.Batch template18.capOK :=
  Packed.capBatch template18 175292 rfl (by decide) cap18_0Codes
    (by decide +kernel)

end TBoards.SpliceFurtherData
