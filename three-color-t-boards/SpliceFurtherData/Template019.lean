import SplicePacked

-- Generated from splice_further.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceFurtherData
open Splice

def template19 : Group where
  k := 5
  pivot := [2, 2, 2, 2, 1, 1, 1, 0, 0, 2, 2]
  caps := []
  tails := []
  upperMask := 9471070394827158351
  lowerMask := 2417842168158863522254000

private def cap19_0Codes : List Nat := [
  39565808719, 220878597571, 283669410229,
  290614281217, 294086716711, 301031587699]

def cap19_0 : Group.Batch template19.capOK :=
  Packed.capBatch template19 176021 rfl (by decide) cap19_0Codes
    (by decide +kernel)

end TBoards.SpliceFurtherData
