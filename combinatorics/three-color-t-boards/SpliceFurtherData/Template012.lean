import SplicePacked

-- Generated from splice_further.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceFurtherData
open Splice

def template12 : Group where
  k := 5
  pivot := [2, 2, 1, 0, 2, 1, 1, 0, 0, 2, 1]
  caps := []
  tails := []
  upperMask := 11772691244963339215
  lowerMask := 2417839866538013386073136

private def cap12_0Codes : List Nat := [
  283669410230, 290614281218, 294086716712,
  301031587700]

def cap12_0 : Group.Batch template12.capOK :=
  Packed.capBatch template12 165814 rfl (by decide) cap12_0Codes
    (by decide +kernel)

end TBoards.SpliceFurtherData
