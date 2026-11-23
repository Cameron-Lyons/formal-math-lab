import SplicePacked

-- Generated from splice_further.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceFurtherData
open Splice

def template2 : Group where
  k := 5
  pivot := [0, 2, 1, 1, 0, 2, 0, 0, 0, 0, 2]
  caps := []
  tails := []
  upperMask := 4728293783290955176655
  lowerMask := 2413123345445967394235696

private def cap2_0Codes : List Nat := [
  283669410427, 290614281415, 294086716909,
  301031587897]

def cap2_0 : Group.Batch template2.capOK :=
  Packed.capBatch template2 48602 rfl (by decide) cap2_0Codes
    (by decide +kernel)

end TBoards.SpliceFurtherData
