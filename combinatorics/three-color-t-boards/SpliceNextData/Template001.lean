import SplicePacked

-- Generated from splice_next.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceNextData
open Splice

def template1 : Group where
  k := 5
  pivot := [2, 0, 1, 0, 1, 1, 1, 0, 0, 2, 1]
  caps := []
  tails := []
  upperMask := 9459811362368403423
  lowerMask := 2417842179417895981008928

private def cap1_0Codes : List Nat := [
  283669410228, 290614281216, 294086716710,
  301031587698]

def cap1_0 : Group.Batch template1.capOK :=
  Packed.capBatch template1 125719 rfl (by decide) cap1_0Codes
    (by decide +kernel)

end TBoards.SpliceNextData
