import SplicePacked

-- Generated from splice_next.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceNextData
open Splice

def template25 : Group where
  k := 5
  pivot := [2, 2, 2, 2, 0, 2, 1, 2, 1, 2, 2]
  caps := []
  tails := []
  upperMask := 152296494730867807355855
  lowerMask := 2265555144498390542056496

private def cap25_0Codes : List Nat := [
  39565808719, 220878597571, 283669410229,
  290614281217, 294086716711, 301031587699]

def cap25_0 : Group.Batch template25.capOK :=
  Packed.capBatch template25 175598 rfl (by decide) cap25_0Codes
    (by decide +kernel)

end TBoards.SpliceNextData
