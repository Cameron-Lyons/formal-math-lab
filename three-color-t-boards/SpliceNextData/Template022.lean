import SplicePacked

-- Generated from splice_next.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceNextData
open Splice

def template22 : Group where
  k := 5
  pivot := [2, 2, 2, 2, 1, 1, 2, 0, 0, 2, 2]
  caps := []
  tails := []
  upperMask := 4722614181227617633103
  lowerMask := 2413129025048030731779248

private def cap22_0Codes : List Nat := [
  39565808719, 220878597571, 283669410229,
  290614281217, 294086716711, 301031587699]

def cap22_0 : Group.Batch template22.capOK :=
  Packed.capBatch template22 176102 rfl (by decide) cap22_0Codes
    (by decide +kernel)

end TBoards.SpliceNextData
