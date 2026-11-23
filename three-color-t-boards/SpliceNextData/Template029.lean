import SplicePacked

-- Generated from splice_next.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceNextData
open Splice

def template29 : Group where
  k := 5
  pivot := [2, 2, 2, 2, 1, 1, 0, 1, 1, 2, 2]
  caps := []
  tails := []
  upperMask := 295611793877265291087
  lowerMask := 2417556027435381084121264

private def cap29_0Codes : List Nat := [
  39565808719, 220878597571, 283669410229,
  290614281217, 294086716711, 301031587699]

def cap29_0 : Group.Batch template29.capOK :=
  Packed.capBatch template29 175976 rfl (by decide) cap29_0Codes
    (by decide +kernel)

end TBoards.SpliceNextData
