import SplicePacked

-- Generated from splice_sixth.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceSixthData
open Splice

def template7 : Group where
  k := 5
  pivot := [2, 2, 2, 2, 1, 1, 2, 2, 1, 2, 2]
  caps := []
  tails := []
  upperMask := 755578812917464995087183
  lowerMask := 1662272826311793354325168

private def cap7_0Codes : List Nat := [
  39565808719, 220878597571, 283669410229,
  290614281217, 294086716711, 301031587699]

def cap7_0 : Group.Batch template7.capOK :=
  Packed.capBatch template7 176165 rfl (by decide) cap7_0Codes
    (by decide +kernel)

end TBoards.SpliceSixthData
