import SplicePacked

-- Generated from splice_next.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceNextData
open Splice

def template28 : Group where
  k := 5
  pivot := [2, 2, 2, 2, 1, 1, 0, 2, 1, 2, 2]
  caps := []
  tails := []
  upperMask := 151118208953159621286735
  lowerMask := 2266733430276098728125616

private def cap28_0Codes : List Nat := [
  39565808719, 220878597571, 283669410229,
  290614281217, 294086716711, 301031587699]

def cap28_0 : Group.Batch template28.capOK :=
  Packed.capBatch template28 176003 rfl (by decide) cap28_0Codes
    (by decide +kernel)

end TBoards.SpliceNextData
