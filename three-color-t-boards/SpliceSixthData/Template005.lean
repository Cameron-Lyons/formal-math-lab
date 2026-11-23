import SplicePacked

-- Generated from splice_sixth.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceSixthData
open Splice

def template5 : Group where
  k := 5
  pivot := [2, 2, 2, 2, 1, 1, 0, 2, 1, 1, 1]
  caps := []
  tails := []
  upperMask := 75560345210752623450959
  lowerMask := 2342291294018505725961392

private def cap5_0Codes : List Nat := [
  39565808719, 220878597571, 283669410229,
  290614281217, 294086716711, 301031587699]

def cap5_0 : Group.Batch template5.capOK :=
  Packed.capBatch template5 175999 rfl (by decide) cap5_0Codes
    (by decide +kernel)

end TBoards.SpliceSixthData
