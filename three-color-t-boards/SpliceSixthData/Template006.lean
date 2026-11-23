import SplicePacked

-- Generated from splice_sixth.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceSixthData
open Splice

def template6 : Group where
  k := 5
  pivot := [2, 2, 2, 2, 1, 1, 2, 2, 0, 2, 2]
  caps := []
  tails := []
  upperMask := 321121096475899809121103
  lowerMask := 2096730542753358540291248

private def cap6_0Codes : List Nat := [
  39565808719, 220878597571, 283669410229,
  290614281217, 294086716711, 301031587699]

def cap6_0 : Group.Batch template6.capOK :=
  Packed.capBatch template6 176156 rfl (by decide) cap6_0Codes
    (by decide +kernel)

end TBoards.SpliceSixthData
