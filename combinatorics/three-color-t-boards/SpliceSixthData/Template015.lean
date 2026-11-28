import SplicePacked

-- Generated from splice_sixth.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceSixthData
open Splice

def template15 : Group where
  k := 5
  pivot := [2, 2, 2, 2, 0, 1, 2, 1, 1, 2, 2]
  caps := []
  tails := []
  upperMask := 75853187289415416611695
  lowerMask := 2341998451939842932800656

private def cap15_0Codes : List Nat := [
  39565808719, 220878597571, 283669410229,
  290614281217, 294086716711, 301031587699]

def cap15_0 : Group.Batch template15.capOK :=
  Packed.capBatch template15 175409 rfl (by decide) cap15_0Codes
    (by decide +kernel)

end TBoards.SpliceSixthData
