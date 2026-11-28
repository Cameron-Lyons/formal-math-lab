import SplicePacked

-- Generated from splice_next.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceNextData
open Splice

def template20 : Group where
  k := 5
  pivot := [2, 2, 2, 2, 1, 2, 0, 2, 0, 2, 2]
  caps := []
  tails := []
  upperMask := 18890794493747127419727
  lowerMask := 2398960844735511221992624

private def cap20_0Codes : List Nat := [
  39565808719, 220878597571, 283669410229,
  290614281217, 294086716711, 301031587699]

def cap20_0 : Group.Batch template20.capOK :=
  Packed.capBatch template20 176237 rfl (by decide) cap20_0Codes
    (by decide +kernel)

end TBoards.SpliceNextData
