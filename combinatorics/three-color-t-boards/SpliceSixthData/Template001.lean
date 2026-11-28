import SplicePacked

-- Generated from splice_sixth.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceSixthData
open Splice

def template1 : Group where
  k := 5
  pivot := [2, 2, 2, 2, 1, 1, 0, 2, 0, 2, 2]
  caps := []
  tails := []
  upperMask := 18890794493747122150223
  lowerMask := 2398960844735511227262128

private def cap1_0Codes : List Nat := [
  39565808719, 220878597571, 283669410229,
  290614281217, 294086716711, 301031587699]

def cap1_0 : Group.Batch template1.capOK :=
  Packed.capBatch template1 175994 rfl (by decide) cap1_0Codes
    (by decide +kernel)

end TBoards.SpliceSixthData
