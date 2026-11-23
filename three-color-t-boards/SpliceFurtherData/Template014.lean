import SplicePacked

-- Generated from splice_further.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceFurtherData
open Splice

def template14 : Group where
  k := 5
  pivot := [0, 2, 1, 0, 2, 2, 0, 0, 0, 0, 2]
  caps := []
  tails := []
  upperMask := 306958595483968665291727
  lowerMask := 2110893043745289684120624

private def cap14_0Codes : List Nat := [
  283669410427, 290614281415, 294086716909,
  301031587897]

def cap14_0 : Group.Batch template14.capOK :=
  Packed.capBatch template14 47873 rfl (by decide) cap14_0Codes
    (by decide +kernel)

end TBoards.SpliceFurtherData
