import SplicePacked

-- Generated from splice_sixth.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceSixthData
open Splice

def template26 : Group where
  k := 5
  pivot := [2, 2, 2, 2, 1, 2, 2, 0, 0, 2, 2]
  caps := []
  tails := []
  upperMask := 4727150431918484751055
  lowerMask := 2413124488797339864661296

private def cap26_0Codes : List Nat := [
  39565808717, 220878597569, 283669410227,
  290614281215, 294086716709, 301031587697]

def cap26_0 : Group.Batch template26.capOK :=
  Packed.capBatch template26 176345 rfl (by decide) cap26_0Codes
    (by decide +kernel)

end TBoards.SpliceSixthData
