import SplicePacked

-- Generated from splice_sixth.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceSixthData
open Splice

def template16 : Group where
  k := 5
  pivot := [1, 1, 1, 1, 0, 1, 2, 0, 0, 2, 1]
  caps := []
  tails := []
  upperMask := 4722605175110589790063
  lowerMask := 2413129034054147759622288

private def cap16_0Codes : List Nat := [
  39565808719, 220878597571, 283669410229,
  290614281217, 294086716711, 301031587699]

def cap16_0 : Group.Batch template16.capOK :=
  Packed.capBatch template16 87892 rfl (by decide) cap16_0Codes
    (by decide +kernel)

end TBoards.SpliceSixthData
