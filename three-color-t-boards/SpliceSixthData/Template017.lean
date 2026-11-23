import SplicePacked

-- Generated from splice_sixth.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceSixthData
open Splice

def template17 : Group where
  k := 5
  pivot := [2, 2, 2, 2, 1, 2, 2, 0, 0, 2, 2]
  caps := []
  tails := []
  upperMask := 4722614181227638686543
  lowerMask := 2413129025048030710725808

private def cap17_0Codes : List Nat := [
  39565808719, 220878597571, 283669410229,
  290614281217, 294086716711, 301031587699]

def cap17_0 : Group.Batch template17.capOK :=
  Packed.capBatch template17 176345 rfl (by decide) cap17_0Codes
    (by decide +kernel)

end TBoards.SpliceSixthData
