import SplicePacked

-- Generated from splice_next.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceNextData
open Splice

def template18 : Group where
  k := 5
  pivot := [2, 2, 2, 2, 1, 2, 2, 0, 0, 2, 2]
  caps := []
  tails := []
  upperMask := 4722614181227638686543
  lowerMask := 2413129025048030710725808

private def cap18_0Codes : List Nat := [
  39565808719, 220878597571, 283669410229,
  290614281217, 294086716711, 301031587699]

def cap18_0 : Group.Batch template18.capOK :=
  Packed.capBatch template18 176345 rfl (by decide) cap18_0Codes
    (by decide +kernel)

end TBoards.SpliceNextData
