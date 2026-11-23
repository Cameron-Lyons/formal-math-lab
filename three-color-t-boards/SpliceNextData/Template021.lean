import SplicePacked

-- Generated from splice_next.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceNextData
open Splice

def template21 : Group where
  k := 5
  pivot := [2, 2, 2, 2, 1, 2, 0, 2, 0, 0, 2]
  caps := []
  tails := []
  upperMask := 4723695045104368911183
  lowerMask := 2413127944184153980501168

private def cap21_0Codes : List Nat := [
  39565808719, 220878597571, 283669410229,
  290614281217, 294086716711, 301031587699]

def cap21_0 : Group.Batch template21.capOK :=
  Packed.capBatch template21 176231 rfl (by decide) cap21_0Codes
    (by decide +kernel)

end TBoards.SpliceNextData
