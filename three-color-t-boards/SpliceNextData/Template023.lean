import SplicePacked

-- Generated from splice_next.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceNextData
open Splice

def template23 : Group where
  k := 5
  pivot := [1, 1, 1, 1, 2, 2, 1, 2, 0, 0, 2]
  caps := []
  tails := []
  upperMask := 5312828927858656568143
  lowerMask := 2412538810301399692844208

private def cap23_0Codes : List Nat := [
  39565808719, 220878597571, 283669410229,
  290614281217, 294086716711, 301031587699]

def cap23_0 : Group.Batch template23.capOK :=
  Packed.capBatch template23 89561 rfl (by decide) cap23_0Codes
    (by decide +kernel)

end TBoards.SpliceNextData
