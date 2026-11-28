import SplicePacked

-- Generated from splice_next.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceNextData
open Splice

def template13 : Group where
  k := 5
  pivot := [0, 2, 1, 0, 1, 2, 1, 0, 0, 0, 2]
  caps := []
  tails := []
  upperMask := 37788394207593850275819
  lowerMask := 2380063245021664499136532

private def cap13_0Codes : List Nat := [
  283669410283, 290614281271, 294086716765,
  301031587753]

def cap13_0 : Group.Batch template13.capOK :=
  Packed.capBatch template13 47225 rfl (by decide) cap13_0Codes
    (by decide +kernel)

end TBoards.SpliceNextData
