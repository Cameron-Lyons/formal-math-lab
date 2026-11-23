import SplicePacked

-- Generated from splice_further.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceFurtherData
open Splice

def template73 : Group where
  k := 5
  pivot := [2, 2, 0, 1, 2, 2, 2, 1, 0, 2, 2]
  caps := []
  tails := []
  upperMask := 6774889401302555
  lowerMask := 2417851632454368948109796

private def cap73_0Codes : List Nat := [
  329437094815, 409676182759, 418550184577]

def cap73_0 : Group.Batch template73.capOK :=
  Packed.capBatch template73 161792 rfl (by decide) cap73_0Codes
    (by decide +kernel)

end TBoards.SpliceFurtherData
