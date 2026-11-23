import SplicePacked

-- Generated from splice_further.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceFurtherData
open Splice

def template76 : Group where
  k := 5
  pivot := [2, 2, 0, 1, 2, 2, 2, 1, 0, 2, 2]
  caps := []
  tails := []
  upperMask := 13530525015226171
  lowerMask := 2417851625698733334186180

private def cap76_0Codes : List Nat := [
  388726771332]

def cap76_0 : Group.Batch template76.capOK :=
  Packed.capBatch template76 161792 rfl (by decide) cap76_0Codes
    (by decide +kernel)

end TBoards.SpliceFurtherData
