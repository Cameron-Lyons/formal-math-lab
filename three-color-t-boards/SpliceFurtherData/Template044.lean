import SplicePacked

-- Generated from splice_further.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceFurtherData
open Splice

def template44 : Group where
  k := 5
  pivot := [2, 2, 0, 1, 2, 2, 2, 1, 0, 2, 2]
  caps := []
  tails := []
  upperMask := 9290842569848379
  lowerMask := 2417851629938415779563972

private def cap44_0Codes : List Nat := [
  36432603238, 98936481496, 99227711164]

def cap44_0 : Group.Batch template44.capOK :=
  Packed.capBatch template44 161792 rfl (by decide) cap44_0Codes
    (by decide +kernel)

end TBoards.SpliceFurtherData
