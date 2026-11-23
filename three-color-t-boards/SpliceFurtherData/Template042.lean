import SplicePacked

-- Generated from splice_further.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceFurtherData
open Splice

def template42 : Group where
  k := 5
  pivot := [2, 2, 0, 1, 2, 2, 2, 1, 0, 2, 2]
  caps := []
  tails := []
  upperMask := 2535447474091547
  lowerMask := 2417851636693810875320804

private def cap42_0Codes : List Nat := [
  34931860429]

def cap42_0 : Group.Batch template42.capOK :=
  Packed.capBatch template42 161792 rfl (by decide) cap42_0Codes
    (by decide +kernel)

end TBoards.SpliceFurtherData
