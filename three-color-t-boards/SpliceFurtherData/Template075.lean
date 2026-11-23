import SplicePacked

-- Generated from splice_further.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceFurtherData
open Splice

def template75 : Group where
  k := 5
  pivot := [2, 2, 0, 1, 2, 2, 2, 1, 0, 2, 2]
  caps := []
  tails := []
  upperMask := 11278454635380507
  lowerMask := 2417851627950803714031844

private def cap75_0Codes : List Nat := [
  388713551616]

def cap75_0 : Group.Batch template75.capOK :=
  Packed.capBatch template75 161792 rfl (by decide) cap75_0Codes
    (by decide +kernel)

end TBoards.SpliceFurtherData
