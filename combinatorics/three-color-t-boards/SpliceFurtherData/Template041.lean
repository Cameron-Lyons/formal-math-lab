import SplicePacked

-- Generated from splice_further.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceFurtherData
open Splice

def template41 : Group where
  k := 5
  pivot := [2, 2, 0, 1, 2, 2, 2, 1, 0, 2, 2]
  caps := []
  tails := []
  upperMask := 2341899069306651
  lowerMask := 2417851636887359280105700

private def cap41_0Codes : List Nat := [
  34927453857]

def cap41_0 : Group.Batch template41.capOK :=
  Packed.capBatch template41 161792 rfl (by decide) cap41_0Codes
    (by decide +kernel)

end TBoards.SpliceFurtherData
