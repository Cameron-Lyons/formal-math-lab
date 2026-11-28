import SplicePacked

-- Generated from splice_further.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceFurtherData
open Splice

def template51 : Group where
  k := 5
  pivot := [2, 2, 0, 1, 2, 2, 2, 1, 0, 2, 2]
  caps := []
  tails := []
  upperMask := 2324341243131419
  lowerMask := 2417851636904917106280932

private def cap51_0Codes : List Nat := [
  136517282149]

def cap51_0 : Group.Batch template51.capOK :=
  Packed.capBatch template51 161792 rfl (by decide) cap51_0Codes
    (by decide +kernel)

end TBoards.SpliceFurtherData
