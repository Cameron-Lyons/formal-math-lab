import SplicePacked

-- Generated from splice_further.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceFurtherData
open Splice

def template9 : Group where
  k := 5
  pivot := [2, 0, 1, 2, 2, 2, 0, 1, 2, 2, 0]
  caps := []
  tails := []
  upperMask := 2341624173180475
  lowerMask := 2417851636887634176231876

private def cap9_0Codes : List Nat := [
  3637267590, 5084558580, 11801739528,
  14513190876, 31957170894, 34888826854,
  98979351096, 412000344684]

def cap9_0 : Group.Batch template9.capOK :=
  Packed.capBatch template9 131028 rfl (by decide) cap9_0Codes
    (by decide +kernel)

end TBoards.SpliceFurtherData
