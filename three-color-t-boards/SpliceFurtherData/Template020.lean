import SplicePacked

-- Generated from splice_further.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceFurtherData
open Splice

def template20 : Group where
  k := 5
  pivot := [0, 2, 2, 0, 2, 0, 0, 2, 2, 0, 2]
  caps := []
  tails := []
  upperMask := 2429615101458271
  lowerMask := 2417851636799643247954080

private def cap20_0Codes : List Nat := [
  11801739528, 14513190876, 31957170894,
  36432603238, 98936481496, 99227711164]

def cap20_0 : Group.Batch template20.capOK :=
  Packed.capBatch template20 54020 rfl (by decide) cap20_0Codes
    (by decide +kernel)

end TBoards.SpliceFurtherData
