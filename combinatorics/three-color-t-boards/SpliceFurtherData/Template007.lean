import SplicePacked

-- Generated from splice_further.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceFurtherData
open Splice

def template7 : Group where
  k := 5
  pivot := [2, 0, 2, 2, 0, 0, 2, 2, 0, 2, 0]
  caps := []
  tails := []
  upperMask := 2394431266502491
  lowerMask := 2417851636834827082909860

private def cap7_0Codes : List Nat := [
  4067140656, 5094120144, 11801739528,
  13968121962, 13968122682, 14513190876,
  31957170894, 94207209906, 94207210626,
  98979351096, 136128855744]

def cap7_0 : Group.Batch template7.capOK :=
  Packed.capBatch template7 135816 rfl (by decide) cap7_0Codes
    (by decide +kernel)

end TBoards.SpliceFurtherData
