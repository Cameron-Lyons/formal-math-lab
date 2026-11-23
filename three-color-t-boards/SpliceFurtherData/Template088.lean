import SplicePacked

-- Generated from splice_further.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceFurtherData
open Splice

def template88 : Group where
  k := 5
  pivot := [2, 2, 1, 0, 2, 1, 2, 0, 0, 2, 2]
  caps := []
  tails := []
  upperMask := 4722605455503276673999
  lowerMask := 2413129033773755072738352

private def cap88_0Codes : List Nat := [
  283669410229, 290614281217, 294086716711,
  301031587699]

def cap88_0 : Group.Batch template88.capOK :=
  Packed.capBatch template88 165896 rfl (by decide) cap88_0Codes
    (by decide +kernel)

end TBoards.SpliceFurtherData
