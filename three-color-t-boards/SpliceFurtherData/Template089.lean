import SplicePacked

-- Generated from splice_further.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceFurtherData
open Splice

def template89 : Group where
  k := 5
  pivot := [2, 0, 1, 0, 1, 1, 1, 0, 0, 2, 0]
  caps := []
  tails := []
  upperMask := 9462063170772023135
  lowerMask := 2417842177166087577389216

private def cap89_0Codes : List Nat := [
  283669410229, 290614281217, 294086716711,
  301031587699]

def cap89_0 : Group.Batch template89.capOK :=
  Packed.capBatch template89 125718 rfl (by decide) cap89_0Codes
    (by decide +kernel)

end TBoards.SpliceFurtherData
