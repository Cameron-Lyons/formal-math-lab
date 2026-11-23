import SplicePacked

-- Generated from splice_next.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceNextData
open Splice

def template26 : Group where
  k := 5
  pivot := [2, 2, 2, 2, 1, 2, 1, 1, 0, 2, 2]
  caps := []
  tails := []
  upperMask := 110856105206200206159
  lowerMask := 2417740783124052149206192

private def cap26_0Codes : List Nat := [
  39565808719, 220878597571, 283669410229,
  290614281217, 294086716711, 301031587699]

def cap26_0 : Group.Batch template26.capOK :=
  Packed.capBatch template26 176291 rfl (by decide) cap26_0Codes
    (by decide +kernel)

end TBoards.SpliceNextData
