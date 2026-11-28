import SplicePacked

-- Generated from splice_next.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceNextData
open Splice

def template7 : Group where
  k := 5
  pivot := [1, 0, 2, 1, 1, 0, 0, 0, 0, 2, 1]
  caps := []
  tails := []
  upperMask := 13997188004681882319
  lowerMask := 2417837642041253667530032

private def cap7_0Codes : List Nat := [
  283669410423, 290614281411, 294086716905,
  301031587893]

def cap7_0 : Group.Batch template7.capOK :=
  Packed.capBatch template7 75094 rfl (by decide) cap7_0Codes
    (by decide +kernel)

end TBoards.SpliceNextData
