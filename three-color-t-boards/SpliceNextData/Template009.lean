import SplicePacked

-- Generated from splice_next.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceNextData
open Splice

def template9 : Group where
  k := 5
  pivot := [0, 2, 1, 0, 1, 1, 0, 0, 0, 2, 1]
  caps := []
  tails := []
  upperMask := 11763824783175981023
  lowerMask := 2417839875404475173431328

private def cap9_0Codes : List Nat := [
  283669410278, 290614281266, 294086716760,
  301031587748]

def cap9_0 : Group.Batch template9.capOK :=
  Packed.capBatch template9 46906 rfl (by decide) cap9_0Codes
    (by decide +kernel)

end TBoards.SpliceNextData
