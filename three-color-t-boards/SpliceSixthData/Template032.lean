import SplicePacked

-- Generated from splice_sixth.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceSixthData
open Splice

def template32 : Group where
  k := 5
  pivot := [1, 0, 1, 0, 2, 2, 0, 0, 0, 2, 1]
  caps := []
  tails := []
  upperMask := 198475388582957035
  lowerMask := 2417851440753869766455316

private def cap32_0Codes : List Nat := [
  283669410252, 290614281240, 294086716734,
  301031587722]

def cap32_0 : Group.Batch template32.capOK :=
  Packed.capBatch template32 67561 rfl (by decide) cap32_0Codes
    (by decide +kernel)

end TBoards.SpliceSixthData
