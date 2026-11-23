import SplicePacked

-- Generated from splice_pal.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SplicePalData
open Splice

def template10 : Group where
  k := 5
  pivot := [2, 2, 1, 1, 2, 0, 2, 1, 1, 2, 2]
  caps := []
  tails := []
  upperMask := 76000591107103641889410
  lowerMask := 2341851048122154707522941

private def cap10_0Codes : List Nat := [
  137666256499, 138053145547]

def cap10_0 : Group.Batch template10.capOK :=
  Packed.capBatch template10 167876 rfl (by decide) cap10_0Codes
    (by decide +kernel)

end TBoards.SplicePalData
