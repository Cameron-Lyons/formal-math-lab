import SplicePacked

-- Generated from splice_pal.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SplicePalData
open Splice

def template7 : Group where
  k := 5
  pivot := [2, 0, 1, 1, 2, 0, 2, 1, 1, 0, 2]
  caps := []
  tails := []
  upperMask := 76000586656555446352530
  lowerMask := 2341851052572702903059821

private def cap7_0Codes : List Nat := [
  137666256499, 138053145547]

def cap7_0 : Group.Batch template7.capOK :=
  Packed.capBatch template7 128504 rfl (by decide) cap7_0Codes
    (by decide +kernel)

end TBoards.SplicePalData
