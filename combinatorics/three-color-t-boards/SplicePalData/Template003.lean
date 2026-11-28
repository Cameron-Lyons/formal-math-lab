import SplicePacked

-- Generated from splice_pal.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SplicePalData
open Splice

def template3 : Group where
  k := 5
  pivot := [1, 0, 0, 2, 2, 1, 2, 2, 0, 0, 1]
  caps := []
  tails := []
  upperMask := 152453160054971840666134
  lowerMask := 2265398479174286508746217

private def cap3_0Codes : List Nat := [
  169047322013, 169076046069, 169434211061,
  169462935117]

def cap3_0 : Group.Batch template3.capOK :=
  Packed.capBatch template3 65341 rfl (by decide) cap3_0Codes
    (by decide +kernel)

end TBoards.SplicePalData
