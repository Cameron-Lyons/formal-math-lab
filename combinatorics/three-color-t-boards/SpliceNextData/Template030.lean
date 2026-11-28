import SplicePacked

-- Generated from splice_next.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceNextData
open Splice

def template30 : Group where
  k := 5
  pivot := [0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0]
  caps := []
  tails := []
  upperMask := 2044056542310359040524288
  lowerMask := 373795096918899308888063

private def cap30_0Codes : List Nat := [
  709624991960, 710134827586, 748060898278,
  748352127946, 810856006204, 842204050862,
  843651341852]

def cap30_0 : Group.Batch template30.capOK :=
  Packed.capBatch template30 2295 rfl (by decide) cap30_0Codes
    (by decide +kernel)

end TBoards.SpliceNextData
