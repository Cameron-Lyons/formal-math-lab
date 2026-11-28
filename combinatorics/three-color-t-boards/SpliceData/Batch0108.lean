import SpliceData.Batch0105

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceData
open Splice

private def batch0108Codes : List Nat := [
  94430936255, 94430975619, 194356720229,
  194356759593, 194371062575, 194371101939]

def batch0108 : Group.Batch template7.capOK where
  codes := batch0108Codes
  values := batch0108Codes.map (decodePiece 0 5)
  valid := by decide +kernel
  fingerprints := by decide +kernel
end TBoards.SpliceData
