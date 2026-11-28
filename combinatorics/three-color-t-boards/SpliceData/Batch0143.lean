import SpliceData.Batch0140

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceData
open Splice

private def batch0143Codes : List Nat := [
  283669410256, 290614281244, 294086716738,
  301031587726]

def batch0143 : Group.Batch template12.capOK where
  codes := batch0143Codes
  values := batch0143Codes.map (decodePiece 0 5)
  valid := by decide +kernel
  fingerprints := by decide +kernel
end TBoards.SpliceData
