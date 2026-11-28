import SpliceData.Batch0116

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceData
open Splice

private def batch0119Codes : List Nat := [
  649074757970, 649074797334, 652547193464,
  652547232828]

def batch0119 : Group.Batch template9.capOK where
  codes := batch0119Codes
  values := batch0119Codes.map (decodePiece 0 5)
  valid := by decide +kernel
  fingerprints := by decide +kernel
end TBoards.SpliceData
