import SpliceData.Batch0001

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceData
open Splice

private def batch0004Codes : List Nat := [
  8859616192]

def batch0004 : Group.Batch template1.capOK where
  codes := batch0004Codes
  values := batch0004Codes.map (decodePiece 0 5)
  valid := by decide +kernel
  fingerprints := by decide +kernel
end TBoards.SpliceData
