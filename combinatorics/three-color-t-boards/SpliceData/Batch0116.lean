import SpliceData.Batch0113

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceData
open Splice

private def batch0116Codes : List Nat := [
  666263577884, 666263617248, 756919972310,
  756920011674, 759230148524, 759230187888,
  759244490870, 759244530234]

def batch0116 : Group.Batch template8.capOK where
  codes := batch0116Codes
  values := batch0116Codes.map (decodePiece 0 5)
  valid := by decide +kernel
  fingerprints := by decide +kernel
end TBoards.SpliceData
