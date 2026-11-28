import SpliceData.Batch0120

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceData
open Splice

private def batch0123Codes : List Nat := [
  94430933932, 94430953614, 193194458626,
  193194478308, 193208800972, 193208820654,
  193210395286]

def batch0123 : Group.Batch template10.capOK where
  codes := batch0123Codes
  values := batch0123Codes.map (decodePiece 0 5)
  valid := by decide +kernel
  fingerprints := by decide +kernel
end TBoards.SpliceData
