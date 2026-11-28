import SpliceData.Batch0042

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceData
open Splice

private def batch0045Codes : List Nat := [
  395071800]

def batch0045 : Group.Batch template2.capOK where
  codes := batch0045Codes
  values := batch0045Codes.map (decodePiece 0 5)
  valid := by decide +kernel
  fingerprints := by decide +kernel
end TBoards.SpliceData
