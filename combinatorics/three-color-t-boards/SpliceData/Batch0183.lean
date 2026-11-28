import SpliceData.Batch0180

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceData
open Splice

private def batch0183Codes : List Nat := [
  3228711432085155879342284341259, 3228723724917376920968143665553, 3228724472565835696234329276755,
  3228759147676515012960166204064]

def batch0183 : Group.Batch template12.tailOK where
  codes := batch0183Codes
  values := batch0183Codes.map (decodePiece 6 4)
  valid := by decide +kernel
  fingerprints := by decide +kernel
end TBoards.SpliceData
