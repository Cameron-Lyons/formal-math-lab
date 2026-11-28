import SpliceData.Batch0100

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceData
open Splice

private def batch0103Codes : List Nat := [
  3290700384692345841821439961679, 3312334967314766799570575376558, 3314270993519950021913199797537,
  3346132893899680998769758664867]

def batch0103 : Group.Batch template5.tailOK where
  codes := batch0103Codes
  values := batch0103Codes.map (decodePiece 6 4)
  valid := by decide +kernel
  fingerprints := by decide +kernel
end TBoards.SpliceData
