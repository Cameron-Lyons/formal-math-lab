import SpliceData.Batch0134

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceData
open Splice

private def batch0137Codes : List Nat := [
  666263575696, 666263595378, 756919970122,
  756919989804, 758067887056, 758067906738,
  758069481370, 758082229402, 758082249084]

def batch0137 : Group.Batch template11.capOK where
  codes := batch0137Codes
  values := batch0137Codes.map (decodePiece 0 5)
  valid := by decide +kernel
  fingerprints := by decide +kernel
end TBoards.SpliceData
