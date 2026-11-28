import SplicePacked

-- Generated from splice_further.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceFurtherData
open Splice

def template78 : Group where
  k := 5
  pivot := [2, 2, 0, 1, 2, 2, 2, 1, 0, 2, 2]
  caps := []
  tails := []
  upperMask := 4804835161945659
  lowerMask := 2417851634424423187466692

private def cap78_0Codes : List Nat := [
  391687133827, 409131113845, 411842565193]

def cap78_0 : Group.Batch template78.capOK :=
  Packed.capBatch template78 161792 rfl (by decide) cap78_0Codes
    (by decide +kernel)

end TBoards.SpliceFurtherData
