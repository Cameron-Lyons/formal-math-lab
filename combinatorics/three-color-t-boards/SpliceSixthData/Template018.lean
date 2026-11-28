import SplicePacked

-- Generated from splice_sixth.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceSixthData
open Splice

def template18 : Group where
  k := 5
  pivot := [2, 2, 2, 2, 1, 2, 1, 0, 0, 2, 2]
  caps := []
  tails := []
  upperMask := 9250956964654289615
  lowerMask := 2417842388272293695122736

private def cap18_0Codes : List Nat := [
  36079024315, 126735418741, 129157722445,
  283655061319, 287127496813, 294072367801,
  297544803295]

def cap18_0 : Group.Batch template18.capOK :=
  Packed.capBatch template18 176264 rfl (by decide) cap18_0Codes
    (by decide +kernel)

end TBoards.SpliceSixthData
