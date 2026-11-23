import SplicePacked

-- Generated from splice_extension.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceExtensionData
open Splice

def template13 : Group where
  k := 5
  pivot := [1, 2, 2, 2, 1, 1, 2, 2, 1, 1, 2]
  caps := []
  tails := []
  upperMask := 5088199944861211
  lowerMask := 2417851634141058404551140

private def cap13_0Codes : List Nat := [
  3637267590, 5084558580, 98979351096,
  137663617482, 137678294386, 286108231212,
  287127022572, 388713551616]

def cap13_0 : Group.Batch template13.capOK :=
  Packed.capBatch template13 117113 rfl (by decide) cap13_0Codes
    (by decide +kernel)

end TBoards.SpliceExtensionData
