import SplicePacked

-- Generated from splice_sixth.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceSixthData
open Splice

def template22 : Group where
  k := 5
  pivot := [0, 0, 1, 2, 0, 1, 0, 2, 1, 0, 0]
  caps := []
  tails := []
  upperMask := 1337570020364133145138
  lowerMask := 2416514069208894216267213

private def cap22_0Codes : List Nat := [
  169047361377, 169434250425]

def cap22_0 : Group.Batch template22.capOK :=
  Packed.capBatch template22 11241 rfl (by decide) cap22_0Codes
    (by decide +kernel)

end TBoards.SpliceSixthData
