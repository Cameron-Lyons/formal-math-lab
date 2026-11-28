import SplicePacked

-- Generated from splice_sixth.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceSixthData
open Splice

def template27 : Group where
  k := 5
  pivot := [2, 2, 1, 0, 1, 0, 0, 0, 0, 2, 2]
  caps := []
  tails := []
  upperMask := 74025949066973941595
  lowerMask := 2417777613280191375470756

private def cap27_0Codes : List Nat := [
  283669410553, 290614281541, 294086717035,
  301031588023]

def cap27_0 : Group.Batch template27.capOK :=
  Packed.capBatch template27 164762 rfl (by decide) cap27_0Codes
    (by decide +kernel)

end TBoards.SpliceSixthData
