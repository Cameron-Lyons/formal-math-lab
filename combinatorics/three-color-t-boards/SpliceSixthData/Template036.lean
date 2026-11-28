import SplicePacked

-- Generated from splice_sixth.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceSixthData
open Splice

def template36 : Group where
  k := 5
  pivot := [0, 0, 1, 0, 1, 1, 0, 1, 1, 0, 0]
  caps := []
  tails := []
  upperMask := 2044148577872415790465024
  lowerMask := 373703061356842558947327

private def cap36_0Codes : List Nat := [
  428701576283, 564666071579, 711116882423,
  805383335411, 812361155585]

def cap36_0 : Group.Batch template36.capOK :=
  Packed.capBatch template36 7569 rfl (by decide) cap36_0Codes
    (by decide +kernel)

end TBoards.SpliceSixthData
