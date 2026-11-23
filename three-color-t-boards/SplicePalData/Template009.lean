import SplicePacked

-- Generated from splice_pal.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SplicePalData
open Splice

def template9 : Group where
  k := 5
  pivot := [2, 2, 1, 1, 2, 0, 2, 1, 1, 2, 2]
  caps := []
  tails := []
  upperMask := 76000586585911861895814
  lowerMask := 2341851052643346487516537

private def cap9_0Codes : List Nat := [
  137666249937, 138053138985]

def cap9_0 : Group.Batch template9.capOK :=
  Packed.capBatch template9 167876 rfl (by decide) cap9_0Codes
    (by decide +kernel)

end TBoards.SplicePalData
