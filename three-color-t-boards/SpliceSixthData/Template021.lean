import SplicePacked

-- Generated from splice_sixth.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceSixthData
open Splice

def template21 : Group where
  k := 5
  pivot := [0, 0, 1, 2, 0, 0, 0, 2, 1, 0, 0]
  caps := []
  tails := []
  upperMask := 1337443884115853646386
  lowerMask := 2416514195345142495765965

private def cap21_0Codes : List Nat := [
  169047361377, 169434250425]

def cap21_0 : Group.Batch template21.capOK :=
  Packed.capBatch template21 10998 rfl (by decide) cap21_0Codes
    (by decide +kernel)

end TBoards.SpliceSixthData
