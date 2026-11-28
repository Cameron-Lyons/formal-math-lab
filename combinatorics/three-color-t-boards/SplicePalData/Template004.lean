import SplicePacked

-- Generated from splice_pal.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SplicePalData
open Splice

def template4 : Group where
  k := 5
  pivot := [0, 0, 1, 2, 0, 0, 0, 2, 1, 0, 0]
  caps := []
  tails := []
  upperMask := 1337443884115853646386
  lowerMask := 2416514195345142495765965

private def cap4_0Codes : List Nat := [
  169047322013, 169076046069, 169434211061,
  169462935117]

def cap4_0 : Group.Batch template4.capOK :=
  Packed.capBatch template4 10998 rfl (by decide) cap4_0Codes
    (by decide +kernel)

end TBoards.SplicePalData
