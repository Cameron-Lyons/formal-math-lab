import SplicePacked

-- Generated from splice_extension.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceExtensionData
open Splice

def template14 : Group where
  k := 5
  pivot := [2, 2, 1, 2, 2, 1, 2, 0, 1, 2, 2]
  caps := []
  tails := []
  upperMask := 5719323851273755
  lowerMask := 2417851633509934498138596

private def cap14_0Codes : List Nat := [
  137536073509, 287515448977, 381351675631,
  418860541731, 423064945795]

def cap14_0 : Group.Batch template14.capOK :=
  Packed.capBatch template14 170279 rfl (by decide) cap14_0Codes
    (by decide +kernel)

end TBoards.SpliceExtensionData
