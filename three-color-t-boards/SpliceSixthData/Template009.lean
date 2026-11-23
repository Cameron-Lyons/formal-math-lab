import SplicePacked

-- Generated from splice_sixth.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceSixthData
open Splice

def template9 : Group where
  k := 5
  pivot := [2, 2, 2, 2, 0, 1, 2, 2, 2, 1, 2]
  caps := []
  tails := []
  upperMask := 1813388906188573223289711
  lowerMask := 604462733040685126122640

private def cap9_0Codes : List Nat := [
  39565808719, 220878597571, 283669410229,
  290614281217, 294086716711, 301031587699]

def cap9_0 : Group.Batch template9.capOK :=
  Packed.capBatch template9 175442 rfl (by decide) cap9_0Codes
    (by decide +kernel)

end TBoards.SpliceSixthData
