import SplicePacked

-- Generated from splice_further.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceFurtherData
open Splice

def template96 : Group where
  k := 5
  pivot := [2, 2, 0, 2, 2, 1, 2, 2, 0, 2, 2]
  caps := []
  tails := []
  upperMask := 8023930263713563
  lowerMask := 2417851631205328085698788

private def cap96_0Codes : List Nat := [
  136549522495, 329352064311, 422417657937,
  423064945795]

def cap96_0 : Group.Batch template96.capOK :=
  Packed.capBatch template96 163763 rfl (by decide) cap96_0Codes
    (by decide +kernel)

end TBoards.SpliceFurtherData
