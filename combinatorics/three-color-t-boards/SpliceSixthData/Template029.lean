import SplicePacked

-- Generated from splice_sixth.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceSixthData
open Splice

def template29 : Group where
  k := 5
  pivot := [0, 0, 1, 0, 1, 1, 0, 1, 1, 0, 0]
  caps := []
  tails := []
  upperMask := 2044139534644431407808512
  lowerMask := 373712104584826941603839

private def cap29_0Codes : List Nat := [
  458571758578, 465549578752, 559816031740,
  706266842584, 842231337880]

def cap29_0 : Group.Batch template29.capOK :=
  Packed.capBatch template29 7569 rfl (by decide) cap29_0Codes
    (by decide +kernel)

end TBoards.SpliceSixthData
