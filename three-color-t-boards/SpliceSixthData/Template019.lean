import SplicePacked

-- Generated from splice_sixth.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceSixthData
open Splice

def template19 : Group where
  k := 5
  pivot := [2, 2, 2, 2, 0, 2, 1, 0, 0, 2, 2]
  caps := []
  tails := []
  upperMask := 9326955207805113295
  lowerMask := 2417842312274050544299056

private def cap19_0Codes : List Nat := [
  36079024318, 126735418744, 129157722448,
  283655061322, 287127496816, 294072367804,
  297544803298]

def cap19_0 : Group.Batch template19.capOK :=
  Packed.capBatch template19 175535 rfl (by decide) cap19_0Codes
    (by decide +kernel)

end TBoards.SpliceSixthData
