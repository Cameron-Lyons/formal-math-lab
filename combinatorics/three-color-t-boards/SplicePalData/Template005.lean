import SplicePacked

-- Generated from splice_pal.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SplicePalData
open Splice

def template5 : Group where
  k := 5
  pivot := [0, 0, 1, 2, 0, 1, 0, 2, 1, 0, 0]
  caps := []
  tails := []
  upperMask := 1337570020364133145138
  lowerMask := 2416514069208894216267213

private def cap5_0Codes : List Nat := [
  169047322013, 169076046069, 169434211061,
  169462935117]

def cap5_0 : Group.Batch template5.capOK :=
  Packed.capBatch template5 11241 rfl (by decide) cap5_0Codes
    (by decide +kernel)

end TBoards.SplicePalData
