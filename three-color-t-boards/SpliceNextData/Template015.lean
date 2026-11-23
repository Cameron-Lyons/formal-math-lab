import SplicePacked

-- Generated from splice_next.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceNextData
open Splice

def template15 : Group where
  k := 5
  pivot := [0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 2]
  caps := []
  tails := []
  upperMask := 2044130239214663344586752
  lowerMask := 373721400014595004825599

private def cap15_0Codes : List Nat := [
  560161586870, 561180378230, 709624637000,
  721360744808, 748309258346, 753081398816,
  753081399536, 832001686154, 833320486760,
  833320487480, 842194489298, 843221468786]

def cap15_0 : Group.Batch template15.capOK :=
  Packed.capBatch template15 8858 rfl (by decide) cap15_0Codes
    (by decide +kernel)

end TBoards.SpliceNextData
