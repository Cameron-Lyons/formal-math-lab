import SplicePacked

-- Generated from splice_next.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceNextData
open Splice

def template16 : Group where
  k := 5
  pivot := [0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 2]
  caps := []
  tails := []
  upperMask := 2044157855287578380468224
  lowerMask := 373693783941679968944127

private def cap16_0Codes : List Nat := [
  560161586870, 561180378230, 748309258346,
  753081398816, 753081399536, 832001686154,
  833320486760, 833320487480, 842194489298,
  843221468786]

def cap16_0 : Group.Batch template16.capOK :=
  Packed.capBatch template16 2954 rfl (by decide) cap16_0Codes
    (by decide +kernel)

end TBoards.SpliceNextData
