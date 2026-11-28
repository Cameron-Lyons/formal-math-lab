import SplicePacked

-- Generated from splice_next.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceNextData
open Splice

def template14 : Group where
  k := 5
  pivot := [0, 1, 1, 0, 0, 0, 1, 1, 0, 0, 1]
  caps := []
  tails := []
  upperMask := 2044130167157069440876544
  lowerMask := 373721472072188908535807

private def cap14_0Codes : List Nat := [
  427281572311, 428728863301, 435446044249,
  438157495597, 455601475615, 458533131575,
  522623655817, 835644649405]

def cap14_0 : Group.Batch template14.capOK :=
  Packed.capBatch template14 26353 rfl (by decide) cap14_0Codes
    (by decide +kernel)

end TBoards.SpliceNextData
