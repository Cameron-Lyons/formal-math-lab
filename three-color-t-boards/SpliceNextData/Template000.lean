import SplicePacked

-- Generated from splice_next.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceNextData
open Splice

def template0 : Group where
  k := 5
  pivot := [0, 2, 1, 0, 1, 1, 0, 2, 0, 0, 2]
  caps := []
  tails := []
  upperMask := 4723686319379980754911
  lowerMask := 2413127952909878368657440

private def cap0_0Codes : List Nat := [
  283669410229, 290614281217, 294086716711,
  301031587699]

def cap0_0 : Group.Batch template0.capOK :=
  Packed.capBatch template0 46955 rfl (by decide) cap0_0Codes
    (by decide +kernel)

end TBoards.SpliceNextData
