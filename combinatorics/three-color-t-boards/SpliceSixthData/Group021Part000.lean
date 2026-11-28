import SpliceSixthData.Group018Part009
import SpliceSixthData.Template021

-- Generated from splice_sixth.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceSixthData
open Splice

private def tail21_0Codes : List Nat := [
  957225421181405892705950228170, 1282467269000000908903237812946, 1285612854897959668005020256268,
  3249487620833682440444681043060]

def tail21_0 : Group.Batch template21.tailOK :=
  Packed.tailBatch template21 10998 rfl (by decide) tail21_0Codes
    (by decide +kernel)

end TBoards.SpliceSixthData
