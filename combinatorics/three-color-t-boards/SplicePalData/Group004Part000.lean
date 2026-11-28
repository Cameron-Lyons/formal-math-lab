import SplicePalData.Group001Part002
import SplicePalData.Template004

-- Generated from splice_pal.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SplicePalData
open Splice

private def tail4_0Codes : List Nat := [
  957225421181405892705950228170, 1282467269000000908903237812946, 1285612854897959668005020256268,
  3249487620833682440444681043060]

def tail4_0 : Group.Batch template4.tailOK :=
  Packed.tailBatch template4 10998 rfl (by decide) tail4_0Codes
    (by decide +kernel)

end TBoards.SplicePalData
