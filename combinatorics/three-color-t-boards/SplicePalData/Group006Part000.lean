import SplicePalData.Group003Part000
import SplicePalData.Template006

-- Generated from splice_pal.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SplicePalData
open Splice

private def tail6_0Codes : List Nat := [
  1059520189099467498602255007234, 2867827380779941112728270981580, 2868346539196801492675369204306,
  3343931729876159966341359272004]

def tail6_0 : Group.Batch template6.tailOK :=
  Packed.tailBatch template6 12618 rfl (by decide) tail6_0Codes
    (by decide +kernel)

end TBoards.SplicePalData
