import SpliceTransferData.Part007

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceTransferData
open Splice

private def template72 : Group where
  k := 5
  pivot := [1, 2, 2, 2, 1, 1, 1, 2, 2, 1, 1]
  caps := ([36432603239] : List Nat).map Packed.cap
  tails := []
  upperMask := 75557868251164314859035
  lowerMask := 2342293770978094034553316
private def selection72 : List Nat := [207, 25, 379, 2, 122, 56, 94, 403, 220, 308, 137, 0, 125]

def group72 := Transfer.assemble SpliceExtensionData.group13 template72 selection72
theorem group72_checked : group72.Checked := by
  apply Transfer.assemble_checked _ _ _ SpliceExtensionData.group13_checked <;> decide +kernel
theorem group72_size : group72.size = 13 := by decide +kernel

private def template73 : Group where
  k := 5
  pivot := [1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1]
  caps := ([150448474659] : List Nat).map Packed.cap
  tails := []
  upperMask := 73792063945027253787
  lowerMask := 2417777847165313322158564
private def selection73 : List Nat := [352, 0, 11, 335, 775, 7, 30, 25, 371, 7, 132, 287]

def group73 := Transfer.assemble SpliceExtensionData.group13 template73 selection73
theorem group73_checked : group73.Checked := by
  apply Transfer.assemble_checked _ _ _ SpliceExtensionData.group13_checked <;> decide +kernel
theorem group73_size : group73.size = 12 := by decide +kernel

private def template74 : Group where
  k := 5
  pivot := [1, 2, 1, 2, 2, 1, 2, 2, 1, 1, 2]
  caps := ([1226646784, 42249759490, 94292240410, 388716850864] : List Nat).map Packed.cap
  tails := []
  upperMask := 5651149839611419
  lowerMask := 2417851633578108509800932
private def selection74 : List Nat := [1490, 1495, 0]

def group74 := Transfer.assemble SpliceExtensionData.group12 template74 selection74
theorem group74_checked : group74.Checked := by
  apply Transfer.assemble_checked _ _ _ SpliceExtensionData.group12_checked <;> decide +kernel
theorem group74_size : group74.size = 12 := by decide +kernel

private def template75 : Group where
  k := 5
  pivot := [0, 0, 0, 2, 2, 0, 0, 0, 2, 2, 2]
  caps := ([98979368592] : List Nat).map Packed.cap
  tails := []
  upperMask := 92360870763706138
  lowerMask := 2417851546868387585706213
private def selection75 : List Nat := [234, 0, 0, 0, 0, 133, 0, 0, 0, 0, 0, 0]

def group75 := Transfer.assemble SpliceExtensionData.group6 template75 selection75
theorem group75_checked : group75.Checked := by
  apply Transfer.assemble_checked _ _ _ SpliceExtensionData.group6_checked <;> decide +kernel
theorem group75_size : group75.size = 12 := by decide +kernel

private def template76 : Group where
  k := 5
  pivot := [2, 0, 0, 2, 2, 2, 0, 0, 2, 2, 0]
  caps := ([663838424058] : List Nat).map Packed.cap
  tails := []
  upperMask := 9225660915071071519
  lowerMask := 2417842413568343278340832
private def selection76 : List Nat := [1695, 2, 6, 1294, 6, 945, 2727, 460, 18, 14, 760]

def group76 := Transfer.assemble SpliceExtensionData.group6 template76 selection76
theorem group76_checked : group76.Checked := by
  apply Transfer.assemble_checked _ _ _ SpliceExtensionData.group6_checked <;> decide +kernel
theorem group76_size : group76.size = 11 := by decide +kernel

private def template77 : Group where
  k := 5
  pivot := [1, 0, 0, 0, 0, 0, 2, 0, 0, 2, 2]
  caps := ([599874912181] : List Nat).map Packed.cap
  tails := []
  upperMask := 48662238785653969679
  lowerMask := 2417802976990472695442672
private def selection77 : List Nat := [6805, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def group77 := Transfer.assemble SpliceExtensionData.group5 template77 selection77
theorem group77_checked : group77.Checked := by
  apply Transfer.assemble_checked _ _ _ SpliceExtensionData.group5_checked <;> decide +kernel
theorem group77_size : group77.size = 11 := by decide +kernel

private def template78 : Group where
  k := 5
  pivot := [2, 2, 1, 2, 1, 2, 1, 1, 1, 2, 2]
  caps := ([314040742416] : List Nat).map Packed.cap
  tails := []
  upperMask := 227854224474694230696555
  lowerMask := 2189997414754564118715796
private def selection78 : List Nat := [40, 431, 0, 255, 0, 427, 0, 869, 0, 0]

def group78 := Transfer.assemble SpliceExtensionData.group0 template78 selection78
theorem group78_checked : group78.Checked := by
  apply Transfer.assemble_checked _ _ _ SpliceExtensionData.group0_checked <;> decide +kernel
theorem group78_size : group78.size = 10 := by decide +kernel

private def template79 : Group where
  k := 5
  pivot := [2, 1, 2, 2, 1, 2, 2, 1, 1, 1, 1]
  caps := ([4783822039] : List Nat).map Packed.cap
  tails := []
  upperMask := 9229023117974910491
  lowerMask := 2417842410206140374501860
private def selection79 : List Nat := [62, 0, 40, 0, 755, 286, 1053, 32, 728, 0]

def group79 := Transfer.assemble SpliceExtensionData.group12 template79 selection79
theorem group79_checked : group79.Checked := by
  apply Transfer.assemble_checked _ _ _ SpliceExtensionData.group12_checked <;> decide +kernel
theorem group79_size : group79.size = 10 := by decide +kernel

end TBoards.SpliceTransferData
