import SpliceTransferData.Part003

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceTransferData
open Splice

private def template40 : Group where
  k := 5
  pivot := [2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1]
  caps := ([291289172356] : List Nat).map Packed.cap
  tails := []
  upperMask := 1708316269398474025558048
  lowerMask := 709535369830784323854303
private def selection40 : List Nat := [109, 0, 165, 14, 52, 0, 12, 0, 0, 38, 16, 43, 9, 0, 13, 0, 3, 46, 45, 1, 0, 0, 36, 16, 10, 10, 13, 0, 81, 186, 24, 0, 74, 49, 65, 20, 12, 12, 9, 10, 20, 8, 26, 45, 66, 6, 32, 23]

def group40 := Transfer.assemble SpliceData.group3 template40 selection40
theorem group40_checked : group40.Checked := by
  apply Transfer.assemble_checked _ _ _ SpliceData.group3_checked <;> decide +kernel
theorem group40_size : group40.size = 48 := by decide +kernel

private def template41 : Group where
  k := 5
  pivot := [2, 2, 0, 1, 2, 2, 2, 2, 0, 2, 2]
  caps := ([136549522495] : List Nat).map Packed.cap
  tails := []
  upperMask := 11348853493085755
  lowerMask := 2417851627880404856326596
private def selection41 : List Nat := [70, 0, 0, 209, 0, 255, 0, 0, 0, 163, 1479, 0, 0, 0, 247, 133, 0, 136, 0, 0, 81, 0, 910, 558, 0, 0, 0, 0, 0, 0, 771, 0, 0, 0, 0, 228, 447, 0, 0, 369, 0, 0, 2708, 0, 0, 0, 0, 0]

def group41 := Transfer.assemble SpliceExtensionData.group10 template41 selection41
theorem group41_checked : group41.Checked := by
  apply Transfer.assemble_checked _ _ _ SpliceExtensionData.group10_checked <;> decide +kernel
theorem group41_size : group41.size = 48 := by decide +kernel

private def template42 : Group where
  k := 5
  pivot := [2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1]
  caps := ([1226292778, 139988135826, 388712089764, 388712444292] : List Nat).map Packed.cap
  tails := []
  upperMask := 5651149839611419
  lowerMask := 2417851633578108509800932
private def selection42 : List Nat := [62, 0, 0, 1100, 731, 0, 0, 335, 0, 176, 1596, 57]

def group42 := Transfer.assemble SpliceExtensionData.group12 template42 selection42
theorem group42_checked : group42.Checked := by
  apply Transfer.assemble_checked _ _ _ SpliceExtensionData.group12_checked <;> decide +kernel
theorem group42_size : group42.size = 48 := by decide +kernel

private def template43 : Group where
  k := 5
  pivot := [0, 1, 0, 0, 2, 2, 0, 0, 2, 2, 2]
  caps := ([323168407101] : List Nat).map Packed.cap
  tails := []
  upperMask := 18737263325930074911
  lowerMask := 2417832901965932419337440
private def selection43 : List Nat := [2787, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def group43 := Transfer.assemble SpliceExtensionData.group6 template43 selection43
theorem group43_checked : group43.Checked := by
  apply Transfer.assemble_checked _ _ _ SpliceExtensionData.group6_checked <;> decide +kernel
theorem group43_size : group43.size = 48 := by decide +kernel

private def template44 : Group where
  k := 5
  pivot := [1, 0, 1, 0, 1, 2, 2, 0, 1, 2, 2]
  caps := ([127287737794] : List Nat).map Packed.cap
  tails := []
  upperMask := 74113576542157813291
  lowerMask := 2417777525652716191599060
private def selection44 : List Nat := [190, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def group44 := Transfer.assemble SpliceExtensionData.group7 template44 selection44
theorem group44_checked : group44.Checked := by
  apply Transfer.assemble_checked _ _ _ SpliceExtensionData.group7_checked <;> decide +kernel
theorem group44_size : group44.size = 47 := by decide +kernel

private def template45 : Group where
  k := 5
  pivot := [0, 1, 0, 0, 1, 2, 2, 0, 1, 2, 2]
  caps := ([378165659889, 388582966371] : List Nat).map Packed.cap
  tails := []
  upperMask := 9405857645049033785
  lowerMask := 2417842233371613300378566
private def selection45 : List Nat := [112, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def group45 := Transfer.assemble SpliceExtensionData.group7 template45 selection45
theorem group45_checked : group45.Checked := by
  apply Transfer.assemble_checked _ _ _ SpliceExtensionData.group7_checked <;> decide +kernel
theorem group45_size : group45.size = 46 := by decide +kernel

private def template46 : Group where
  k := 5
  pivot := [1, 2, 2, 2, 1, 1, 2, 2, 1, 1, 0]
  caps := ([137764387828, 317915978896] : List Nat).map Packed.cap
  tails := []
  upperMask := 23102598454343194
  lowerMask := 2417851616126659895069157
private def selection46 : List Nat := [20, 0, 452, 0, 252, 14, 31, 139, 72, 8, 163, 38, 2, 411, 342, 3, 131, 207, 89, 132, 139, 8]

def group46 := Transfer.assemble SpliceExtensionData.group13 template46 selection46
theorem group46_checked : group46.Checked := by
  apply Transfer.assemble_checked _ _ _ SpliceExtensionData.group13_checked <;> decide +kernel
theorem group46_size : group46.size = 44 := by decide +kernel

private def template47 : Group where
  k := 5
  pivot := [2, 2, 1, 2, 2, 1, 2, 0, 1, 1, 1]
  caps := ([286052182435] : List Nat).map Packed.cap
  tails := []
  upperMask := 18596578447123985947
  lowerMask := 2417833042650811225426404
private def selection47 : List Nat := [725, 152, 298, 0, 189, 377, 63, 0, 6, 41, 39, 36, 28, 0, 275, 11, 155, 8, 200, 101, 282, 0, 76, 29, 160, 377, 342, 408, 129, 206, 152, 299, 300, 18, 217, 23, 100, 309, 21, 31, 264, 0, 19]

def group47 := Transfer.assemble SpliceExtensionData.group14 template47 selection47
theorem group47_checked : group47.Checked := by
  apply Transfer.assemble_checked _ _ _ SpliceExtensionData.group14_checked <;> decide +kernel
theorem group47_size : group47.size = 43 := by decide +kernel

end TBoards.SpliceTransferData
