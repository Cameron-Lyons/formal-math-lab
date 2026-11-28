import SpliceTransferData.Part000

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceTransferData
open Splice

private def template16 : Group where
  k := 5
  pivot := [2, 2, 0, 0, 0, 1, 0, 0, 2, 2, 2]
  caps := ([105184104057] : List Nat).map Packed.cap
  tails := []
  upperMask := 9297718508572128543
  lowerMask := 2417842341510749777283808
private def selection16 : List Nat := [568, 0, 0, 0, 0, 403, 0, 0, 0, 313, 0, 0, 0, 0, 0, 0, 0, 0, 207, 214, 0, 0, 0, 302, 0, 0, 0, 0, 0, 0, 0, 0, 362, 0, 0, 0, 0, 0, 0, 0, 0, 469, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 224, 0, 0, 0, 0, 0, 0, 180, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 165, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 203, 0, 0, 0, 0, 280, 0, 0, 0, 0, 0, 0, 0, 0, 0, 269, 0, 0, 0, 0, 0, 0, 361, 0, 0, 0, 0, 664, 0, 0, 0, 0, 0, 0, 0, 0, 0, 250, 0, 0, 0, 0, 0, 0, 0, 0, 0, 335, 0, 0, 0, 0, 0, 0, 513, 0, 0, 0, 0, 0, 0, 0, 0, 0, 278, 0, 0, 0, 0, 506, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 565, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def group16 := Transfer.assemble SpliceExtensionData.group6 template16 selection16
theorem group16_checked : group16.Checked := by
  apply Transfer.assemble_checked _ _ _ SpliceExtensionData.group6_checked <;> decide +kernel
theorem group16_size : group16.size = 199 := by decide +kernel

private def template17 : Group where
  k := 5
  pivot := [1, 0, 0, 0, 2, 2, 0, 0, 2, 2, 2]
  caps := ([137701874673] : List Nat).map Packed.cap
  tails := []
  upperMask := 56332073610524445
  lowerMask := 2417851582897184738887906
private def selection17 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def group17 := Transfer.assemble SpliceExtensionData.group6 template17 selection17
theorem group17_checked : group17.Checked := by
  apply Transfer.assemble_checked _ _ _ SpliceExtensionData.group6_checked <;> decide +kernel
theorem group17_size : group17.size = 153 := by decide +kernel

private def template18 : Group where
  k := 5
  pivot := [1, 1, 0, 0, 2, 2, 0, 0, 2, 2, 2]
  caps := ([291776068440] : List Nat).map Packed.cap
  tails := []
  upperMask := 18593148001489008415
  lowerMask := 2417833046081256860403936
private def selection18 : List Nat := [815, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1836, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def group18 := Transfer.assemble SpliceExtensionData.group6 template18 selection18
theorem group18_checked : group18.Checked := by
  apply Transfer.assemble_checked _ _ _ SpliceExtensionData.group6_checked <;> decide +kernel
theorem group18_size : group18.size = 136 := by decide +kernel

private def template19 : Group where
  k := 5
  pivot := [2, 2, 2, 0, 1, 1, 1, 0, 1, 2, 2]
  caps := ([296385770800] : List Nat).map Packed.cap
  tails := []
  upperMask := 83012689337390872123
  lowerMask := 2417768626539920958540228
private def selection19 : List Nat := [159, 161, 160, 0, 26, 0, 232, 117, 254, 0, 97, 0, 0, 38, 105, 87, 78, 0, 197, 0, 0, 91, 107, 0, 41, 122, 0, 0, 0, 399, 206, 0, 133, 0, 0, 0, 116, 0, 61, 502, 0, 0, 171, 0, 149, 0, 0, 0, 281, 114, 313, 0, 0, 0, 0, 0, 54, 0, 232, 109, 0, 0, 0, 0, 269, 0, 0, 0, 93, 0, 166, 0, 0, 0, 0, 331, 0, 0, 0, 0, 0, 140, 0, 0, 85, 50, 0, 0, 0, 482, 0, 0, 142, 0, 306, 0, 0, 0, 0, 108, 0, 0, 0, 66, 114, 0, 0, 0, 0, 255, 0, 0, 0, 0, 0, 504, 0, 0, 221, 0, 0, 0, 154, 0, 0, 0, 326, 133, 167, 0, 0, 0]

def group19 := Transfer.assemble SpliceExtensionData.group7 template19 selection19
theorem group19_checked : group19.Checked := by
  apply Transfer.assemble_checked _ _ _ SpliceExtensionData.group7_checked <;> decide +kernel
theorem group19_size : group19.size = 132 := by decide +kernel

private def template20 : Group where
  k := 5
  pivot := [2, 0, 0, 2, 2, 2, 0, 0, 2, 2, 0]
  caps := ([576660812490, 579372263838] : List Nat).map Packed.cap
  tails := []
  upperMask := 38317675235260189
  lowerMask := 2417851600911583114152162
private def selection20 : List Nat := [16, 42, 20, 42, 27, 1327, 1, 3, 0, 4, 199, 0, 6, 2, 4, 375, 446, 450, 11, 0, 8, 0, 930, 3, 4, 371, 9, 1, 0, 0, 409, 9, 9, 55, 3, 8, 5, 2, 0, 0, 1, 567, 1264, 449, 0, 0, 18, 0, 3, 3, 9, 2, 0, 9, 0, 12, 718, 10, 5, 4, 0, 2, 0]

def group20 := Transfer.assemble SpliceExtensionData.group6 template20 selection20
theorem group20_checked : group20.Checked := by
  apply Transfer.assemble_checked _ _ _ SpliceExtensionData.group6_checked <;> decide +kernel
theorem group20_size : group20.size = 126 := by decide +kernel

private def template21 : Group where
  k := 5
  pivot := [2, 2, 2, 0, 1, 2, 2, 0, 1, 0, 0]
  caps := ([139993054390] : List Nat).map Packed.cap
  tails := []
  upperMask := 92236061992720933435
  lowerMask := 2417759403167265628478916
private def selection21 : List Nat := [87, 28, 60, 118, 125, 63, 69, 54, 217, 5, 3, 12, 16, 283, 107, 6, 30, 0, 24, 45, 0, 28, 326, 185, 39, 48, 109, 96, 76, 23, 68, 557, 545, 13, 1, 105, 38, 21, 8, 60, 142, 128, 0, 184, 338, 65, 56, 276, 21, 82, 19, 0, 88, 21, 156, 5, 54, 43, 111, 152, 29, 14, 190, 22, 92, 68, 103, 454, 30, 0, 22, 390, 0, 20, 117, 21, 0, 28, 0, 0, 188, 250, 99, 77, 0, 96, 25, 157, 2, 54, 46, 0, 80, 65, 190, 0, 35, 0, 0, 40, 7, 143, 53, 92, 42, 90, 0, 17, 11, 0, 0, 27, 0, 55, 81]

def group21 := Transfer.assemble SpliceExtensionData.group7 template21 selection21
theorem group21_checked : group21.Checked := by
  apply Transfer.assemble_checked _ _ _ SpliceExtensionData.group7_checked <;> decide +kernel
theorem group21_size : group21.size = 115 := by decide +kernel

private def template22 : Group where
  k := 5
  pivot := [2, 2, 0, 0, 2, 2, 0, 0, 1, 0, 1]
  caps := ([412005461535] : List Nat).map Packed.cap
  tails := []
  upperMask := 230595595830542214943
  lowerMask := 2417621043633427807197408
private def selection22 : List Nat := [44, 0, 0, 77, 73, 42, 111, 63, 0, 0, 36, 218, 75, 236, 0, 166, 13, 103, 0, 80, 35, 201, 250, 353, 137, 48, 0, 133, 13, 0, 82, 106, 0, 62, 50, 7, 60, 204, 151, 0, 101, 134, 0, 79, 12, 362, 154, 533, 265, 0, 172, 60, 244, 522, 69, 0, 0, 0, 116, 17, 0, 110, 142, 114, 105, 23, 90, 38, 119, 0, 75, 15, 146, 0, 760, 285, 17, 128, 47, 0, 74, 0, 81, 24, 133, 157, 0, 60, 41, 0, 99, 28, 14, 0, 34, 0, 58, 19, 36, 92, 108, 229, 0, 57, 37, 79, 0, 15, 143, 0, 20, 87, 0]

def group22 := Transfer.assemble SpliceExtensionData.group8 template22 selection22
theorem group22_checked : group22.Checked := by
  apply Transfer.assemble_checked _ _ _ SpliceExtensionData.group8_checked <;> decide +kernel
theorem group22_size : group22.size = 113 := by decide +kernel

private def template23 : Group where
  k := 5
  pivot := [2, 2, 2, 0, 1, 2, 2, 0, 1, 0, 0]
  caps := ([296943002841] : List Nat).map Packed.cap
  tails := []
  upperMask := 191492808455632433
  lowerMask := 2417851447736449893779918
private def selection23 : List Nat := [709, 560, 131, 43, 49, 335, 17, 377, 0, 171, 24, 80, 64, 52, 0, 14, 128, 7, 162, 22, 5, 0, 105, 0, 21, 21, 0, 80, 22, 39, 62, 29, 49, 43, 0, 25, 3, 7, 0, 82, 250, 150, 28, 181, 53, 29, 197, 0, 14, 86, 3, 20, 211, 103, 21, 472, 44, 478, 16, 90, 27, 281, 173, 13, 16, 273, 0, 195, 97, 151, 6, 0, 70, 12, 107, 0, 0, 70, 0, 37, 139, 154, 23, 15, 0, 241, 0, 68, 6, 113, 0, 0, 27, 0, 54, 158, 134, 32, 10, 88, 17, 52, 23, 114, 20, 39]

def group23 := Transfer.assemble SpliceExtensionData.group9 template23 selection23
theorem group23_checked : group23.Checked := by
  apply Transfer.assemble_checked _ _ _ SpliceExtensionData.group9_checked <;> decide +kernel
theorem group23_size : group23.size = 106 := by decide +kernel

end TBoards.SpliceTransferData
