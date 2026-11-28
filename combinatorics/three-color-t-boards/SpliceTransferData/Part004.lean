import SpliceTransferData.Part002

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceTransferData
open Splice

private def template32 : Group where
  k := 5
  pivot := [0, 1, 0, 0, 1, 2, 2, 0, 1, 2, 2]
  caps := ([129455936760, 376635700272] : List Nat).map Packed.cap
  tails := []
  upperMask := 9414864845041972275
  lowerMask := 2417842224364413307440076
private def selection32 : List Nat := [2785, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def group32 := Transfer.assemble SpliceExtensionData.group9 template32 selection32
theorem group32_checked : group32.Checked := by
  apply Transfer.assemble_checked _ _ _ SpliceExtensionData.group9_checked <;> decide +kernel
theorem group32_size : group32.size = 68 := by decide +kernel

private def template33 : Group where
  k := 5
  pivot := [0, 1, 1, 0, 1, 2, 2, 0, 1, 2, 2]
  caps := ([388238572920] : List Nat).map Packed.cap
  tails := []
  upperMask := 92524291816969351739
  lowerMask := 2417759114937441380060612
private def selection33 : List Nat := [2533, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def group33 := Transfer.assemble SpliceExtensionData.group7 template33 selection33
theorem group33_checked : group33.Checked := by
  apply Transfer.assemble_checked _ _ _ SpliceExtensionData.group7_checked <;> decide +kernel
theorem group33_size : group33.size = 64 := by decide +kernel

private def template34 : Group where
  k := 5
  pivot := [0, 0, 1, 0, 1, 2, 2, 0, 1, 2, 2]
  caps := ([127287744355] : List Nat).map Packed.cap
  tails := []
  upperMask := 92524291819116835371
  lowerMask := 2417759114937439232576980
private def selection34 : List Nat := [2533, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def group34 := Transfer.assemble SpliceExtensionData.group7 template34 selection34
theorem group34_checked : group34.Checked := by
  apply Transfer.assemble_checked _ _ _ SpliceExtensionData.group7_checked <;> decide +kernel
theorem group34_size : group34.size = 64 := by decide +kernel

private def template35 : Group where
  k := 5
  pivot := [0, 0, 0, 0, 2, 2, 0, 0, 2, 2, 2]
  caps := ([137701881234] : List Nat).map Packed.cap
  tails := []
  upperMask := 9261689712090035485
  lowerMask := 2417842377539546259376866
private def selection35 : List Nat := [2479, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def group35 := Transfer.assemble SpliceExtensionData.group6 template35 selection35
theorem group35_checked : group35.Checked := by
  apply Transfer.assemble_checked _ _ _ SpliceExtensionData.group6_checked <;> decide +kernel
theorem group35_size : group35.size = 56 := by decide +kernel

private def template36 : Group where
  k := 5
  pivot := [1, 0, 0, 0, 2, 2, 0, 0, 2, 2, 2]
  caps := ([4084901229] : List Nat).map Packed.cap
  tails := []
  upperMask := 221363216663219283743
  lowerMask := 2417630276012595130128608
private def selection36 : List Nat := [3372, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def group36 := Transfer.assemble SpliceExtensionData.group6 template36 selection36
theorem group36_checked : group36.Checked := by
  apply Transfer.assemble_checked _ _ _ SpliceExtensionData.group6_checked <;> decide +kernel
theorem group36_size : group36.size = 55 := by decide +kernel

private def template37 : Group where
  k := 5
  pivot := [2, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1]
  caps := ([11801739528, 14513190876, 31957170894, 36432603238, 98936481496, 99227711164] : List Nat).map Packed.cap
  tails := []
  upperMask := 5651149839611419
  lowerMask := 2417851633578108509800932
private def selection37 : List Nat := [366, 323, 982, 973, 333, 806, 101, 0, 53]

def group37 := Transfer.assemble SpliceExtensionData.group12 template37 selection37
theorem group37_checked : group37.Checked := by
  apply Transfer.assemble_checked _ _ _ SpliceExtensionData.group12_checked <;> decide +kernel
theorem group37_size : group37.size = 54 := by decide +kernel

private def template38 : Group where
  k := 5
  pivot := [2, 2, 2, 0, 1, 2, 2, 0, 1, 0, 1]
  caps := ([139993054389] : List Nat).map Packed.cap
  tails := []
  upperMask := 83012689887146681915
  lowerMask := 2417768626539371202730436
private def selection38 : List Nat := [78, 0, 5, 0, 53, 0, 128, 516, 328, 62, 10, 411, 279, 68, 1605, 22, 14, 5, 337, 561, 63, 39, 160, 28, 255, 27, 0, 616, 684, 32, 34, 51, 183, 309, 0, 0, 268, 80, 13, 79, 18, 437, 35, 97, 256, 437, 141, 9, 37, 36, 50, 33, 333]

def group38 := Transfer.assemble SpliceExtensionData.group7 template38 selection38
theorem group38_checked : group38.Checked := by
  apply Transfer.assemble_checked _ _ _ SpliceExtensionData.group7_checked <;> decide +kernel
theorem group38_size : group38.size = 53 := by decide +kernel

private def template39 : Group where
  k := 5
  pivot := [2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1]
  caps := ([8859635875] : List Nat).map Packed.cap
  tails := []
  upperMask := 1708316269398473891340321
  lowerMask := 709535369830784458072030
private def selection39 : List Nat := [127, 0, 0, 0, 202, 16, 170, 0, 0, 0, 21, 19, 0, 0, 19, 8, 55, 0, 0, 16, 0, 14, 0, 56, 62, 181, 61, 181, 86, 31, 52, 42, 63, 0, 4, 65, 170, 102, 0, 67, 45, 8, 14, 24, 6, 146, 86, 17, 36, 104, 77]

def group39 := Transfer.assemble SpliceData.group1 template39 selection39
theorem group39_checked : group39.Checked := by
  apply Transfer.assemble_checked _ _ _ SpliceData.group1_checked <;> decide +kernel
theorem group39_size : group39.size = 51 := by decide +kernel

end TBoards.SpliceTransferData
