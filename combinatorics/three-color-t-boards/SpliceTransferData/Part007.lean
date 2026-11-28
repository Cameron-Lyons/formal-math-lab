import SpliceTransferData.Part005

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceTransferData
open Splice

private def template56 : Group where
  k := 5
  pivot := [1, 0, 0, 2, 2, 2, 2, 0, 1, 1, 0]
  caps := ([194356719986, 194356759350, 194371062332, 194371101696] : List Nat).map Packed.cap
  tails := []
  upperMask := 1511968981448107475882870
  lowerMask := 905882657781150873529481
private def selection56 : List Nat := [45, 67, 0, 80, 0, 180, 0, 0]

def group56 := Transfer.assemble SpliceData.group7 template56 selection56
theorem group56_checked : group56.Checked := by
  apply Transfer.assemble_checked _ _ _ SpliceData.group7_checked <;> decide +kernel
theorem group56_size : group56.size = 32 := by decide +kernel

private def template57 : Group where
  k := 5
  pivot := [2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1]
  caps := ([573718708837] : List Nat).map Packed.cap
  tails := []
  upperMask := 1708316287412872400822304
  lowerMask := 709535351816385948590047
private def selection57 : List Nat := [112, 101, 0, 100, 0, 0, 9, 0, 1, 11, 2, 9, 44, 20, 0, 45, 4, 56, 47, 23, 20, 0, 117, 20, 58, 5, 36, 58, 106, 95, 121]

def group57 := Transfer.assemble SpliceData.group4 template57 selection57
theorem group57_checked : group57.Checked := by
  apply Transfer.assemble_checked _ _ _ SpliceData.group4_checked <;> decide +kernel
theorem group57_size : group57.size = 31 := by decide +kernel

private def template58 : Group where
  k := 5
  pivot := [2, 2, 0, 0, 2, 2, 0, 0, 1, 0, 0]
  caps := ([412005461536] : List Nat).map Packed.cap
  tails := []
  upperMask := 239818967936116466463
  lowerMask := 2417611820261322232945888
private def selection58 : List Nat := [78, 145, 965, 317, 0, 329, 21, 103, 313, 473, 1411, 1964, 0, 311, 496, 58, 288, 975, 49, 0, 488, 283, 388, 195, 0, 94, 0, 0]

def group58 := Transfer.assemble SpliceExtensionData.group8 template58 selection58
theorem group58_checked : group58.Checked := by
  apply Transfer.assemble_checked _ _ _ SpliceExtensionData.group8_checked <;> decide +kernel
theorem group58_size : group58.size = 28 := by decide +kernel

private def template59 : Group where
  k := 5
  pivot := [2, 0, 0, 2, 2, 2, 0, 0, 2, 2, 0]
  caps := ([596816243856, 599747899816] : List Nat).map Packed.cap
  tails := []
  upperMask := 146404066292152087
  lowerMask := 2417851492825192057260264
private def selection59 : List Nat := [442, 3, 207, 1425, 903, 16, 2105, 3, 42, 2003, 11, 744, 14]

def group59 := Transfer.assemble SpliceExtensionData.group6 template59 selection59
theorem group59_checked : group59.Checked := by
  apply Transfer.assemble_checked _ _ _ SpliceExtensionData.group6_checked <;> decide +kernel
theorem group59_size : group59.size = 26 := by decide +kernel

private def template60 : Group where
  k := 5
  pivot := [0, 0, 1, 0, 1, 2, 2, 0, 1, 2, 2]
  caps := ([51963956407] : List Nat).map Packed.cap
  tails := []
  upperMask := 92524292366725161531
  lowerMask := 2417759114936891624250820
private def selection60 : List Nat := [3216, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def group60 := Transfer.assemble SpliceExtensionData.group7 template60 selection60
theorem group60_checked : group60.Checked := by
  apply Transfer.assemble_checked _ _ _ SpliceExtensionData.group7_checked <;> decide +kernel
theorem group60_size : group60.size = 23 := by decide +kernel

private def template61 : Group where
  k := 5
  pivot := [2, 2, 0, 0, 2, 2, 0, 0, 1, 0, 0]
  caps := ([126659658891] : List Nat).map Packed.cap
  tails := []
  upperMask := 166311215780315010831
  lowerMask := 2417685328013478034401520
private def selection61 : List Nat := [234, 15, 524, 767, 0, 48, 327, 1903, 944, 166, 217, 255, 1179, 889, 93, 0, 37, 59, 314, 52, 352]

def group61 := Transfer.assemble SpliceExtensionData.group6 template61 selection61
theorem group61_checked : group61.Checked := by
  apply Transfer.assemble_checked _ _ _ SpliceExtensionData.group6_checked <;> decide +kernel
theorem group61_size : group61.size = 21 := by decide +kernel

private def template62 : Group where
  k := 5
  pivot := [2, 2, 0, 0, 2, 2, 0, 0, 1, 0, 0]
  caps := ([387555208226] : List Nat).map Packed.cap
  tails := []
  upperMask := 9414812098279781661
  lowerMask := 2417842224417160069630690
private def selection62 : List Nat := [1182, 0, 426, 116, 703, 134, 100, 2230, 344, 1194, 399, 345, 172, 713, 220, 1650, 193, 0]

def group62 := Transfer.assemble SpliceExtensionData.group8 template62 selection62
theorem group62_checked : group62.Checked := by
  apply Transfer.assemble_checked _ _ _ SpliceExtensionData.group8_checked <;> decide +kernel
theorem group62_size : group62.size = 18 := by decide +kernel

private def template63 : Group where
  k := 5
  pivot := [1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1]
  caps := ([99227750529] : List Nat).map Packed.cap
  tails := []
  upperMask := 73792063945027253787
  lowerMask := 2417777847165313322158564
private def selection63 : List Nat := [167, 196, 722, 7, 12, 0, 376, 12, 0, 35, 2, 206, 0, 173, 137, 291, 0, 314]

def group63 := Transfer.assemble SpliceExtensionData.group13 template63 selection63
theorem group63_checked : group63.Checked := by
  apply Transfer.assemble_checked _ _ _ SpliceExtensionData.group13_checked <;> decide +kernel
theorem group63_size : group63.size = 18 := by decide +kernel

end TBoards.SpliceTransferData
