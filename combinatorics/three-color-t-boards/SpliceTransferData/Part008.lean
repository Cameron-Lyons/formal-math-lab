import SpliceTransferData.Part006

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceTransferData
open Splice

private def template64 : Group where
  k := 5
  pivot := [2, 0, 1, 2, 2, 1, 2, 2, 1, 2, 0]
  caps := ([599786526819] : List Nat).map Packed.cap
  tails := []
  upperMask := 149834511927129619
  lowerMask := 2417851489394746422282732
private def selection64 : List Nat := [727, 64, 1101, 33, 14, 0, 4, 32, 20, 185, 0, 0, 228, 1679, 5, 13, 566]

def group64 := Transfer.assemble SpliceExtensionData.group14 template64 selection64
theorem group64_checked : group64.Checked := by
  apply Transfer.assemble_checked _ _ _ SpliceExtensionData.group14_checked <;> decide +kernel
theorem group64_size : group64.size = 17 := by decide +kernel

private def template65 : Group where
  k := 5
  pivot := [2, 0, 0, 1, 2, 2, 2, 0, 1, 1, 0]
  caps := ([100227883748, 100227923112] : List Nat).map Packed.cap
  tails := []
  upperMask := 1513739868865989453304694
  lowerMask := 904111770363268896107657
private def selection65 : List Nat := [217, 0, 0, 0, 0, 0, 0, 0]

def group65 := Transfer.assemble SpliceData.group7 template65 selection65
theorem group65_checked : group65.Checked := by
  apply Transfer.assemble_checked _ _ _ SpliceData.group7_checked <;> decide +kernel
theorem group65_size : group65.size = 16 := by decide +kernel

private def template66 : Group where
  k := 5
  pivot := [0, 1, 0, 0, 0, 1, 2, 2, 0, 2, 2]
  caps := ([129059659324, 287267499568] : List Nat).map Packed.cap
  tails := []
  upperMask := 9432879273683727410
  lowerMask := 2417842206349984665684941
private def selection66 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0]

def group66 := Transfer.assemble SpliceExtensionData.group10 template66 selection66
theorem group66_checked : group66.Checked := by
  apply Transfer.assemble_checked _ _ _ SpliceExtensionData.group10_checked <;> decide +kernel
theorem group66_size : group66.size = 16 := by decide +kernel

private def template67 : Group where
  k := 5
  pivot := [2, 1, 2, 1, 1, 2, 2, 1, 2, 2, 1]
  caps := ([1355771926, 5056208662, 129413048394, 137153781856, 287127022572] : List Nat).map Packed.cap
  tails := []
  upperMask := 5651149839611419
  lowerMask := 2417851633578108509800932
private def selection67 : List Nat := [3411, 0, 689]

def group67 := Transfer.assemble SpliceExtensionData.group12 template67 selection67
theorem group67_checked : group67.Checked := by
  apply Transfer.assemble_checked _ _ _ SpliceExtensionData.group12_checked <;> decide +kernel
theorem group67_size : group67.size = 15 := by decide +kernel

private def template68 : Group where
  k := 5
  pivot := [2, 0, 0, 0, 2, 2, 2, 0, 0, 1, 0]
  caps := ([569687418105] : List Nat).map Packed.cap
  tails := []
  upperMask := 4722422814943255475997
  lowerMask := 2413129216414315093936354
private def selection68 : List Nat := [1354, 0, 1959, 760, 0, 0, 1283, 579, 1356, 0, 0, 0, 0, 106, 449]

def group68 := Transfer.assemble SpliceExtensionData.group6 template68 selection68
theorem group68_checked : group68.Checked := by
  apply Transfer.assemble_checked _ _ _ SpliceExtensionData.group6_checked <;> decide +kernel
theorem group68_size : group68.size = 15 := by decide +kernel

private def template69 : Group where
  k := 5
  pivot := [1, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1]
  caps := ([9935803900] : List Nat).map Packed.cap
  tails := []
  upperMask := 1708353162886346432536609
  lowerMask := 709498476342911916875742
private def selection69 : List Nat := [176, 0, 0, 8, 21, 0, 47, 21, 12, 0, 1155, 63, 0, 4, 65]

def group69 := Transfer.assemble SpliceData.group1 template69 selection69
theorem group69_checked : group69.Checked := by
  apply Transfer.assemble_checked _ _ _ SpliceData.group1_checked <;> decide +kernel
theorem group69_size : group69.size = 15 := by decide +kernel

private def template70 : Group where
  k := 5
  pivot := [2, 0, 1, 2, 2, 1, 2, 2, 1, 2, 0]
  caps := ([701030799981] : List Nat).map Packed.cap
  tails := []
  upperMask := 147579671913527678491
  lowerMask := 2417704059557344821733860
private def selection70 : List Nat := [2544, 455, 953, 0, 352, 663, 0, 3, 16, 35, 4, 56, 600]

def group70 := Transfer.assemble SpliceExtensionData.group14 template70 selection70
theorem group70_checked : group70.Checked := by
  apply Transfer.assemble_checked _ _ _ SpliceExtensionData.group14_checked <;> decide +kernel
theorem group70_size : group70.size = 13 := by decide +kernel

private def template71 : Group where
  k := 5
  pivot := [2, 0, 1, 2, 2, 1, 2, 2, 1, 2, 0]
  caps := ([606764346993] : List Nat).map Packed.cap
  tails := []
  upperMask := 293949700002985483
  lowerMask := 2417851345279558346426868
private def selection71 : List Nat := [97, 28, 12, 0, 0, 0, 80, 1868, 229, 77, 1597, 179, 80]

def group71 := Transfer.assemble SpliceExtensionData.group14 template71 selection71
theorem group71_checked : group71.Checked := by
  apply Transfer.assemble_checked _ _ _ SpliceExtensionData.group14_checked <;> decide +kernel
theorem group71_size : group71.size = 13 := by decide +kernel

end TBoards.SpliceTransferData
