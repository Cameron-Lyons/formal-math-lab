import SpliceTransferData.Part016

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceTransferData
open Splice

private def template144 : Group where
  k := 5
  pivot := [1, 1, 0, 0, 2, 2, 2, 0, 0, 2, 2]
  caps := ([12220552404] : List Nat).map Packed.cap
  tails := []
  upperMask := 18737263188491122463
  lowerMask := 2417832901966069858289888
private def selection144 : List Nat := [2792, 40]

def group144 := Transfer.assemble SpliceExtensionData.group6 template144 selection144
theorem group144_checked : group144.Checked := by
  apply Transfer.assemble_checked _ _ _ SpliceExtensionData.group6_checked <;> decide +kernel
theorem group144_size : group144.size = 2 := by decide +kernel

private def template145 : Group where
  k := 5
  pivot := [1, 1, 0, 0, 1, 2, 2, 0, 1, 0, 1]
  caps := ([324353305512] : List Nat).map Packed.cap
  tails := []
  upperMask := 249186508318247097403
  lowerMask := 2417602452720940102314948
private def selection145 : List Nat := [3003, 0]

def group145 := Transfer.assemble SpliceExtensionData.group9 template145 selection145
theorem group145_checked : group145.Checked := by
  apply Transfer.assemble_checked _ _ _ SpliceExtensionData.group9_checked <;> decide +kernel
theorem group145_size : group145.size = 2 := by decide +kernel

private def template146 : Group where
  k := 5
  pivot := [1, 0, 1, 0, 1, 2, 2, 0, 1, 1, 0]
  caps := ([554805295978] : List Nat).map Packed.cap
  tails := []
  upperMask := 28438069464896517651
  lowerMask := 2417823201159793452894700
private def selection146 : List Nat := [221, 21]

def group146 := Transfer.assemble SpliceExtensionData.group9 template146 selection146
theorem group146_checked : group146.Checked := by
  apply Transfer.assemble_checked _ _ _ SpliceExtensionData.group9_checked <;> decide +kernel
theorem group146_size : group146.size = 2 := by decide +kernel

private def template147 : Group where
  k := 5
  pivot := [0, 2, 2, 2, 0, 0, 0, 0, 2, 2, 0]
  caps := ([381310052836] : List Nat).map Packed.cap
  tails := []
  upperMask := 4758090084719539735
  lowerMask := 2417846881139173629872616
private def selection147 : List Nat := [937, 1424]

def group147 := Transfer.assemble SpliceExtensionData.group6 template147 selection147
theorem group147_checked : group147.Checked := by
  apply Transfer.assemble_checked _ _ _ SpliceExtensionData.group6_checked <;> decide +kernel
theorem group147_size : group147.size = 2 := by decide +kernel

private def template148 : Group where
  k := 5
  pivot := [0, 1, 1, 0, 1, 2, 2, 0, 1, 0, 1]
  caps := ([299764613705] : List Nat).map Packed.cap
  tails := []
  upperMask := 28122817626473378355
  lowerMask := 2417823516411631876033996
private def selection148 : List Nat := [555, 10]

def group148 := Transfer.assemble SpliceExtensionData.group7 template148 selection148
theorem group148_checked : group148.Checked := by
  apply Transfer.assemble_checked _ _ _ SpliceExtensionData.group7_checked <;> decide +kernel
theorem group148_size : group148.size = 2 := by decide +kernel

private def template149 : Group where
  k := 5
  pivot := [0, 1, 0, 0, 2, 2, 2, 0, 0, 2, 2]
  caps := ([427760778870] : List Nat).map Packed.cap
  tails := []
  upperMask := 18602155338115592991
  lowerMask := 2417833037073920233819360
private def selection149 : List Nat := [3991, 5]

def group149 := Transfer.assemble SpliceExtensionData.group8 template149 selection149
theorem group149_checked : group149.Checked := by
  apply Transfer.assemble_checked _ _ _ SpliceExtensionData.group8_checked <;> decide +kernel
theorem group149_size : group149.size = 2 := by decide +kernel

private def template150 : Group where
  k := 5
  pivot := [0, 1, 0, 0, 2, 2, 0, 0, 1, 1, 0]
  caps := ([296785094174, 377024182118] : List Nat).map Packed.cap
  tails := []
  upperMask := 83490018217366402333
  lowerMask := 2417768149211040983010018
private def selection150 : List Nat := [687]

def group150 := Transfer.assemble SpliceExtensionData.group8 template150 selection150
theorem group150_checked : group150.Checked := by
  apply Transfer.assemble_checked _ _ _ SpliceExtensionData.group8_checked <;> decide +kernel
theorem group150_size : group150.size = 2 := by decide +kernel

private def template151 : Group where
  k := 5
  pivot := [0, 1, 0, 0, 2, 2, 0, 0, 1, 0, 1]
  caps := ([275973324471] : List Nat).map Packed.cap
  tails := []
  upperMask := 4814926750602116478735
  lowerMask := 2413036712478656232933616
private def selection151 : List Nat := [4769, 33]

def group151 := Transfer.assemble SpliceExtensionData.group6 template151 selection151
theorem group151_checked : group151.Checked := by
  apply Transfer.assemble_checked _ _ _ SpliceExtensionData.group6_checked <;> decide +kernel
theorem group151_size : group151.size = 2 := by decide +kernel

end TBoards.SpliceTransferData
