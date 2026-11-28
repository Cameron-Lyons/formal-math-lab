import SpliceTransferData.Part018

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceTransferData
open Splice

private def template160 : Group where
  k := 5
  pivot := [1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 1]
  caps := ([569556559053] : List Nat).map Packed.cap
  tails := []
  upperMask := 23102598320125467
  lowerMask := 2417851616126660029286884
private def selection160 : List Nat := [1750]

def group160 := Transfer.assemble SpliceExtensionData.group13 template160 selection160
theorem group160_checked : group160.Checked := by
  apply Transfer.assemble_checked _ _ _ SpliceExtensionData.group13_checked <;> decide +kernel
theorem group160_size : group160.size = 1 := by decide +kernel

private def template161 : Group where
  k := 5
  pivot := [1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 1]
  caps := ([565008139647] : List Nat).map Packed.cap
  tails := []
  upperMask := 23665548214875675
  lowerMask := 2417851615563710134536676
private def selection161 : List Nat := [323]

def group161 := Transfer.assemble SpliceExtensionData.group12 template161 selection161
theorem group161_checked : group161.Checked := by
  apply Transfer.assemble_checked _ _ _ SpliceExtensionData.group12_checked <;> decide +kernel
theorem group161_size : group161.size = 1 := by decide +kernel

private def template162 : Group where
  k := 5
  pivot := [1, 1, 1, 0, 1, 2, 2, 0, 1, 0, 0]
  caps := ([294091458457] : List Nat).map Packed.cap
  tails := []
  upperMask := 92578334875058845240
  lowerMask := 2417759060894383290567111
private def selection162 : List Nat := [2585]

def group162 := Transfer.assemble SpliceExtensionData.group7 template162 selection162
theorem group162_checked : group162.Checked := by
  apply Transfer.assemble_checked _ _ _ SpliceExtensionData.group7_checked <;> decide +kernel
theorem group162_size : group162.size = 1 := by decide +kernel

private def template163 : Group where
  k := 5
  pivot := [1, 1, 1, 0, 1, 1, 0, 0, 1, 1, 1]
  caps := ([765810577495] : List Nat).map Packed.cap
  tails := []
  upperMask := 1520611971717582625060411
  lowerMask := 897239667511675724351940
private def selection163 : List Nat := [807]

def group163 := Transfer.assemble SpliceExtensionData.group9 template163 selection163
theorem group163_checked : group163.Checked := by
  apply Transfer.assemble_checked _ _ _ SpliceExtensionData.group9_checked <;> decide +kernel
theorem group163_size : group163.size = 1 := by decide +kernel

private def template164 : Group where
  k := 5
  pivot := [1, 0, 1, 0, 1, 2, 2, 0, 1, 1, 1]
  caps := ([282855997160] : List Nat).map Packed.cap
  tails := []
  upperMask := 9675607766574253618731
  lowerMask := 2408176031462684095793620
private def selection164 : List Nat := [5697]

def group164 := Transfer.assemble SpliceExtensionData.group7 template164 selection164
theorem group164_checked : group164.Checked := by
  apply Transfer.assemble_checked _ _ _ SpliceExtensionData.group7_checked <;> decide +kernel
theorem group164_size : group164.size = 1 := by decide +kernel

private def template165 : Group where
  k := 5
  pivot := [1, 0, 0, 2, 2, 2, 0, 0, 0, 2, 2]
  caps := ([31979137149] : List Nat).map Packed.cap
  tails := []
  upperMask := 221363216663219283743
  lowerMask := 2417630276012595130128608
private def selection165 : List Nat := [3392]

def group165 := Transfer.assemble SpliceExtensionData.group6 template165 selection165
theorem group165_checked : group165.Checked := by
  apply Transfer.assemble_checked _ _ _ SpliceExtensionData.group6_checked <;> decide +kernel
theorem group165_size : group165.size = 1 := by decide +kernel

private def template166 : Group where
  k := 5
  pivot := [1, 0, 0, 2, 2, 2, 0, 0, 0, 1, 0]
  caps := ([754199300812] : List Nat).map Packed.cap
  tails := []
  upperMask := 4731682180524172130074
  lowerMask := 2413119957048734177282277
private def selection166 : List Nat := [5016]

def group166 := Transfer.assemble SpliceExtensionData.group6 template166 selection166
theorem group166_checked : group166.Checked := by
  apply Transfer.assemble_checked _ _ _ SpliceExtensionData.group6_checked <;> decide +kernel
theorem group166_size : group166.size = 1 := by decide +kernel

private def template167 : Group where
  k := 5
  pivot := [1, 0, 0, 2, 2, 0, 0, 0, 1, 0, 1]
  caps := ([127260985530] : List Nat).map Packed.cap
  tails := []
  upperMask := 101828675697081857803
  lowerMask := 2417749810553561267554548
private def selection167 : List Nat := [3947]

def group167 := Transfer.assemble SpliceExtensionData.group8 template167 selection167
theorem group167_checked : group167.Checked := by
  apply Transfer.assemble_checked _ _ _ SpliceExtensionData.group8_checked <;> decide +kernel
theorem group167_size : group167.size = 1 := by decide +kernel

end TBoards.SpliceTransferData
