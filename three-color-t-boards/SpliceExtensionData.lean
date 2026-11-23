import SpliceExtensionData.Group012Part002
import SpliceExtensionData.Group013Part001
import SpliceExtensionData.Group014Part003

-- Generated from splice_extension.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceExtensionData
open Splice

def group0 := Group.assemble template0 [cap0_0] [tail0_0, tail0_1, tail0_2, tail0_3, tail0_4]
theorem group0_checked : group0.Checked := by
  apply Group.assemble_checked <;> decide +kernel
private theorem group0_size : group0.size = 8420 := by decide +kernel

def group1 := Group.assemble template1 [cap1_0] [tail1_0, tail1_1, tail1_2, tail1_3, tail1_4]
theorem group1_checked : group1.Checked := by
  apply Group.assemble_checked <;> decide +kernel
private theorem group1_size : group1.size = 9984 := by decide +kernel

def group2 := Group.assemble template2 [cap2_0] [tail2_0, tail2_1, tail2_2, tail2_3]
theorem group2_checked : group2.Checked := by
  apply Group.assemble_checked <;> decide +kernel
private theorem group2_size : group2.size = 7988 := by decide +kernel

def group3 := Group.assemble template3 [cap3_0] [tail3_0, tail3_1, tail3_2, tail3_3, tail3_4, tail3_5, tail3_6, tail3_7]
theorem group3_checked : group3.Checked := by
  apply Group.assemble_checked <;> decide +kernel
private theorem group3_size : group3.size = 22374 := by decide +kernel

def group4 := Group.assemble template4 [cap4_0] [tail4_0, tail4_1, tail4_2, tail4_3, tail4_4, tail4_5, tail4_6, tail4_7, tail4_8, tail4_9, tail4_10, tail4_11, tail4_12, tail4_13, tail4_14]
theorem group4_checked : group4.Checked := by
  apply Group.assemble_checked <;> decide +kernel
private theorem group4_size : group4.size = 28844 := by decide +kernel

def group5 := Group.assemble template5 [cap5_0] [tail5_0, tail5_1, tail5_2, tail5_3, tail5_4, tail5_5, tail5_6, tail5_7, tail5_8, tail5_9, tail5_10, tail5_11, tail5_12, tail5_13, tail5_14, tail5_15, tail5_16, tail5_17, tail5_18, tail5_19, tail5_20, tail5_21, tail5_22, tail5_23, tail5_24, tail5_25, tail5_26, tail5_27, tail5_28, tail5_29, tail5_30, tail5_31, tail5_32, tail5_33, tail5_34, tail5_35, tail5_36, tail5_37, tail5_38, tail5_39]
theorem group5_checked : group5.Checked := by
  apply Group.assemble_checked <;> decide +kernel
private theorem group5_size : group5.size = 80908 := by decide +kernel

def group6 := Group.assemble template6 [cap6_0] [tail6_0, tail6_1, tail6_2, tail6_3, tail6_4, tail6_5, tail6_6, tail6_7, tail6_8, tail6_9, tail6_10, tail6_11, tail6_12, tail6_13, tail6_14, tail6_15, tail6_16]
theorem group6_checked : group6.Checked := by
  apply Group.assemble_checked <;> decide +kernel
private theorem group6_size : group6.size = 100788 := by decide +kernel

def group7 := Group.assemble template7 [cap7_0] [tail7_0, tail7_1, tail7_2, tail7_3, tail7_4, tail7_5, tail7_6, tail7_7, tail7_8, tail7_9, tail7_10, tail7_11, tail7_12, tail7_13, tail7_14, tail7_15, tail7_16, tail7_17, tail7_18]
theorem group7_checked : group7.Checked := by
  apply Group.assemble_checked <;> decide +kernel
private theorem group7_size : group7.size = 112860 := by decide +kernel

def group8 := Group.assemble template8 [cap8_0] [tail8_0, tail8_1, tail8_2, tail8_3, tail8_4, tail8_5, tail8_6, tail8_7, tail8_8, tail8_9, tail8_10, tail8_11, tail8_12, tail8_13, tail8_14, tail8_15, tail8_16, tail8_17, tail8_18, tail8_19]
theorem group8_checked : group8.Checked := by
  apply Group.assemble_checked <;> decide +kernel
private theorem group8_size : group8.size = 121800 := by decide +kernel

def group9 := Group.assemble template9 [cap9_0] [tail9_0, tail9_1, tail9_2, tail9_3, tail9_4, tail9_5, tail9_6, tail9_7, tail9_8, tail9_9, tail9_10, tail9_11, tail9_12, tail9_13, tail9_14, tail9_15, tail9_16, tail9_17, tail9_18]
theorem group9_checked : group9.Checked := by
  apply Group.assemble_checked <;> decide +kernel
private theorem group9_size : group9.size = 111360 := by decide +kernel

def group10 := Group.assemble template10 [cap10_0] [tail10_0, tail10_1, tail10_2, tail10_3, tail10_4, tail10_5, tail10_6, tail10_7, tail10_8, tail10_9, tail10_10, tail10_11, tail10_12, tail10_13, tail10_14, tail10_15, tail10_16, tail10_17]
theorem group10_checked : group10.Checked := by
  apply Group.assemble_checked <;> decide +kernel
private theorem group10_size : group10.size = 70792 := by decide +kernel

def group11 := Group.assemble template11 [cap11_0] [tail11_0, tail11_1, tail11_2, tail11_3, tail11_4, tail11_5, tail11_6, tail11_7, tail11_8, tail11_9, tail11_10, tail11_11, tail11_12, tail11_13, tail11_14, tail11_15, tail11_16]
theorem group11_checked : group11.Checked := by
  apply Group.assemble_checked <;> decide +kernel
private theorem group11_size : group11.size = 67408 := by decide +kernel

def group12 := Group.assemble template12 [cap12_0] [tail12_0, tail12_1, tail12_2, tail12_3, tail12_4, tail12_5, tail12_6, tail12_7, tail12_8]
theorem group12_checked : group12.Checked := by
  apply Group.assemble_checked <;> decide +kernel
private theorem group12_size : group12.size = 45903 := by decide +kernel

def group13 := Group.assemble template13 [cap13_0] [tail13_0, tail13_1, tail13_2, tail13_3, tail13_4, tail13_5]
theorem group13_checked : group13.Checked := by
  apply Group.assemble_checked <;> decide +kernel
private theorem group13_size : group13.size = 22520 := by decide +kernel

def group14 := Group.assemble template14 [cap14_0] [tail14_0, tail14_1, tail14_2, tail14_3, tail14_4, tail14_5, tail14_6, tail14_7, tail14_8, tail14_9, tail14_10, tail14_11, tail14_12]
theorem group14_checked : group14.Checked := by
  apply Group.assemble_checked <;> decide +kernel
private theorem group14_size : group14.size = 32780 := by decide +kernel

def groups : List Group := [group0, group1, group2, group3, group4, group5, group6, group7, group8, group9, group10, group11, group12, group13, group14]

theorem checked : ∀ g ∈ groups, g.Checked := by
  simp only [groups, List.forall_mem_cons, List.not_mem_nil, false_implies,
    implies_true, and_true]
  exact ⟨group0_checked, group1_checked, group2_checked, group3_checked, group4_checked, group5_checked, group6_checked, group7_checked, group8_checked, group9_checked, group10_checked, group11_checked, group12_checked, group13_checked, group14_checked⟩

theorem size_sum : (groups.map Group.size).sum = 844729 := by
  simp only [groups, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    group0_size, group1_size, group2_size, group3_size, group4_size, group5_size, group6_size, group7_size, group8_size, group9_size, group10_size, group11_size, group12_size, group13_size, group14_size] <;> decide

def markers : List (List Nat) := [
  [0, 1, 0, 1, 1, 0, 2, 1, 1, 1, 1, 2, 0],
  [0, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 0],
  [0, 0, 0, 1, 2, 2, 2, 2, 1, 2, 0, 2, 0],
  [1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1],
  [2, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 2],
  [2, 0, 0, 0, 2, 1, 1, 1, 2, 2, 0, 0, 2],
  [1, 1, 0, 2, 0, 2, 2, 1, 1, 0, 1, 0, 1],
  [0, 1, 0, 0, 1, 2, 2, 2, 0, 1, 1, 0, 0],
  [2, 1, 0, 0, 1, 2, 2, 2, 2, 1, 1, 0, 2],
  [2, 1, 2, 1, 2, 0, 1, 2, 1, 2, 0, 0, 2],
  [0, 1, 0, 0, 1, 2, 2, 0, 2, 1, 1, 0, 0],
  [2, 1, 0, 0, 1, 2, 2, 0, 2, 1, 1, 0, 2],
  [1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1],
  [1, 2, 2, 0, 1, 1, 2, 1, 2, 2, 2, 2, 1],
  [1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1],
  [0, 1, 0, 0, 1, 0, 1, 2, 1, 1, 1, 0, 0],
  [1, 2, 2, 1, 0, 2, 1, 1, 0, 0, 2, 2, 1],
  [0, 2, 2, 0, 0, 2, 2, 0, 0, 2, 2, 2, 0],
  [1, 2, 2, 0, 0, 2, 2, 0, 0, 2, 2, 2, 1],
  [0, 2, 2, 2, 0, 1, 2, 2, 0, 1, 2, 2, 0],
  [1, 2, 2, 2, 0, 1, 2, 2, 0, 1, 2, 2, 1],
  [1, 2, 2, 2, 2, 0, 1, 2, 2, 0, 2, 2, 1],
  [1, 2, 2, 2, 2, 1, 0, 2, 2, 1, 2, 2, 1],
  [0, 2, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 0],
  [0, 1, 2, 2, 2, 1, 1, 2, 2, 1, 1, 2, 0],
  [1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1],
  [0, 2, 2, 1, 2, 2, 1, 2, 0, 1, 2, 2, 0],
  [1, 2, 2, 1, 2, 2, 1, 2, 0, 1, 2, 2, 1]]
end TBoards.SpliceExtensionData
