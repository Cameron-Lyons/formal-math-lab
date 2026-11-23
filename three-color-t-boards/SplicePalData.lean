import SplicePalData.Group008Part002
import SplicePalData.Group009Part000
import SplicePalData.Group010Part002

-- Generated from splice_pal.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SplicePalData
open Splice

def group0 := Group.assemble template0 [cap0_0] [tail0_0, tail0_1, tail0_2, tail0_3]
theorem group0_checked : group0.Checked := by
  apply Group.assemble_checked <;> decide +kernel
private theorem group0_size : group0.size = 3876 := by decide +kernel

def group1 := Group.assemble template1 [cap1_0] [tail1_0, tail1_1, tail1_2, tail1_3, tail1_4, tail1_5, tail1_6, tail1_7, tail1_8]
theorem group1_checked : group1.Checked := by
  apply Group.assemble_checked <;> decide +kernel
private theorem group1_size : group1.size = 8980 := by decide +kernel

def group2 := Group.assemble template2 [cap2_0] [tail2_0]
theorem group2_checked : group2.Checked := by
  apply Group.assemble_checked <;> decide +kernel
private theorem group2_size : group2.size = 424 := by decide +kernel

def group3 := Group.assemble template3 [cap3_0] [tail3_0]
theorem group3_checked : group3.Checked := by
  apply Group.assemble_checked <;> decide +kernel
private theorem group3_size : group3.size = 96 := by decide +kernel

def group4 := Group.assemble template4 [cap4_0] [tail4_0]
theorem group4_checked : group4.Checked := by
  apply Group.assemble_checked <;> decide +kernel
private theorem group4_size : group4.size = 16 := by decide +kernel

def group5 := Group.assemble template5 [cap5_0] [tail5_0]
theorem group5_checked : group5.Checked := by
  apply Group.assemble_checked <;> decide +kernel
private theorem group5_size : group5.size = 80 := by decide +kernel

def group6 := Group.assemble template6 [cap6_0] [tail6_0]
theorem group6_checked : group6.Checked := by
  apply Group.assemble_checked <;> decide +kernel
private theorem group6_size : group6.size = 16 := by decide +kernel

def group7 := Group.assemble template7 [cap7_0] [tail7_0, tail7_1, tail7_2, tail7_3, tail7_4]
theorem group7_checked : group7.Checked := by
  apply Group.assemble_checked <;> decide +kernel
private theorem group7_size : group7.size = 4336 := by decide +kernel

def group8 := Group.assemble template8 [cap8_0] [tail8_0, tail8_1, tail8_2, tail8_3, tail8_4, tail8_5, tail8_6, tail8_7, tail8_8, tail8_9]
theorem group8_checked : group8.Checked := by
  apply Group.assemble_checked <;> decide +kernel
private theorem group8_size : group8.size = 9628 := by decide +kernel

def group9 := Group.assemble template9 [cap9_0] [tail9_0, tail9_1, tail9_2, tail9_3]
theorem group9_checked : group9.Checked := by
  apply Group.assemble_checked <;> decide +kernel
private theorem group9_size : group9.size = 3776 := by decide +kernel

def group10 := Group.assemble template10 [cap10_0] [tail10_0, tail10_1, tail10_2, tail10_3, tail10_4, tail10_5, tail10_6, tail10_7, tail10_8, tail10_9, tail10_10]
theorem group10_checked : group10.Checked := by
  apply Group.assemble_checked <;> decide +kernel
private theorem group10_size : group10.size = 10868 := by decide +kernel

def groups : List Group := [group0, group1, group2, group3, group4, group5, group6, group7, group8, group9, group10]

theorem checked : ∀ g ∈ groups, g.Checked := by
  simp only [groups, List.forall_mem_cons, List.not_mem_nil, false_implies,
    implies_true, and_true]
  exact ⟨group0_checked, group1_checked, group2_checked, group3_checked, group4_checked, group5_checked, group6_checked, group7_checked, group8_checked, group9_checked, group10_checked⟩

theorem size_sum : (groups.map Group.size).sum = 42096 := by
  simp only [groups, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    group0_size, group1_size, group2_size, group3_size, group4_size, group5_size, group6_size, group7_size, group8_size, group9_size, group10_size] <;> decide

end TBoards.SplicePalData
