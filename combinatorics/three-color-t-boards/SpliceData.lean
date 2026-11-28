import SpliceData.Batch0181
import SpliceData.Batch0182
import SpliceData.Batch0183

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceData
open Splice

def group0 := Group.assemble template0 [batch0000] [batch0001, batch0002, batch0003]
theorem group0_checked : group0.Checked := by
  apply Group.assemble_checked <;> decide +kernel

def group1 := Group.assemble template1 [batch0004] [batch0005, batch0006, batch0007, batch0008, batch0009, batch0010, batch0011, batch0012, batch0013, batch0014, batch0015, batch0016, batch0017, batch0018, batch0019, batch0020, batch0021, batch0022, batch0023, batch0024, batch0025, batch0026, batch0027, batch0028, batch0029, batch0030, batch0031, batch0032, batch0033, batch0034, batch0035, batch0036, batch0037, batch0038, batch0039, batch0040, batch0041, batch0042, batch0043, batch0044]
theorem group1_checked : group1.Checked := by
  apply Group.assemble_checked <;> decide +kernel

def group2 := Group.assemble template2 [batch0045] [batch0046]
theorem group2_checked : group2.Checked := by
  apply Group.assemble_checked <;> decide +kernel

def group3 := Group.assemble template3 [batch0047] [batch0048, batch0049, batch0050, batch0051, batch0052, batch0053, batch0054, batch0055, batch0056, batch0057, batch0058, batch0059, batch0060, batch0061, batch0062, batch0063, batch0064, batch0065, batch0066, batch0067, batch0068, batch0069, batch0070, batch0071, batch0072]
theorem group3_checked : group3.Checked := by
  apply Group.assemble_checked <;> decide +kernel

def group4 := Group.assemble template4 [batch0073] [batch0074, batch0075, batch0076, batch0077, batch0078, batch0079, batch0080, batch0081, batch0082, batch0083, batch0084, batch0085, batch0086, batch0087, batch0088, batch0089, batch0090, batch0091, batch0092, batch0093, batch0094]
theorem group4_checked : group4.Checked := by
  apply Group.assemble_checked <;> decide +kernel

def group5 := Group.assemble template5 [batch0095] [batch0096, batch0097, batch0098, batch0099, batch0100, batch0101, batch0102, batch0103]
theorem group5_checked : group5.Checked := by
  apply Group.assemble_checked <;> decide +kernel

def group6 := Group.assemble template6 [batch0104] [batch0105, batch0106, batch0107]
theorem group6_checked : group6.Checked := by
  apply Group.assemble_checked <;> decide +kernel

def group7 := Group.assemble template7 [batch0108] [batch0109, batch0110, batch0111, batch0112, batch0113, batch0114, batch0115]
theorem group7_checked : group7.Checked := by
  apply Group.assemble_checked <;> decide +kernel

def group8 := Group.assemble template8 [batch0116] [batch0117, batch0118]
theorem group8_checked : group8.Checked := by
  apply Group.assemble_checked <;> decide +kernel

def group9 := Group.assemble template9 [batch0119] [batch0120, batch0121, batch0122]
theorem group9_checked : group9.Checked := by
  apply Group.assemble_checked <;> decide +kernel

def group10 := Group.assemble template10 [batch0123] [batch0124, batch0125, batch0126, batch0127, batch0128, batch0129, batch0130, batch0131, batch0132, batch0133, batch0134, batch0135, batch0136]
theorem group10_checked : group10.Checked := by
  apply Group.assemble_checked <;> decide +kernel

def group11 := Group.assemble template11 [batch0137] [batch0138, batch0139, batch0140, batch0141, batch0142]
theorem group11_checked : group11.Checked := by
  apply Group.assemble_checked <;> decide +kernel

def group12 := Group.assemble template12 [batch0143] [batch0144, batch0145, batch0146, batch0147, batch0148, batch0149, batch0150, batch0151, batch0152, batch0153, batch0154, batch0155, batch0156, batch0157, batch0158, batch0159, batch0160, batch0161, batch0162, batch0163, batch0164, batch0165, batch0166, batch0167, batch0168, batch0169, batch0170, batch0171, batch0172, batch0173, batch0174, batch0175, batch0176, batch0177, batch0178, batch0179, batch0180, batch0181, batch0182, batch0183]
theorem group12_checked : group12.Checked := by
  apply Group.assemble_checked <;> decide +kernel

def groups : List Group := [group0, group1, group2, group3, group4, group5, group6, group7, group8, group9, group10, group11, group12]
theorem checked : ∀ g ∈ groups, g.Checked := by
  simp only [groups, List.forall_mem_cons, List.not_mem_nil, false_implies,
    implies_true, and_true]
  exact ⟨group0_checked, group1_checked, group2_checked, group3_checked, group4_checked, group5_checked, group6_checked, group7_checked, group8_checked, group9_checked, group10_checked, group11_checked, group12_checked⟩

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
  [2, 1, 0, 0, 1, 2, 2, 0, 2, 1, 1, 0, 2]]
end TBoards.SpliceData
