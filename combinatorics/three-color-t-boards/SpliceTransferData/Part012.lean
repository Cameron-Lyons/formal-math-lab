import SpliceTransferData.Part010

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceTransferData
open Splice

private def template96 : Group where
  k := 5
  pivot := [1, 2, 2, 2, 1, 0, 2, 2, 2, 1, 2]
  caps := ([606846130038, 607137359706] : List Nat).map Packed.cap
  tails := []
  upperMask := 302042133567651355
  lowerMask := 2417851337187124781760996
private def selection96 : List Nat := [4063, 366, 7]

def group96 := Transfer.assemble SpliceExtensionData.group11 template96 selection96
theorem group96_checked : group96.Checked := by
  apply Transfer.assemble_checked _ _ _ SpliceExtensionData.group11_checked <;> decide +kernel
theorem group96_size : group96.size = 6 := by decide +kernel

private def template97 : Group where
  k := 5
  pivot := [1, 2, 2, 2, 0, 2, 2, 2, 0, 1, 2]
  caps := ([663824081712] : List Nat).map Packed.cap
  tails := []
  upperMask := 9234720821628384827
  lowerMask := 2417842404508436721027524
private def selection97 : List Nat := [2050, 116, 27, 0, 2997, 2604]

def group97 := Transfer.assemble SpliceExtensionData.group10 template97 selection97
theorem group97_checked : group97.Checked := by
  apply Transfer.assemble_checked _ _ _ SpliceExtensionData.group10_checked <;> decide +kernel
theorem group97_size : group97.size = 6 := by decide +kernel

private def template98 : Group where
  k := 5
  pivot := [1, 2, 1, 2, 2, 1, 1, 2, 2, 1, 2]
  caps := ([13968476922, 42292629090, 137678294386] : List Nat).map Packed.cap
  tails := []
  upperMask := 5651149839611419
  lowerMask := 2417851633578108509800932
private def selection98 : List Nat := [2986, 0]

def group98 := Transfer.assemble SpliceExtensionData.group12 template98 selection98
theorem group98_checked : group98.Checked := by
  apply Transfer.assemble_checked _ _ _ SpliceExtensionData.group12_checked <;> decide +kernel
theorem group98_size : group98.size = 6 := by decide +kernel

private def template99 : Group where
  k := 5
  pivot := [0, 0, 2, 2, 0, 0, 0, 0, 2, 2, 2]
  caps := ([97780457352] : List Nat).map Packed.cap
  tails := []
  upperMask := 4686032490681611803
  lowerMask := 2417846953196767667800548
private def selection99 : List Nat := [656, 0, 0, 0, 0, 0]

def group99 := Transfer.assemble SpliceExtensionData.group6 template99 selection99
theorem group99_checked : group99.Checked := by
  apply Transfer.assemble_checked _ _ _ SpliceExtensionData.group6_checked <;> decide +kernel
theorem group99_size : group99.size = 6 := by decide +kernel

private def template100 : Group where
  k := 5
  pivot := [0, 0, 1, 1, 1, 0, 2, 1, 1, 1, 1]
  caps := ([11656458835] : List Nat).map Packed.cap
  tails := []
  upperMask := 239808238041033945854
  lowerMask := 2417611830991217315466497
private def selection100 : List Nat := [918, 0, 1269, 8, 0, 5]

def group100 := Transfer.assemble SpliceExtensionData.group3 template100 selection100
theorem group100_checked : group100.Checked := by
  apply Transfer.assemble_checked _ _ _ SpliceExtensionData.group3_checked <;> decide +kernel
theorem group100_size : group100.size = 6 := by decide +kernel

private def template101 : Group where
  k := 5
  pivot := [2, 0, 0, 2, 2, 0, 0, 2, 2, 2, 0]
  caps := ([599786526819] : List Nat).map Packed.cap
  tails := []
  upperMask := 155411265479784215
  lowerMask := 2417851483817992869628136
private def selection101 : List Nat := [703, 0, 2208, 1067, 5455]

def group101 := Transfer.assemble SpliceExtensionData.group8 template101 selection101
theorem group101_checked : group101.Checked := by
  apply Transfer.assemble_checked _ _ _ SpliceExtensionData.group8_checked <;> decide +kernel
theorem group101_size : group101.size = 5 := by decide +kernel

private def template102 : Group where
  k := 5
  pivot := [1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1]
  caps := ([14570579943] : List Nat).map Packed.cap
  tails := []
  upperMask := 149203386946975259
  lowerMask := 2417851490025871402437092
private def selection102 : List Nat := [104, 903, 1190, 534, 0]

def group102 := Transfer.assemble SpliceExtensionData.group13 template102 selection102
theorem group102_checked : group102.Checked := by
  apply Transfer.assemble_checked _ _ _ SpliceExtensionData.group13_checked <;> decide +kernel
theorem group102_size : group102.size = 5 := by decide +kernel

private def template103 : Group where
  k := 5
  pivot := [1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1]
  caps := ([32000217615] : List Nat).map Packed.cap
  tails := []
  upperMask := 41116996695389723
  lowerMask := 2417851598112261654022628
private def selection103 : List Nat := [88, 164, 0, 2164, 103]

def group103 := Transfer.assemble SpliceExtensionData.group13 template103 selection103
theorem group103_checked : group103.Checked := by
  apply Transfer.assemble_checked _ _ _ SpliceExtensionData.group13_checked <;> decide +kernel
theorem group103_size : group103.size = 5 := by decide +kernel

end TBoards.SpliceTransferData
