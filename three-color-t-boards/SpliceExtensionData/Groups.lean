import SplicePacked

-- Generated from splice_extension.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceExtensionData
open Splice

def template0 : Group where
  k := 5
  pivot := [2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2]
  caps := []
  tails := []
  upperMask := 152296505426916862812779
  lowerMask := 2265555133802341486599572

private def cap0_0Codes : List Nat := [
  283669410256, 290614281244, 294086716738,
  301031587726]

def cap0_0 : Group.Batch template0.capOK :=
  Packed.capBatch template0 167579 rfl (by decide) cap0_0Codes
    (by decide +kernel)

def template1 : Group where
  k := 5
  pivot := [2, 2, 0, 1, 1, 2, 1, 2, 2, 2, 2]
  caps := []
  tails := []
  upperMask := 1211287197707460644651643
  lowerMask := 1206564441521797704760708

private def cap1_0Codes : List Nat := [
  283669410256, 290614281244, 294086716738,
  301031587726]

def cap1_0 : Group.Batch template1.capOK :=
  Packed.capBatch template1 161027 rfl (by decide) cap1_0Codes
    (by decide +kernel)

def template2 : Group where
  k := 5
  pivot := [2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2]
  caps := []
  tails := []
  upperMask := 1211287197076340991279723
  lowerMask := 1206564442152917358132628

private def cap2_0Codes : List Nat := [
  283669410256, 290614281244, 294086716738,
  301031587726]

def cap2_0 : Group.Batch template2.capOK :=
  Packed.capBatch template2 168074 rfl (by decide) cap2_0Codes
    (by decide +kernel)

def template3 : Group where
  k := 5
  pivot := [1, 0, 0, 1, 0, 1, 2, 1, 1, 1, 0]
  caps := []
  tails := []
  upperMask := 239808519245425621726
  lowerMask := 2417611830710012923790625

private def cap3_0Codes : List Nat := [
  94430933932, 94430953614, 193194458626,
  193194478308, 193208800972, 193208820654]

def cap3_0 : Group.Batch template3.capOK :=
  Packed.capBatch template3 61680 rfl (by decide) cap3_0Codes
    (by decide +kernel)

def template4 : Group where
  k := 5
  pivot := [2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2]
  caps := []
  tails := []
  upperMask := 1211287179059743462613839
  lowerMask := 1206564460169514886798512

private def cap4_0Codes : List Nat := [
  283669410229, 290614281217, 294086716711,
  301031587699]

def cap4_0 : Group.Batch template4.capOK :=
  Packed.capBatch template4 167588 rfl (by decide) cap4_0Codes
    (by decide +kernel)

def template5 : Group where
  k := 5
  pivot := [2, 2, 1, 0, 2, 1, 1, 0, 0, 2, 2]
  caps := []
  tails := []
  upperMask := 9462344670482013135
  lowerMask := 2417842176884587867399216

private def cap5_0Codes : List Nat := [
  283669410229, 290614281217, 294086716711,
  301031587699]

def cap5_0 : Group.Batch template5.capOK :=
  Packed.capBatch template5 165815 rfl (by decide) cap5_0Codes
    (by decide +kernel)

def template6 : Group where
  k := 5
  pivot := [2, 2, 0, 0, 2, 2, 0, 0, 2, 2, 2]
  caps := []
  tails := []
  upperMask := 2288878216296223
  lowerMask := 2417851636940380133116128

private def cap6_0Codes : List Nat := [
  4067140656, 5094120144, 13968121962,
  13968122682, 15286923288, 94207209906,
  94207210626, 98979351096, 125927864634,
  137663972442, 286108231212, 287127022572]

def cap6_0 : Group.Batch template6.capOK :=
  Packed.capBatch template6 159434 rfl (by decide) cap6_0Codes
    (by decide +kernel)

def template7 : Group where
  k := 5
  pivot := [2, 2, 2, 0, 1, 2, 2, 0, 1, 2, 2]
  caps := []
  tails := []
  upperMask := 2341624173180475
  lowerMask := 2417851636887634176231876

private def cap7_0Codes : List Nat := [
  4067140656, 5094120144, 13968121962,
  13968122682, 15286923288, 42249759490,
  94207209906, 94207210626, 98979351096,
  137678294386, 286108231212, 287127022572]

def cap7_0 : Group.Batch template7.capOK :=
  Packed.capBatch template7 171980 rfl (by decide) cap7_0Codes
    (by decide +kernel)

def template8 : Group where
  k := 5
  pivot := [2, 2, 0, 0, 2, 2, 0, 0, 2, 2, 2]
  caps := []
  tails := []
  upperMask := 11296077403928351
  lowerMask := 2417851627933180945484000

private def cap8_0Codes : List Nat := [
  136517282149, 137536073509, 285980332279,
  297716440087, 324664953625, 329437094095,
  329437094815, 408357381433, 409676182039,
  409676182759, 418550184577, 419577164065]

def cap8_0 : Group.Batch template8.capOK :=
  Packed.capBatch template8 159434 rfl (by decide) cap8_0Codes
    (by decide +kernel)

def template9 : Group where
  k := 5
  pivot := [2, 2, 2, 0, 1, 2, 2, 0, 1, 2, 2]
  caps := []
  tails := []
  upperMask := 11348823360812603
  lowerMask := 2417851627880434988599748

private def cap9_0Codes : List Nat := [
  136517282149, 137536073509, 285966010335,
  324664953625, 329437094095, 329437094815,
  381394545231, 408357381433, 409676182039,
  409676182759, 418550184577, 419577164065]

def cap9_0 : Group.Batch template9.capOK :=
  Packed.capBatch template9 171980 rfl (by decide) cap9_0Codes
    (by decide +kernel)

def template10 : Group where
  k := 5
  pivot := [2, 2, 2, 2, 0, 1, 2, 2, 0, 2, 2]
  caps := []
  tails := []
  upperMask := 11348853493085755
  lowerMask := 2417851627880404856326596

private def cap10_0Codes : List Nat := [
  329437094095, 329437094815, 409676182039,
  409676182759, 418550184577, 418559746141,
  419577164065, 420007037131]

def cap10_0 : Group.Batch template10.capOK :=
  Packed.capBatch template10 175427 rfl (by decide) cap10_0Codes
    (by decide +kernel)

def template11 : Group where
  k := 5
  pivot := [2, 2, 2, 2, 1, 0, 2, 2, 1, 2, 2]
  caps := []
  tails := []
  upperMask := 13811759563423259
  lowerMask := 2417851625417498785989092

private def cap11_0Codes : List Nat := [
  329437094095, 329437094815, 409676182039,
  409676182759, 418550184577, 418559746141,
  419577164065, 420007037131]

def cap11_0 : Group.Batch template11.capOK :=
  Packed.capBatch template11 175922 rfl (by decide) cap11_0Codes
    (by decide +kernel)

def template12 : Group where
  k := 5
  pivot := [2, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1]
  caps := []
  tails := []
  upperMask := 5651149839611419
  lowerMask := 2417851633578108509800932

private def cap12_0Codes : List Nat := [
  4067140656, 5094120144, 11801739528,
  13968121962, 13968122682, 14513190876,
  31957170894, 94207209906, 94207210626,
  98979351096, 136128855744]

def cap12_0 : Group.Batch template12.capOK :=
  Packed.capBatch template12 156481 rfl (by decide) cap12_0Codes
    (by decide +kernel)

end TBoards.SpliceExtensionData
