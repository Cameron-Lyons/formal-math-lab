import Splice

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceData
open Splice

-- Decode exactly the specified number of digits, including leading zeros.
private def digits (width n : Nat) : List Nat := match width with
  | 0 => []
  | w+1 => n%3 :: digits w (n/3)

def decodePiece (start : Nat) (rows n : Nat) : Board := match rows with
  | 0 => []
  | r+1 =>
    let width := 2*(start+r)+1
    decodePiece start r (n / 3^width) ++ [(digits width n).reverse]

def template0 : Group where
  k := 5
  pivot := [1, 0, 1, 1, 0, 2, 1, 1, 1, 1, 2]
  caps := []
  tails := []
  upperMask := 19408281523622361743359
  lowerMask := 2398443357705635987668992

def template1 : Group where
  k := 5
  pivot := [2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2]
  caps := []
  tails := []
  upperMask := 1708316233369677140811809
  lowerMask := 709535405859581208600542

def template2 : Group where
  k := 5
  pivot := [0, 0, 1, 2, 2, 2, 2, 1, 2, 0, 2]
  caps := []
  tails := []
  upperMask := 1361812487443419013727803
  lowerMask := 1056039151785839335684548

def template3 : Group where
  k := 5
  pivot := [2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2]
  caps := []
  tails := []
  upperMask := 1708316233369677275029536
  lowerMask := 709535405859581074382815

def template4 : Group where
  k := 5
  pivot := [2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2]
  caps := []
  tails := []
  upperMask := 1708316251384075650293792
  lowerMask := 709535387845182699118559

def template5 : Group where
  k := 5
  pivot := [0, 0, 0, 2, 1, 1, 1, 2, 2, 0, 0]
  caps := []
  tails := []
  upperMask := 309631871253949107044385
  lowerMask := 2108219767975309242367966

def template6 : Group where
  k := 5
  pivot := [1, 0, 2, 0, 2, 2, 1, 1, 0, 1, 0]
  caps := []
  tails := []
  upperMask := 759231097979362226487496
  lowerMask := 1658620541249896122924855

def template7 : Group where
  k := 5
  pivot := [1, 0, 0, 1, 2, 2, 2, 0, 1, 1, 0]
  caps := []
  tails := []
  upperMask := 1514330164671950112445302
  lowerMask := 903521474557308236967049

def template8 : Group where
  k := 5
  pivot := [1, 0, 0, 1, 2, 2, 2, 2, 1, 1, 0]
  caps := []
  tails := []
  upperMask := 7904480254998120255734
  lowerMask := 2409947158974260229156617

def template9 : Group where
  k := 5
  pivot := [1, 2, 1, 2, 0, 1, 2, 1, 2, 0, 0]
  caps := []
  tails := []
  upperMask := 1366023768600736175719450
  lowerMask := 1051827870628522173692901

def template10 : Group where
  k := 5
  pivot := [1, 0, 0, 1, 2, 2, 0, 2, 1, 1, 0]
  caps := []
  tails := []
  upperMask := 2582547267319726619382
  lowerMask := 2415269091961938622792969

def template11 : Group where
  k := 5
  pivot := [1, 0, 0, 1, 2, 2, 0, 2, 1, 1, 0]
  caps := []
  tails := []
  upperMask := 7314137157410464217334
  lowerMask := 2410537502071847885195017

def template12 : Group where
  k := 5
  pivot := [2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2]
  caps := []
  tails := []
  upperMask := 1211287198200041870680683
  lowerMask := 1206564441029216478731668

end TBoards.SpliceData
