import Ten.Part.P0
import Ten.Part.P1
import Ten.Part.P2
import Ten.Part.P3
import Ten.Part.P4
import Ten.Part.P5
import Ten.Part.P6
import Ten.Part.P7
import Ten.Part.P8
import Ten.Part.P9
import Ten.Part.P10
import Ten.Part.P11
import Ten.Part.P12
import Ten.Part.P13
import Ten.Part.P14
import Ten.Part.P15
import Ten.Part.P16
import Ten.Part.P17
import Ten.Part.P18
import Ten.Part.P19
import Ten.Part.P20
import Ten.Part.P21
import Ten.Part.P22
import Ten.Part.P23
import Ten.Part.P24
import Ten.Part.P25
import Ten.Part.P26
import Ten.Part.P27
import Ten.Part.P28
import Ten.Part.P29
import Ten.Part.P30
import Ten.Part.P31
import Ten.Part.P32
import Ten.Part.P33
import Ten.Part.P34
import Ten.Part.P35
import Ten.Part.P36
import Ten.Part.P37
import Ten.Part.P38
import Ten.Part.P39
import Ten.Part.P40
import Ten.Part.P41
import Ten.Part.P42
import Ten.Part.P43
import Ten.Part.P44
import Ten.Part.P45
import Ten.Part.P46
import Ten.Part.P47
import Ten.Part.P48
import Ten.Part.P49
import Ten.Part.P50
import Ten.Part.P51
import Ten.Part.P52
import Ten.Part.P53
import Ten.Part.P54
import Ten.Part.P55
import Ten.Part.P56
import Ten.Part.P57
import Ten.Part.P58
import Ten.Part.P59
import Ten.Part.P60
import Ten.Part.P61
import Ten.Part.P62
import Ten.Part.P63
import Ten.Part.P64
import Ten.Part.P65
import Ten.Part.P66
import Ten.Part.P67
import Ten.Part.P68
import Ten.Part.P69
import Ten.Part.P70
import Ten.Part.P71
import Ten.Part.P72
import Ten.Part.P73
import Ten.Part.P74
import Ten.Part.P75
import Ten.Part.P76
import Ten.Part.P77
import Ten.Part.P78
import Ten.Part.P79
import Ten.Part.P80

/-- Every list of cubes in `parts` is refuted. -/
theorem Ten.parts_refuted : ∀ k < 81, Refutes formula parts[k]!
  | 0, _ => part0
  | 1, _ => part1
  | 2, _ => part2
  | 3, _ => part3
  | 4, _ => part4
  | 5, _ => part5
  | 6, _ => part6
  | 7, _ => part7
  | 8, _ => part8
  | 9, _ => part9
  | 10, _ => part10
  | 11, _ => part11
  | 12, _ => part12
  | 13, _ => part13
  | 14, _ => part14
  | 15, _ => part15
  | 16, _ => part16
  | 17, _ => part17
  | 18, _ => part18
  | 19, _ => part19
  | 20, _ => part20
  | 21, _ => part21
  | 22, _ => part22
  | 23, _ => part23
  | 24, _ => part24
  | 25, _ => part25
  | 26, _ => part26
  | 27, _ => part27
  | 28, _ => part28
  | 29, _ => part29
  | 30, _ => part30
  | 31, _ => part31
  | 32, _ => part32
  | 33, _ => part33
  | 34, _ => part34
  | 35, _ => part35
  | 36, _ => part36
  | 37, _ => part37
  | 38, _ => part38
  | 39, _ => part39
  | 40, _ => part40
  | 41, _ => part41
  | 42, _ => part42
  | 43, _ => part43
  | 44, _ => part44
  | 45, _ => part45
  | 46, _ => part46
  | 47, _ => part47
  | 48, _ => part48
  | 49, _ => part49
  | 50, _ => part50
  | 51, _ => part51
  | 52, _ => part52
  | 53, _ => part53
  | 54, _ => part54
  | 55, _ => part55
  | 56, _ => part56
  | 57, _ => part57
  | 58, _ => part58
  | 59, _ => part59
  | 60, _ => part60
  | 61, _ => part61
  | 62, _ => part62
  | 63, _ => part63
  | 64, _ => part64
  | 65, _ => part65
  | 66, _ => part66
  | 67, _ => part67
  | 68, _ => part68
  | 69, _ => part69
  | 70, _ => part70
  | 71, _ => part71
  | 72, _ => part72
  | 73, _ => part73
  | 74, _ => part74
  | 75, _ => part75
  | 76, _ => part76
  | 77, _ => part77
  | 78, _ => part78
  | 79, _ => part79
  | 80, _ => part80
  | _ + 81, h => absurd h (by omega)
