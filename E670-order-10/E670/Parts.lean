import E670.Part.P0
import E670.Part.P1
import E670.Part.P2
import E670.Part.P3
import E670.Part.P4
import E670.Part.P5
import E670.Part.P6
import E670.Part.P7
import E670.Part.P8
import E670.Part.P9
import E670.Part.P10
import E670.Part.P11
import E670.Part.P12
import E670.Part.P13
import E670.Part.P14
import E670.Part.P15
import E670.Part.P16
import E670.Part.P17
import E670.Part.P18
import E670.Part.P19
import E670.Part.P20
import E670.Part.P21
import E670.Part.P22
import E670.Part.P23
import E670.Part.P24
import E670.Part.P25
import E670.Part.P26
import E670.Part.P27
import E670.Part.P28
import E670.Part.P29
import E670.Part.P30
import E670.Part.P31
import E670.Part.P32
import E670.Part.P33
import E670.Part.P34
import E670.Part.P35
import E670.Part.P36
import E670.Part.P37
import E670.Part.P38
import E670.Part.P39
import E670.Part.P40
import E670.Part.P41
import E670.Part.P42
import E670.Part.P43
import E670.Part.P44
import E670.Part.P45
import E670.Part.P46
import E670.Part.P47
import E670.Part.P48
import E670.Part.P49
import E670.Part.P50
import E670.Part.P51
import E670.Part.P52
import E670.Part.P53
import E670.Part.P54
import E670.Part.P55
import E670.Part.P56
import E670.Part.P57
import E670.Part.P58
import E670.Part.P59
import E670.Part.P60
import E670.Part.P61
import E670.Part.P62
import E670.Part.P63
import E670.Part.P64
import E670.Part.P65
import E670.Part.P66
import E670.Part.P67
import E670.Part.P68
import E670.Part.P69
import E670.Part.P70
import E670.Part.P71
import E670.Part.P72
import E670.Part.P73
import E670.Part.P74
import E670.Part.P75
import E670.Part.P76
import E670.Part.P77
import E670.Part.P78
import E670.Part.P79
import E670.Part.P80
import E670.Part.P81
import E670.Part.P82
import E670.Part.P83
import E670.Part.P84
import E670.Part.P85
import E670.Part.P86
import E670.Part.P87
import E670.Part.P88
import E670.Part.P89
import E670.Part.P90
import E670.Part.P91
import E670.Part.P92
import E670.Part.P93
import E670.Part.P94
import E670.Part.P95
import E670.Part.P96
import E670.Part.P97
import E670.Part.P98
import E670.Part.P99
import E670.Part.P100
import E670.Part.P101
import E670.Part.P102
import E670.Part.P103
import E670.Part.P104
import E670.Part.P105
import E670.Part.P106
import E670.Part.P107
import E670.Part.P108
import E670.Part.P109

/-- Every list of cubes in `parts` is refuted. -/
theorem E670.parts_refuted : ∀ k < 110, Refutes formula parts[k]!
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
  | 81, _ => part81
  | 82, _ => part82
  | 83, _ => part83
  | 84, _ => part84
  | 85, _ => part85
  | 86, _ => part86
  | 87, _ => part87
  | 88, _ => part88
  | 89, _ => part89
  | 90, _ => part90
  | 91, _ => part91
  | 92, _ => part92
  | 93, _ => part93
  | 94, _ => part94
  | 95, _ => part95
  | 96, _ => part96
  | 97, _ => part97
  | 98, _ => part98
  | 99, _ => part99
  | 100, _ => part100
  | 101, _ => part101
  | 102, _ => part102
  | 103, _ => part103
  | 104, _ => part104
  | 105, _ => part105
  | 106, _ => part106
  | 107, _ => part107
  | 108, _ => part108
  | 109, _ => part109
  | _ + 110, h => absurd h (by omega)
