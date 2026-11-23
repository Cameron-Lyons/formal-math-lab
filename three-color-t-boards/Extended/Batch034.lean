import Extended.Batch030

/- Generated from extended_seeds.json. Published seeds 0–4:
   Qiyuan Ma, DOI 10.5281/zenodo.23631079, CC-BY-4.0. -/

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.Extended

def seed1088 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,0,1,2,1,1,0,0,0],
  [1,0,1,1,1,0,1,1,1,2,2,0,2,1,0],
  [0,0,0,1,0,0,2,0,2,1,0,2,1,2,0,0,2],
  [0,2,2,0,1,1,0,2,0,0,1,2,0,2,0,1,0,0,2]
]

def cert1088n : CertifiedBoard :=
  ⟨seed1088, by apply FastValid.valid; decide +kernel⟩

def cert1088r : CertifiedBoard :=
  ⟨seed1088.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1089 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,0,1,2,1,1,0,2,1],
  [1,1,0,0,1,0,1,1,1,1,0,0,2,0,0],
  [0,0,2,1,0,0,0,1,2,2,0,2,2,0,1,0,2],
  [2,1,2,0,2,0,2,0,1,1,2,0,0,0,2,1,0,1,1]
]

def cert1089n : CertifiedBoard :=
  ⟨seed1089, by apply FastValid.valid; decide +kernel⟩

def cert1089r : CertifiedBoard :=
  ⟨seed1089.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1090 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,0,1,2,1,1,1,0,1],
  [1,0,2,0,1,0,2,0,0,0,2,0,2,1,0],
  [0,1,2,0,2,2,0,2,1,0,1,0,0,1,1,1,0],
  [1,0,0,0,1,1,2,0,0,2,1,2,2,0,1,1,0,0,2]
]

def cert1090n : CertifiedBoard :=
  ⟨seed1090, by apply FastValid.valid; decide +kernel⟩

def cert1090r : CertifiedBoard :=
  ⟨seed1090.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1091 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,0,1,2,1,1,1,0,2],
  [0,1,0,0,1,0,1,1,1,2,2,0,2,0,1],
  [0,0,2,1,0,1,2,0,0,2,0,2,0,1,1,0,0],
  [2,2,0,2,1,0,0,0,2,1,2,0,0,0,1,1,0,2,2]
]

def cert1091n : CertifiedBoard :=
  ⟨seed1091, by apply FastValid.valid; decide +kernel⟩

def cert1091r : CertifiedBoard :=
  ⟨seed1091.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1092 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,0,1,2,1,1,1,2,0],
  [2,0,2,0,1,0,2,1,0,1,1,0,0,2,0],
  [1,1,0,0,0,2,1,0,0,0,1,2,2,0,0,1,1],
  [2,0,2,0,1,0,1,1,1,0,2,2,0,2,1,2,0,0,2]
]

def cert1092n : CertifiedBoard :=
  ⟨seed1092, by apply FastValid.valid; decide +kernel⟩

def cert1092r : CertifiedBoard :=
  ⟨seed1092.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1093 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,0,1,2,1,1,2,0,1],
  [0,1,0,2,0,0,2,1,0,1,1,1,1,0,0],
  [2,0,1,0,2,1,0,1,1,0,0,0,2,0,2,2,0],
  [0,0,0,1,2,0,2,1,2,2,0,2,0,0,1,1,0,0,2]
]

def cert1093n : CertifiedBoard :=
  ⟨seed1093, by apply FastValid.valid; decide +kernel⟩

def cert1093r : CertifiedBoard :=
  ⟨seed1093.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1094 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,0,1,2,1,1,2,0,2],
  [0,1,0,1,1,1,1,0,0,1,1,0,0,2,0],
  [2,0,2,0,0,0,2,1,0,2,2,0,0,1,1,0,1],
  [0,2,1,0,2,1,2,0,1,0,0,0,2,0,1,2,2,0,2]
]

def cert1094n : CertifiedBoard :=
  ⟨seed1094, by apply FastValid.valid; decide +kernel⟩

def cert1094r : CertifiedBoard :=
  ⟨seed1094.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1095 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,0,1,2,1,1,2,0,2],
  [0,1,0,1,1,1,1,0,0,1,1,0,2,0,1],
  [0,0,1,0,0,0,2,0,2,1,2,2,0,0,0,2,1],
  [2,1,0,1,2,0,1,1,0,2,1,0,0,2,2,0,2,0,0]
]

def cert1095n : CertifiedBoard :=
  ⟨seed1095, by apply FastValid.valid; decide +kernel⟩

def cert1095r : CertifiedBoard :=
  ⟨seed1095.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1096 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,0,1,2,1,1,2,0,2],
  [1,0,1,1,1,0,1,0,0,1,1,1,0,0,0],
  [0,2,1,2,2,0,0,1,2,0,0,0,2,0,2,1,0],
  [0,0,2,1,0,0,2,2,0,2,0,1,1,0,2,0,1,0,2]
]

def cert1096n : CertifiedBoard :=
  ⟨seed1096, by apply FastValid.valid; decide +kernel⟩

def cert1096r : CertifiedBoard :=
  ⟨seed1096.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1097 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,0,1,2,1,1,2,0,2],
  [2,0,0,0,1,1,0,1,0,2,1,0,1,1,1],
  [1,0,0,2,0,1,2,2,0,0,1,1,0,0,0,2,0],
  [1,1,1,0,2,1,0,0,2,0,2,2,0,2,1,2,0,1,0]
]

def cert1097n : CertifiedBoard :=
  ⟨seed1097, by apply FastValid.valid; decide +kernel⟩

def cert1097r : CertifiedBoard :=
  ⟨seed1097.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1098 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,0,2,0,0,0,1,1,1],
  [1,0,2,1,1,0,1,0,2,1,0,0,2,1,0],
  [1,2,1,2,0,1,0,1,1,0,0,0,2,0,2,0,2],
  [1,1,1,0,0,2,2,0,1,2,2,0,0,1,2,0,1,1,2]
]

def cert1098n : CertifiedBoard :=
  ⟨seed1098, by apply FastValid.valid; decide +kernel⟩

def cert1098r : CertifiedBoard :=
  ⟨seed1098.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1099 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,0,2,0,1,1,0,0,2],
  [2,0,0,0,1,2,0,2,1,0,0,0,2,1,1],
  [1,0,1,0,0,1,1,1,0,2,1,2,0,1,2,1,0],
  [1,1,0,1,0,2,2,0,0,2,0,2,0,1,1,1,2,2,0]
]

def cert1099n : CertifiedBoard :=
  ⟨seed1099, by apply FastValid.valid; decide +kernel⟩

def cert1099r : CertifiedBoard :=
  ⟨seed1099.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1100 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,0,2,0,1,1,1,0,0],
  [2,1,2,0,1,1,2,0,2,0,0,2,1,0,2],
  [0,0,1,0,1,1,1,0,2,1,1,0,0,0,0,2,1],
  [2,0,1,0,0,1,2,1,0,1,2,2,0,2,2,0,0,2,0]
]

def cert1100n : CertifiedBoard :=
  ⟨seed1100, by apply FastValid.valid; decide +kernel⟩

def cert1100r : CertifiedBoard :=
  ⟨seed1100.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1101 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,0,2,1,0,1,1,1,2],
  [1,2,0,1,2,1,1,0,0,0,1,1,1,0,2],
  [1,0,0,2,0,0,1,2,2,0,0,2,0,1,0,0,0],
  [0,0,2,1,2,0,2,2,0,2,0,1,1,0,2,1,0,1,0]
]

def cert1101n : CertifiedBoard :=
  ⟨seed1101, by apply FastValid.valid; decide +kernel⟩

def cert1101r : CertifiedBoard :=
  ⟨seed1101.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1102 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,0,2,1,0,1,2,0,1],
  [0,0,1,1,1,1,0,0,0,2,2,0,2,0,0],
  [1,1,0,2,0,1,2,1,0,1,0,0,1,1,2,0,2],
  [0,1,0,0,2,0,0,0,2,1,2,2,0,1,1,0,2,1,1]
]

def cert1102n : CertifiedBoard :=
  ⟨seed1102, by apply FastValid.valid; decide +kernel⟩

def cert1102r : CertifiedBoard :=
  ⟨seed1102.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1103 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,1,0,0,0,0,1,2,0],
  [0,1,1,0,1,1,1,1,0,2,1,0,0,2,2],
  [2,2,0,1,0,1,2,2,0,0,1,1,0,0,2,0,1],
  [2,0,2,1,2,0,2,1,1,2,0,0,2,0,1,0,2,0,2]
]

def cert1103n : CertifiedBoard :=
  ⟨seed1103, by apply FastValid.valid; decide +kernel⟩

def cert1103r : CertifiedBoard :=
  ⟨seed1103.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1104 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,1,0,0,0,0,2,0,1],
  [0,2,1,1,1,0,1,1,0,0,1,1,2,0,2],
  [2,1,2,0,1,2,0,0,2,1,0,1,0,0,1,0,2],
  [0,1,1,1,0,2,0,2,0,1,2,2,0,0,2,2,0,2,1]
]

def cert1104n : CertifiedBoard :=
  ⟨seed1104, by apply FastValid.valid; decide +kernel⟩

def cert1104r : CertifiedBoard :=
  ⟨seed1104.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1105 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,1,0,0,0,0,2,1,1],
  [0,0,1,1,1,1,2,0,0,2,1,0,1,0,0],
  [1,1,0,0,2,0,1,2,0,2,0,2,1,2,2,0,1],
  [0,1,1,0,1,0,2,2,0,1,1,0,2,0,0,1,2,0,2]
]

def cert1105n : CertifiedBoard :=
  ⟨seed1105, by apply FastValid.valid; decide +kernel⟩

def cert1105r : CertifiedBoard :=
  ⟨seed1105.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1106 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,1,0,0,0,0,2,1,1],
  [1,1,0,1,2,0,2,1,0,2,0,0,1,0,0],
  [0,1,1,0,1,2,0,2,0,1,0,2,1,2,2,0,1],
  [0,0,2,0,2,2,0,1,1,2,0,0,1,1,1,1,0,0,2]
]

def cert1106n : CertifiedBoard :=
  ⟨seed1106, by apply FastValid.valid; decide +kernel⟩

def cert1106r : CertifiedBoard :=
  ⟨seed1106.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1107 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,1,0,0,0,1,2,0,1],
  [0,1,1,0,1,1,1,0,2,1,0,0,2,0,2],
  [2,2,0,1,0,1,2,2,0,1,1,1,0,0,0,2,0],
  [2,0,2,1,2,0,2,1,1,2,0,0,2,0,0,1,0,2,2]
]

def cert1107n : CertifiedBoard :=
  ⟨seed1107, by apply FastValid.valid; decide +kernel⟩

def cert1107r : CertifiedBoard :=
  ⟨seed1107.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1108 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,1,0,0,0,1,2,0,1],
  [1,1,0,1,1,1,0,0,2,2,0,0,0,1,2],
  [1,2,2,0,0,2,0,1,0,0,2,1,0,1,1,0,2],
  [0,1,1,1,2,0,2,0,1,0,2,0,2,1,2,0,2,1,1]
]

def cert1108n : CertifiedBoard :=
  ⟨seed1108, by apply FastValid.valid; decide +kernel⟩

def cert1108r : CertifiedBoard :=
  ⟨seed1108.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1109 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,1,0,0,0,2,0,1,1],
  [0,2,1,1,1,1,2,2,0,0,1,2,0,0,2],
  [1,1,0,2,0,1,0,0,0,1,0,1,1,0,2,0,2],
  [2,0,2,1,0,1,1,0,0,2,2,0,1,2,0,2,1,2,0]
]

def cert1109n : CertifiedBoard :=
  ⟨seed1109, by apply FastValid.valid; decide +kernel⟩

def cert1109r : CertifiedBoard :=
  ⟨seed1109.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1110 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,1,0,0,0,2,1,1,0],
  [0,1,1,2,0,2,0,0,1,0,0,0,2,1,0],
  [1,0,1,1,1,1,0,2,1,2,2,0,2,0,1,0,2],
  [1,0,0,2,0,1,2,0,1,1,0,1,2,0,2,2,0,0,1]
]

def cert1110n : CertifiedBoard :=
  ⟨seed1110, by apply FastValid.valid; decide +kernel⟩

def cert1110r : CertifiedBoard :=
  ⟨seed1110.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1111 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,1,0,0,0,2,1,1,0],
  [1,0,0,0,1,1,1,0,2,1,0,2,0,1,1],
  [1,2,0,0,2,2,0,2,1,2,0,0,1,1,0,0,2],
  [1,1,1,2,0,2,0,2,0,1,0,1,0,1,2,2,0,1,2]
]

def cert1111n : CertifiedBoard :=
  ⟨seed1111, by apply FastValid.valid; decide +kernel⟩

def cert1111r : CertifiedBoard :=
  ⟨seed1111.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1112 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,1,0,0,0,2,1,1,0],
  [1,0,1,1,1,1,2,0,1,1,0,1,1,0,0],
  [0,0,2,0,2,0,1,0,2,2,0,0,1,2,2,0,2],
  [0,1,0,2,0,0,0,2,1,2,0,2,1,0,0,1,2,0,1]
]

def cert1112n : CertifiedBoard :=
  ⟨seed1112, by apply FastValid.valid; decide +kernel⟩

def cert1112r : CertifiedBoard :=
  ⟨seed1112.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1113 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,1,0,0,0,2,1,1,0],
  [1,1,0,1,1,1,2,2,0,2,0,1,0,0,1],
  [0,1,1,0,0,2,0,1,2,0,0,0,2,1,2,0,2],
  [1,0,1,2,0,1,0,2,2,0,2,1,0,2,0,0,1,1,1]
]

def cert1113n : CertifiedBoard :=
  ⟨seed1113, by apply FastValid.valid; decide +kernel⟩

def cert1113r : CertifiedBoard :=
  ⟨seed1113.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1114 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,1,0,0,0,2,1,1,0],
  [2,0,0,0,1,1,2,2,0,1,1,1,1,0,2],
  [0,1,1,0,0,1,2,0,2,0,2,0,0,2,1,0,1],
  [1,0,1,0,0,2,0,1,2,0,1,0,2,1,2,0,2,2,0]
]

def cert1114n : CertifiedBoard :=
  ⟨seed1114, by apply FastValid.valid; decide +kernel⟩

def cert1114r : CertifiedBoard :=
  ⟨seed1114.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1115 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,1,0,0,0,2,1,1,0],
  [2,0,0,1,1,1,2,2,0,1,0,1,0,0,1],
  [0,1,2,0,2,0,1,2,0,1,1,0,0,2,1,2,0],
  [1,0,1,1,1,0,2,2,0,2,0,2,1,0,2,0,0,0,2]
]

def cert1115n : CertifiedBoard :=
  ⟨seed1115, by apply FastValid.valid; decide +kernel⟩

def cert1115r : CertifiedBoard :=
  ⟨seed1115.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1116 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,1,0,0,0,2,1,1,1],
  [1,0,0,0,1,0,1,2,0,0,1,1,0,0,2],
  [1,1,1,0,2,0,0,2,0,2,2,0,2,1,0,1,2],
  [1,2,2,0,1,0,2,1,2,0,2,0,1,1,2,0,1,1,0]
]

def cert1116n : CertifiedBoard :=
  ⟨seed1116, by apply FastValid.valid; decide +kernel⟩

def cert1116r : CertifiedBoard :=
  ⟨seed1116.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1117 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,1,0,0,0,2,1,1,1],
  [2,1,2,0,1,1,2,0,0,2,0,2,0,0,2],
  [1,1,0,0,1,1,1,0,1,0,0,0,1,2,0,2,0],
  [2,0,2,1,0,1,2,2,0,1,0,2,2,0,1,1,0,2,1]
]

def cert1117n : CertifiedBoard :=
  ⟨seed1117, by apply FastValid.valid; decide +kernel⟩

def cert1117r : CertifiedBoard :=
  ⟨seed1117.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1118 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,1,0,0,2,1,1,1,0],
  [0,1,1,2,0,0,0,0,1,0,1,1,0,0,2],
  [1,0,2,0,1,2,0,2,1,2,2,0,2,1,0,0,1],
  [1,2,0,0,2,2,0,2,0,1,0,2,0,1,1,1,0,1,2]
]

def cert1118n : CertifiedBoard :=
  ⟨seed1118, by apply FastValid.valid; decide +kernel⟩

def cert1118r : CertifiedBoard :=
  ⟨seed1118.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1119 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,1,0,0,2,1,1,1,0],
  [0,1,1,2,0,1,2,0,2,0,1,1,1,0,2],
  [1,2,0,0,0,0,1,0,1,0,2,2,0,2,0,0,1],
  [1,0,0,2,1,0,0,2,1,2,2,0,2,0,1,1,0,1,2]
]

def cert1119n : CertifiedBoard :=
  ⟨seed1119, by apply FastValid.valid; decide +kernel⟩

def cert1119r : CertifiedBoard :=
  ⟨seed1119.map List.reverse, by apply FastValid.valid; decide +kernel⟩

end TBoards.Extended
