import Extended.Batch031

/- Generated from extended_seeds.json. Published seeds 0–4:
   Qiyuan Ma, DOI 10.5281/zenodo.23631079, CC-BY-4.0. -/

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.Extended

def seed1120 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,1,0,0,2,1,1,1,2],
  [1,0,1,2,0,0,1,0,0,2,0,1,1,1,0],
  [1,2,0,0,0,0,1,1,0,2,0,2,2,0,2,1,0],
  [1,0,0,2,1,2,0,1,2,2,0,1,0,1,1,0,2,0,2]
]

def cert1120n : CertifiedBoard :=
  ⟨seed1120, by apply FastValid.valid; decide +kernel⟩

def cert1120r : CertifiedBoard :=
  ⟨seed1120.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1121 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,1,0,0,2,1,1,1,2],
  [1,2,0,2,0,0,2,1,0,1,2,0,1,2,0],
  [1,1,0,1,1,0,2,0,1,0,0,0,1,0,0,0,2],
  [2,0,2,0,1,1,1,0,2,2,0,2,1,2,2,0,0,1,1]
]

def cert1121n : CertifiedBoard :=
  ⟨seed1121, by apply FastValid.valid; decide +kernel⟩

def cert1121r : CertifiedBoard :=
  ⟨seed1121.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1122 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,1,0,0,2,1,1,1,2],
  [2,1,2,0,1,0,2,0,0,1,2,2,0,0,2],
  [0,1,1,1,0,0,0,2,0,1,0,0,0,1,1,0,1],
  [1,2,0,1,1,0,2,2,0,2,0,2,1,0,1,2,0,2,1]
]

def cert1122n : CertifiedBoard :=
  ⟨seed1122, by apply FastValid.valid; decide +kernel⟩

def cert1122r : CertifiedBoard :=
  ⟨seed1122.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1123 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,1,0,0,2,1,1,1,2],
  [2,1,2,0,1,0,2,0,0,1,2,2,0,0,2],
  [0,1,1,1,0,0,0,2,0,1,0,0,0,1,1,0,1],
  [1,2,0,1,2,0,2,2,0,2,0,2,1,0,1,1,0,2,1]
]

def cert1123n : CertifiedBoard :=
  ⟨seed1123, by apply FastValid.valid; decide +kernel⟩

def cert1123r : CertifiedBoard :=
  ⟨seed1123.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1124 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,1,0,1,0,0,0,1,2],
  [2,0,1,1,1,1,2,0,2,1,0,1,0,0,2],
  [1,1,0,0,0,2,0,2,1,2,0,0,1,1,0,2,0],
  [1,2,2,0,0,2,0,2,1,1,0,2,2,0,1,2,0,1,1]
]

def cert1124n : CertifiedBoard :=
  ⟨seed1124, by apply FastValid.valid; decide +kernel⟩

def cert1124r : CertifiedBoard :=
  ⟨seed1124.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1125 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,1,0,1,0,0,1,1,0],
  [0,0,2,1,1,1,1,0,2,1,0,1,2,2,0],
  [1,0,0,1,2,0,0,0,2,0,2,0,1,1,2,0,2],
  [2,0,1,1,0,0,2,1,2,0,1,0,2,2,0,2,0,0,0]
]

def cert1125n : CertifiedBoard :=
  ⟨seed1125, by apply FastValid.valid; decide +kernel⟩

def cert1125r : CertifiedBoard :=
  ⟨seed1125.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1126 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,1,0,1,0,0,1,1,2],
  [0,0,2,0,1,2,0,1,1,0,1,0,0,0,2],
  [1,2,0,0,0,1,1,0,0,2,1,2,2,0,2,1,1],
  [1,1,1,1,0,2,2,0,2,0,1,2,0,2,1,0,2,0,0]
]

def cert1126n : CertifiedBoard :=
  ⟨seed1126, by apply FastValid.valid; decide +kernel⟩

def cert1126r : CertifiedBoard :=
  ⟨seed1126.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1127 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,1,0,1,0,0,2,0,1],
  [0,0,1,1,1,0,2,1,2,2,0,2,1,0,0],
  [0,1,0,0,2,0,2,1,1,1,2,0,0,1,1,0,2],
  [0,2,2,0,1,1,0,1,2,0,0,0,0,2,0,1,2,0,2]
]

def cert1127n : CertifiedBoard :=
  ⟨seed1127, by apply FastValid.valid; decide +kernel⟩

def cert1127r : CertifiedBoard :=
  ⟨seed1127.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1128 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,1,0,1,0,0,2,1,1],
  [2,0,1,2,0,1,1,0,0,0,1,1,0,0,2],
  [1,1,2,0,0,0,2,0,2,1,0,1,2,2,0,0,1],
  [0,1,1,1,1,0,2,0,1,0,2,1,2,0,2,0,2,2,0]
]

def cert1128n : CertifiedBoard :=
  ⟨seed1128, by apply FastValid.valid; decide +kernel⟩

def cert1128r : CertifiedBoard :=
  ⟨seed1128.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1129 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,1,0,1,0,2,1,1,1],
  [2,0,1,2,0,1,1,0,2,0,0,1,2,2,0],
  [1,1,0,0,0,0,1,1,1,0,0,2,0,0,2,0,2],
  [1,2,0,2,1,0,1,0,0,2,1,2,0,2,2,0,1,1,2]
]

def cert1129n : CertifiedBoard :=
  ⟨seed1129, by apply FastValid.valid; decide +kernel⟩

def cert1129r : CertifiedBoard :=
  ⟨seed1129.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1130 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,1,0,1,0,2,1,1,2],
  [0,2,0,1,2,0,2,0,2,1,2,0,0,0,2],
  [0,1,1,1,0,0,0,2,0,1,1,1,0,1,0,0,1],
  [1,2,0,1,1,0,2,1,0,0,1,2,2,0,0,2,2,0,2]
]

def cert1130n : CertifiedBoard :=
  ⟨seed1130, by apply FastValid.valid; decide +kernel⟩

def cert1130r : CertifiedBoard :=
  ⟨seed1130.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1131 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,1,0,1,1,0,0,0,1],
  [0,0,2,1,1,1,2,2,0,2,1,2,0,0,0],
  [0,1,0,1,2,0,0,2,0,1,1,1,0,2,1,0,2],
  [1,1,0,0,1,2,0,2,0,2,2,0,1,0,0,2,0,1,1]
]

def cert1131n : CertifiedBoard :=
  ⟨seed1131, by apply FastValid.valid; decide +kernel⟩

def cert1131r : CertifiedBoard :=
  ⟨seed1131.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1132 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,1,0,1,1,0,0,0,2],
  [0,0,1,1,1,1,2,2,0,0,2,0,0,2,0],
  [1,1,0,2,0,1,2,0,1,2,0,2,1,0,0,1,1],
  [2,0,2,1,2,0,1,0,2,2,0,2,1,1,0,1,0,0,0]
]

def cert1132n : CertifiedBoard :=
  ⟨seed1132, by apply FastValid.valid; decide +kernel⟩

def cert1132r : CertifiedBoard :=
  ⟨seed1132.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1133 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,1,0,1,1,0,0,0,2],
  [0,0,2,1,1,0,2,1,2,0,2,1,0,1,1],
  [2,0,0,1,2,2,0,2,0,0,1,1,1,1,0,0,0],
  [1,1,2,0,1,2,0,2,0,1,0,0,2,0,1,0,2,2,0]
]

def cert1133n : CertifiedBoard :=
  ⟨seed1133, by apply FastValid.valid; decide +kernel⟩

def cert1133r : CertifiedBoard :=
  ⟨seed1133.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1134 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,1,0,1,1,0,0,0,2],
  [0,2,1,1,1,0,2,1,0,0,0,1,0,1,1],
  [1,0,0,1,2,2,0,1,2,0,2,2,0,2,0,1,0],
  [1,1,1,0,2,0,2,0,0,2,1,2,0,1,1,2,0,0,2]
]

def cert1134n : CertifiedBoard :=
  ⟨seed1134, by apply FastValid.valid; decide +kernel⟩

def cert1134r : CertifiedBoard :=
  ⟨seed1134.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1135 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,1,0,1,1,0,0,0,2],
  [0,2,1,1,1,1,2,2,0,1,0,1,1,0,2],
  [2,0,1,1,0,0,0,2,0,2,0,0,1,2,0,0,1],
  [0,1,2,0,2,1,0,0,2,1,2,0,2,2,0,1,0,2,0]
]

def cert1135n : CertifiedBoard :=
  ⟨seed1135, by apply FastValid.valid; decide +kernel⟩

def cert1135r : CertifiedBoard :=
  ⟨seed1135.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1136 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,1,0,1,1,0,0,0,2],
  [1,0,2,1,1,1,1,0,0,0,2,1,2,0,1],
  [0,1,0,1,2,2,0,2,0,0,1,1,2,0,2,0,0],
  [0,0,2,1,0,0,1,1,0,2,2,0,1,2,0,2,0,1,0]
]

def cert1136n : CertifiedBoard :=
  ⟨seed1136, by apply FastValid.valid; decide +kernel⟩

def cert1136r : CertifiedBoard :=
  ⟨seed1136.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1137 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,1,0,1,1,0,0,0,2],
  [2,2,0,1,1,0,2,1,0,0,0,2,0,1,2],
  [1,1,2,0,0,2,0,2,0,0,1,0,0,1,1,1,1],
  [1,2,0,2,1,2,0,2,1,1,0,1,0,2,2,0,1,2,2]
]

def cert1137n : CertifiedBoard :=
  ⟨seed1137, by apply FastValid.valid; decide +kernel⟩

def cert1137r : CertifiedBoard :=
  ⟨seed1137.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1138 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,1,0,1,1,0,0,2,1],
  [1,0,0,1,1,1,1,0,2,0,2,2,0,1,0],
  [0,2,1,0,1,2,0,0,2,1,1,0,2,0,0,0,2],
  [2,1,2,0,1,0,0,0,1,1,2,2,0,1,2,0,2,0,2]
]

def cert1138n : CertifiedBoard :=
  ⟨seed1138, by apply FastValid.valid; decide +kernel⟩

def cert1138r : CertifiedBoard :=
  ⟨seed1138.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1139 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,1,0,1,1,0,2,0,2],
  [0,0,2,1,1,1,2,2,0,1,0,0,1,1,1],
  [1,1,0,1,1,0,0,0,0,2,2,0,2,0,2,0,0],
  [0,1,2,0,0,2,1,0,2,1,2,0,1,0,0,1,2,0,1]
]

def cert1139n : CertifiedBoard :=
  ⟨seed1139, by apply FastValid.valid; decide +kernel⟩

def cert1139r : CertifiedBoard :=
  ⟨seed1139.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1140 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,1,0,1,1,0,2,0,2],
  [1,0,2,1,1,1,2,2,0,2,1,2,0,0,0],
  [0,1,0,0,1,2,0,1,1,1,0,0,0,2,0,1,0],
  [0,0,2,0,2,2,0,1,1,0,0,2,1,0,1,2,0,0,1]
]

def cert1140n : CertifiedBoard :=
  ⟨seed1140, by apply FastValid.valid; decide +kernel⟩

def cert1140r : CertifiedBoard :=
  ⟨seed1140.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1141 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,1,0,1,1,1,0,0,0],
  [0,0,1,1,2,0,2,1,0,0,2,0,1,0,2],
  [0,2,2,0,1,0,2,1,1,1,0,1,2,0,0,2,1],
  [2,1,2,0,1,1,0,0,1,2,2,0,0,0,2,0,2,0,2]
]

def cert1141n : CertifiedBoard :=
  ⟨seed1141, by apply FastValid.valid; decide +kernel⟩

def cert1141r : CertifiedBoard :=
  ⟨seed1141.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1142 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,1,0,1,1,1,0,0,0],
  [0,0,2,1,1,1,2,2,0,1,2,0,1,0,2],
  [1,1,0,1,1,0,0,0,1,2,0,0,2,2,0,2,0],
  [2,0,2,0,0,2,1,0,0,1,0,2,1,2,0,2,0,1,1]
]

def cert1142n : CertifiedBoard :=
  ⟨seed1142, by apply FastValid.valid; decide +kernel⟩

def cert1142r : CertifiedBoard :=
  ⟨seed1142.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1143 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,1,0,1,1,1,0,0,2],
  [1,2,0,1,1,1,2,2,0,1,2,0,0,1,2],
  [0,1,0,2,2,0,0,2,1,1,0,0,1,0,0,0,0],
  [0,0,2,1,2,0,2,0,2,0,2,0,1,1,0,2,1,0,1]
]

def cert1143n : CertifiedBoard :=
  ⟨seed1143, by apply FastValid.valid; decide +kernel⟩

def cert1143r : CertifiedBoard :=
  ⟨seed1143.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1144 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,1,0,1,1,1,0,2,1],
  [2,1,0,0,1,2,0,0,2,0,1,0,0,0,2],
  [1,1,2,2,0,0,0,2,0,1,1,0,0,1,0,1,2],
  [1,2,0,2,0,2,1,2,0,1,1,1,0,2,2,0,2,1,1]
]

def cert1144n : CertifiedBoard :=
  ⟨seed1144, by apply FastValid.valid; decide +kernel⟩

def cert1144r : CertifiedBoard :=
  ⟨seed1144.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1145 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,1,0,1,1,1,2,0,1],
  [0,1,0,0,0,0,2,1,2,2,0,1,2,0,2],
  [0,0,1,0,2,2,0,1,1,0,2,1,0,0,1,1,0],
  [1,0,0,2,0,2,0,2,0,0,2,1,1,1,0,1,2,0,0]
]

def cert1145n : CertifiedBoard :=
  ⟨seed1145, by apply FastValid.valid; decide +kernel⟩

def cert1145r : CertifiedBoard :=
  ⟨seed1145.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1146 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,1,0,1,1,1,2,0,2],
  [0,2,1,1,0,0,1,0,1,2,0,1,2,0,1],
  [2,1,0,0,2,0,1,1,0,0,0,2,0,0,0,2,1],
  [0,1,1,1,0,2,1,2,2,0,0,1,0,2,2,0,2,0,2]
]

def cert1146n : CertifiedBoard :=
  ⟨seed1146, by apply FastValid.valid; decide +kernel⟩

def cert1146r : CertifiedBoard :=
  ⟨seed1146.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1147 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,1,0,1,1,2,0,1,1],
  [0,0,2,1,1,0,2,1,2,0,2,0,1,0,0],
  [1,1,0,1,2,2,0,0,0,0,1,0,0,1,2,0,2],
  [0,2,0,1,1,1,1,0,2,1,0,0,2,2,0,0,2,0,2]
]

def cert1147n : CertifiedBoard :=
  ⟨seed1147, by apply FastValid.valid; decide +kernel⟩

def cert1147r : CertifiedBoard :=
  ⟨seed1147.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1148 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,1,0,1,1,2,0,1,1],
  [0,2,1,1,0,0,0,0,1,2,0,2,0,1,0],
  [1,0,2,0,0,2,2,0,1,1,1,1,0,0,2,0,2],
  [1,1,0,1,2,0,0,2,1,2,2,0,2,1,0,0,1,0,2]
]

def cert1148n : CertifiedBoard :=
  ⟨seed1148, by apply FastValid.valid; decide +kernel⟩

def cert1148r : CertifiedBoard :=
  ⟨seed1148.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1149 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,1,0,1,1,2,0,2,0],
  [0,0,2,1,1,1,1,0,1,0,0,1,1,0,0],
  [1,0,2,0,1,2,0,2,1,2,2,0,0,2,0,1,0],
  [2,0,0,1,2,0,1,1,0,0,0,0,2,1,0,2,2,0,2]
]

def cert1149n : CertifiedBoard :=
  ⟨seed1149, by apply FastValid.valid; decide +kernel⟩

def cert1149r : CertifiedBoard :=
  ⟨seed1149.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1150 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,1,0,1,1,2,0,2,0],
  [1,0,1,1,1,0,2,1,2,0,1,2,0,1,0],
  [2,0,0,1,0,0,2,1,1,1,0,0,0,0,2,0,2],
  [0,0,2,2,0,2,0,0,1,2,2,0,1,1,0,2,1,0,0]
]

def cert1150n : CertifiedBoard :=
  ⟨seed1150, by apply FastValid.valid; decide +kernel⟩

def cert1150r : CertifiedBoard :=
  ⟨seed1150.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1151 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,1,0,1,1,2,0,2,0],
  [2,0,0,1,1,0,2,1,2,2,0,1,0,0,2],
  [1,1,0,2,0,1,0,0,0,0,2,1,0,0,1,1,1],
  [0,0,2,0,1,2,0,2,2,0,2,1,1,1,0,1,2,0,0]
]

def cert1151n : CertifiedBoard :=
  ⟨seed1151, by apply FastValid.valid; decide +kernel⟩

def cert1151r : CertifiedBoard :=
  ⟨seed1151.map List.reverse, by apply FastValid.valid; decide +kernel⟩

end TBoards.Extended
