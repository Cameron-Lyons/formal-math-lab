import Extended.Batch032

/- Generated from extended_seeds.json. Published seeds 0–4:
   Qiyuan Ma, DOI 10.5281/zenodo.23631079, CC-BY-4.0. -/

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.Extended

def seed1152 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,1,0,1,2,0,2,1,1],
  [0,2,0,1,1,0,2,0,0,0,1,1,2,0,2],
  [2,0,1,2,0,1,0,0,0,1,0,1,1,1,0,2,0],
  [1,1,1,0,0,2,2,0,2,1,2,2,0,0,2,1,0,0,2]
]

def cert1152n : CertifiedBoard :=
  ⟨seed1152, by apply FastValid.valid; decide +kernel⟩

def cert1152r : CertifiedBoard :=
  ⟨seed1152.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1153 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,1,0,2,0,1,1,1,2],
  [0,0,2,0,2,1,1,1,0,1,1,0,0,0,0],
  [1,0,1,0,0,1,2,2,0,2,0,1,2,0,2,1,0],
  [1,2,0,0,2,2,0,0,2,1,2,0,1,1,0,0,1,0,2]
]

def cert1153n : CertifiedBoard :=
  ⟨seed1153, by apply FastValid.valid; decide +kernel⟩

def cert1153r : CertifiedBoard :=
  ⟨seed1153.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1154 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,1,0,2,0,2,0,1,1],
  [1,1,0,0,1,1,2,0,0,0,2,1,0,0,0],
  [2,0,2,1,2,0,1,0,1,0,1,1,1,0,2,2,0],
  [0,0,2,1,1,1,0,0,2,0,0,1,2,2,0,1,2,0,2]
]

def cert1154n : CertifiedBoard :=
  ⟨seed1154, by apply FastValid.valid; decide +kernel⟩

def cert1154r : CertifiedBoard :=
  ⟨seed1154.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1155 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,1,0,2,0,2,1,1,0],
  [1,0,1,2,0,0,0,2,0,1,0,1,0,0,2],
  [1,1,0,0,0,2,1,0,2,0,2,1,2,0,1,1,1],
  [2,2,0,2,2,0,0,1,1,0,0,1,1,1,2,0,1,2,2]
]

def cert1155n : CertifiedBoard :=
  ⟨seed1155, by apply FastValid.valid; decide +kernel⟩

def cert1155r : CertifiedBoard :=
  ⟨seed1155.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1156 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,1,0,2,0,2,1,1,1],
  [1,1,0,1,1,1,2,0,0,2,0,1,2,2,0],
  [2,0,0,0,1,1,0,0,1,0,2,0,1,0,0,0,2],
  [1,2,0,2,2,0,2,1,2,0,1,1,0,0,2,1,0,1,2]
]

def cert1156n : CertifiedBoard :=
  ⟨seed1156, by apply FastValid.valid; decide +kernel⟩

def cert1156r : CertifiedBoard :=
  ⟨seed1156.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1157 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,1,0,2,0,2,1,1,2],
  [1,0,0,2,0,0,1,1,0,1,1,1,1,0,0],
  [0,0,2,2,0,1,0,1,0,0,1,2,2,0,2,1,0],
  [1,2,0,1,1,0,2,1,2,0,2,0,1,2,0,0,0,0,2]
]

def cert1157n : CertifiedBoard :=
  ⟨seed1157, by apply FastValid.valid; decide +kernel⟩

def cert1157r : CertifiedBoard :=
  ⟨seed1157.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1158 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,1,0,2,1,1,0,0,0],
  [1,0,0,1,1,1,1,0,2,0,2,0,2,1,0],
  [0,0,2,2,0,1,2,2,0,1,2,0,1,0,1,1,0],
  [1,0,1,1,2,0,0,0,2,1,2,0,2,0,0,1,0,0,2]
]

def cert1158n : CertifiedBoard :=
  ⟨seed1158, by apply FastValid.valid; decide +kernel⟩

def cert1158r : CertifiedBoard :=
  ⟨seed1158.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1159 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,1,0,2,1,1,0,0,2],
  [0,0,1,1,1,0,1,0,0,1,1,1,0,2,0],
  [2,0,1,0,0,0,2,2,0,2,0,1,2,2,0,1,1],
  [1,1,2,0,2,1,0,1,2,0,0,0,2,0,2,1,2,0,0]
]

def cert1159n : CertifiedBoard :=
  ⟨seed1159, by apply FastValid.valid; decide +kernel⟩

def cert1159r : CertifiedBoard :=
  ⟨seed1159.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1160 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,1,0,2,1,1,0,0,2],
  [0,1,1,1,2,0,1,0,0,0,0,2,2,0,2],
  [2,0,1,1,1,0,1,0,0,2,1,0,1,2,0,0,1],
  [0,2,1,2,2,0,0,1,2,0,2,0,2,0,1,1,0,2,0]
]

def cert1160n : CertifiedBoard :=
  ⟨seed1160, by apply FastValid.valid; decide +kernel⟩

def cert1160r : CertifiedBoard :=
  ⟨seed1160.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1161 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,1,0,2,1,1,0,0,2],
  [2,0,2,0,1,1,2,0,0,0,0,2,1,2,0],
  [0,2,1,0,1,1,0,0,1,0,2,0,1,1,1,1,0],
  [1,0,1,2,2,0,1,0,0,1,2,0,2,2,0,2,0,0,2]
]

def cert1161n : CertifiedBoard :=
  ⟨seed1161, by apply FastValid.valid; decide +kernel⟩

def cert1161r : CertifiedBoard :=
  ⟨seed1161.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1162 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,1,0,2,1,1,0,1,2],
  [0,0,1,1,1,1,2,2,0,1,2,0,0,0,2],
  [1,2,0,1,1,0,0,2,0,2,0,0,1,1,0,0,0],
  [0,1,0,0,2,0,1,0,2,1,2,0,2,2,0,2,1,0,1]
]

def cert1162n : CertifiedBoard :=
  ⟨seed1162, by apply FastValid.valid; decide +kernel⟩

def cert1162r : CertifiedBoard :=
  ⟨seed1162.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1163 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,1,0,2,1,1,0,1,2],
  [1,1,0,0,0,0,1,0,1,1,1,0,2,0,1],
  [1,2,0,1,0,0,2,0,0,1,2,2,0,2,0,0,2],
  [0,1,1,2,0,2,2,0,2,1,0,0,2,1,2,0,1,1,1]
]

def cert1163n : CertifiedBoard :=
  ⟨seed1163, by apply FastValid.valid; decide +kernel⟩

def cert1163r : CertifiedBoard :=
  ⟨seed1163.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1164 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,1,0,2,1,1,0,1,2],
  [2,0,0,0,1,1,1,0,2,0,1,0,0,0,2],
  [1,2,0,2,0,1,2,0,0,2,1,0,0,1,0,1,1],
  [1,1,1,2,0,2,2,0,1,1,0,0,2,1,2,2,0,2,0]
]

def cert1164n : CertifiedBoard :=
  ⟨seed1164, by apply FastValid.valid; decide +kernel⟩

def cert1164r : CertifiedBoard :=
  ⟨seed1164.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1165 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,1,0,2,1,1,1,0,0],
  [0,0,1,1,2,0,1,1,0,1,2,2,0,0,2],
  [2,1,0,1,0,0,1,1,1,0,0,0,0,2,2,0,2],
  [0,2,0,2,0,1,0,2,0,0,2,1,2,0,1,2,0,2,1]
]

def cert1165n : CertifiedBoard :=
  ⟨seed1165, by apply FastValid.valid; decide +kernel⟩

def cert1165r : CertifiedBoard :=
  ⟨seed1165.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1166 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,1,0,2,1,1,1,0,0],
  [1,0,0,2,0,0,1,0,1,2,2,0,2,1,0],
  [0,1,1,0,2,1,2,0,1,1,1,2,0,0,0,0,2],
  [0,0,1,2,0,1,1,0,1,0,0,2,0,2,0,2,2,0,1]
]

def cert1166n : CertifiedBoard :=
  ⟨seed1166, by apply FastValid.valid; decide +kernel⟩

def cert1166r : CertifiedBoard :=
  ⟨seed1166.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1167 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,1,0,2,1,1,1,0,0],
  [1,0,0,2,0,0,1,0,1,2,2,0,2,1,0],
  [0,1,1,0,2,1,2,0,1,1,1,2,0,0,0,0,2],
  [0,0,1,2,0,1,1,0,1,0,0,2,0,2,2,0,2,0,1]
]

def cert1167n : CertifiedBoard :=
  ⟨seed1167, by apply FastValid.valid; decide +kernel⟩

def cert1167r : CertifiedBoard :=
  ⟨seed1167.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1168 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,1,0,2,1,1,1,0,0],
  [1,2,0,1,1,1,2,2,0,2,0,1,0,0,2],
  [0,0,0,0,1,1,0,0,2,1,2,0,0,2,1,0,1],
  [0,1,1,0,2,2,0,2,0,2,0,0,1,0,1,2,0,1,2]
]

def cert1168n : CertifiedBoard :=
  ⟨seed1168, by apply FastValid.valid; decide +kernel⟩

def cert1168r : CertifiedBoard :=
  ⟨seed1168.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1169 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,1,0,2,1,1,1,0,0],
  [2,1,2,0,1,1,2,0,0,0,2,0,1,0,2],
  [0,0,1,0,1,1,0,0,2,1,0,1,2,0,0,2,1],
  [1,1,0,0,0,1,2,2,0,2,0,2,2,0,2,0,1,1,1]
]

def cert1169n : CertifiedBoard :=
  ⟨seed1169, by apply FastValid.valid; decide +kernel⟩

def cert1169r : CertifiedBoard :=
  ⟨seed1169.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1170 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,1,0,2,1,1,1,2,0],
  [0,1,0,0,0,0,1,0,1,2,2,0,2,0,2],
  [1,1,0,0,2,0,0,1,2,0,1,1,0,2,1,0,1],
  [2,0,0,2,2,0,2,1,2,0,1,1,1,0,0,2,0,1,1]
]

def cert1170n : CertifiedBoard :=
  ⟨seed1170, by apply FastValid.valid; decide +kernel⟩

def cert1170r : CertifiedBoard :=
  ⟨seed1170.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1171 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,1,0,2,1,1,1,2,0],
  [0,1,1,0,0,0,1,0,1,1,1,0,0,0,2],
  [1,2,0,1,1,0,2,2,0,2,0,0,2,0,0,1,2],
  [2,0,2,0,1,2,2,0,2,1,0,1,0,0,2,1,2,0,1]
]

def cert1171n : CertifiedBoard :=
  ⟨seed1171, by apply FastValid.valid; decide +kernel⟩

def cert1171r : CertifiedBoard :=
  ⟨seed1171.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1172 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,1,0,2,1,1,2,0,1],
  [0,1,1,0,1,1,1,0,1,2,0,2,0,1,0],
  [1,0,0,0,2,2,0,1,2,0,0,1,0,0,2,0,2],
  [1,1,1,0,2,0,2,1,0,0,2,1,2,2,0,0,0,1,1]
]

def cert1172n : CertifiedBoard :=
  ⟨seed1172, by apply FastValid.valid; decide +kernel⟩

def cert1172r : CertifiedBoard :=
  ⟨seed1172.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1173 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,1,0,2,1,1,2,0,1],
  [0,1,1,1,0,0,1,0,0,2,0,2,1,2,0],
  [2,0,1,1,1,0,2,2,0,0,1,1,0,0,0,0,2],
  [0,1,2,0,1,2,2,0,2,0,2,0,0,2,1,0,1,0,1]
]

def cert1173n : CertifiedBoard :=
  ⟨seed1173, by apply FastValid.valid; decide +kernel⟩

def cert1173r : CertifiedBoard :=
  ⟨seed1173.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1174 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,1,0,2,1,1,2,0,2],
  [1,0,0,0,1,1,1,0,1,2,0,2,1,0,0],
  [0,0,0,2,1,2,2,0,1,1,1,0,2,0,0,1,0],
  [2,0,2,2,0,1,0,1,1,0,0,2,0,0,2,0,1,2,0]
]

def cert1174n : CertifiedBoard :=
  ⟨seed1174, by apply FastValid.valid; decide +kernel⟩

def cert1174r : CertifiedBoard :=
  ⟨seed1174.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1175 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,1,0,2,1,1,2,0,2],
  [1,0,0,1,1,0,1,2,0,1,1,1,0,1,2],
  [1,2,0,2,2,0,1,0,0,0,2,0,0,0,1,0,0],
  [0,0,2,0,0,2,1,2,2,0,1,1,1,0,2,0,2,1,0]
]

def cert1175n : CertifiedBoard :=
  ⟨seed1175, by apply FastValid.valid; decide +kernel⟩

def cert1175r : CertifiedBoard :=
  ⟨seed1175.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1176 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,1,0,2,1,1,2,0,2],
  [1,0,0,1,1,1,1,0,1,2,0,2,0,0,0],
  [1,0,0,2,2,0,0,2,0,1,0,1,1,0,2,1,0],
  [0,0,0,1,0,0,2,0,2,1,2,2,0,1,2,0,1,1,0]
]

def cert1176n : CertifiedBoard :=
  ⟨seed1176, by apply FastValid.valid; decide +kernel⟩

def cert1176r : CertifiedBoard :=
  ⟨seed1176.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1177 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,2,0,1,0,0,0,2,1],
  [0,2,1,1,1,1,0,1,1,0,1,0,0,1,1],
  [2,1,0,2,1,0,0,0,1,2,0,0,2,0,2,0,2],
  [1,1,2,1,2,0,0,2,2,0,1,1,0,2,0,1,2,0,2]
]

def cert1177n : CertifiedBoard :=
  ⟨seed1177, by apply FastValid.valid; decide +kernel⟩

def cert1177r : CertifiedBoard :=
  ⟨seed1177.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1178 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,2,0,1,0,0,1,1,2],
  [1,0,0,2,1,0,2,0,2,1,0,1,1,1,0],
  [0,0,2,1,2,0,1,0,1,1,1,0,2,0,0,0,2],
  [1,2,0,1,2,1,1,0,0,1,2,0,2,0,2,2,0,0,0]
]

def cert1178n : CertifiedBoard :=
  ⟨seed1178, by apply FastValid.valid; decide +kernel⟩

def cert1178r : CertifiedBoard :=
  ⟨seed1178.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1179 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,2,0,1,0,0,2,1,1],
  [1,1,0,1,1,1,2,0,2,0,0,2,0,0,0],
  [0,1,1,0,2,1,0,0,1,0,2,2,0,2,1,0,1],
  [0,0,1,2,0,1,2,1,2,0,1,1,1,0,0,0,2,0,2]
]

def cert1179n : CertifiedBoard :=
  ⟨seed1179, by apply FastValid.valid; decide +kernel⟩

def cert1179r : CertifiedBoard :=
  ⟨seed1179.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1180 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,2,0,1,0,1,1,1,2],
  [0,1,1,0,0,0,0,2,1,0,1,1,0,0,1],
  [2,1,2,0,2,0,0,1,0,2,0,1,2,1,0,0,2],
  [1,2,0,1,2,0,2,2,0,0,2,0,2,1,1,1,0,2,1]
]

def cert1180n : CertifiedBoard :=
  ⟨seed1180, by apply FastValid.valid; decide +kernel⟩

def cert1180r : CertifiedBoard :=
  ⟨seed1180.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1181 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,2,0,1,0,1,1,2,0],
  [2,0,2,1,1,1,1,0,2,1,0,0,0,0,2],
  [0,2,0,0,2,0,1,1,0,1,2,0,1,1,0,0,1],
  [0,1,0,2,2,0,2,0,0,2,1,0,0,1,2,1,2,0,2]
]

def cert1181n : CertifiedBoard :=
  ⟨seed1181, by apply FastValid.valid; decide +kernel⟩

def cert1181r : CertifiedBoard :=
  ⟨seed1181.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1182 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,2,0,1,0,1,2,0,2],
  [0,0,1,1,2,1,1,0,2,0,1,1,1,0,0],
  [0,2,2,0,0,0,2,1,0,0,1,1,1,0,0,2,1],
  [2,1,0,2,1,2,0,2,0,1,0,1,2,0,2,0,0,0,2]
]

def cert1182n : CertifiedBoard :=
  ⟨seed1182, by apply FastValid.valid; decide +kernel⟩

def cert1182r : CertifiedBoard :=
  ⟨seed1182.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1183 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,2,0,1,0,1,2,0,2],
  [2,0,2,1,1,1,1,0,2,0,0,0,1,1,2],
  [0,0,0,2,0,1,2,1,0,1,1,0,0,1,1,0,0],
  [1,2,0,1,0,2,0,0,2,1,0,0,2,1,2,0,2,2,0]
]

def cert1183n : CertifiedBoard :=
  ⟨seed1183, by apply FastValid.valid; decide +kernel⟩

def cert1183r : CertifiedBoard :=
  ⟨seed1183.map List.reverse, by apply FastValid.valid; decide +kernel⟩

end TBoards.Extended
