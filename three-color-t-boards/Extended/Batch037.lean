import Extended.Batch033

/- Generated from extended_seeds.json. Published seeds 0–4:
   Qiyuan Ma, DOI 10.5281/zenodo.23631079, CC-BY-4.0. -/

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.Extended

def seed1184 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,2,0,1,0,1,2,0,2],
  [2,0,2,1,1,1,1,0,2,0,0,0,1,1,2],
  [0,0,0,2,0,1,2,1,0,1,1,0,0,1,1,0,0],
  [1,2,0,1,0,2,0,0,2,1,2,0,2,1,0,0,2,2,0]
]

def cert1184n : CertifiedBoard :=
  ⟨seed1184, by apply FastValid.valid; decide +kernel⟩

def cert1184r : CertifiedBoard :=
  ⟨seed1184.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1185 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,2,0,1,0,1,2,0,2],
  [2,0,2,1,1,1,1,0,2,1,0,0,1,0,2],
  [0,0,0,2,0,1,2,1,0,1,1,0,0,1,1,0,0],
  [0,2,0,1,1,2,0,0,2,0,0,0,2,1,2,0,2,2,0]
]

def cert1185n : CertifiedBoard :=
  ⟨seed1185, by apply FastValid.valid; decide +kernel⟩

def cert1185r : CertifiedBoard :=
  ⟨seed1185.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1186 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,2,0,1,0,2,0,2,1],
  [1,0,1,2,0,1,1,0,2,1,0,1,0,0,2],
  [2,1,0,0,0,0,1,2,0,0,1,1,0,0,2,1,1],
  [1,1,2,1,2,0,2,0,0,2,2,0,2,0,1,1,1,1,0]
]

def cert1186n : CertifiedBoard :=
  ⟨seed1186, by apply FastValid.valid; decide +kernel⟩

def cert1186r : CertifiedBoard :=
  ⟨seed1186.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1187 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,2,0,1,1,0,0,2,0],
  [1,0,0,0,1,0,2,1,2,1,0,1,1,1,0],
  [1,0,0,2,2,0,2,1,1,1,2,0,0,0,2,1,0],
  [2,0,0,1,0,1,2,0,2,0,1,2,0,2,0,1,1,0,2]
]

def cert1187n : CertifiedBoard :=
  ⟨seed1187, by apply FastValid.valid; decide +kernel⟩

def cert1187r : CertifiedBoard :=
  ⟨seed1187.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1188 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,2,0,1,1,0,0,2,0],
  [1,0,0,1,1,1,1,2,0,1,0,2,1,1,0],
  [2,0,2,0,0,0,2,1,0,1,1,0,1,2,0,0,2],
  [0,2,1,2,0,2,2,0,2,0,1,2,1,0,0,0,1,0,2]
]

def cert1188n : CertifiedBoard :=
  ⟨seed1188, by apply FastValid.valid; decide +kernel⟩

def cert1188r : CertifiedBoard :=
  ⟨seed1188.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1189 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,2,0,1,1,0,1,1,2],
  [1,0,0,0,1,0,2,1,0,0,2,0,1,2,0],
  [1,2,1,2,0,0,0,1,2,0,1,0,0,2,1,1,0],
  [2,0,2,0,0,2,2,0,2,0,2,1,0,1,1,1,1,0,2]
]

def cert1189n : CertifiedBoard :=
  ⟨seed1189, by apply FastValid.valid; decide +kernel⟩

def cert1189r : CertifiedBoard :=
  ⟨seed1189.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1190 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,2,0,1,1,0,1,2,0],
  [0,0,1,1,2,0,2,1,2,1,0,0,0,0,2],
  [0,1,0,1,0,0,2,1,1,1,1,0,2,2,0,0,1],
  [2,0,1,2,0,1,1,0,0,2,0,2,1,0,2,0,2,0,0]
]

def cert1190n : CertifiedBoard :=
  ⟨seed1190, by apply FastValid.valid; decide +kernel⟩

def cert1190r : CertifiedBoard :=
  ⟨seed1190.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1191 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,2,0,1,1,0,2,0,2],
  [2,0,1,1,1,0,0,0,2,1,0,2,1,2,0],
  [1,0,1,0,0,0,2,1,0,0,1,0,1,2,1,1,0],
  [0,1,2,0,2,2,0,0,2,0,2,0,1,1,1,2,0,0,1]
]

def cert1191n : CertifiedBoard :=
  ⟨seed1191, by apply FastValid.valid; decide +kernel⟩

def cert1191r : CertifiedBoard :=
  ⟨seed1191.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1192 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,2,0,1,1,1,0,0,0],
  [0,0,2,1,1,1,2,0,2,0,0,0,1,1,0],
  [1,2,0,0,1,2,1,0,1,0,2,1,0,0,2,1,2],
  [1,0,0,2,2,0,1,1,0,1,0,2,0,2,0,1,2,0,2]
]

def cert1192n : CertifiedBoard :=
  ⟨seed1192, by apply FastValid.valid; decide +kernel⟩

def cert1192r : CertifiedBoard :=
  ⟨seed1192.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1193 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,2,0,1,1,1,0,0,1],
  [0,1,0,1,1,0,2,0,2,0,2,1,0,0,2],
  [1,0,1,2,0,1,0,2,1,2,0,0,0,0,2,1,1],
  [1,1,1,0,0,2,0,0,1,2,0,2,2,0,1,1,2,1,0]
]

def cert1193n : CertifiedBoard :=
  ⟨seed1193, by apply FastValid.valid; decide +kernel⟩

def cert1193r : CertifiedBoard :=
  ⟨seed1193.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1194 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,2,0,1,1,1,0,2,0],
  [2,0,2,1,1,1,2,0,1,2,1,0,1,1,0],
  [1,0,0,1,2,0,1,0,1,0,0,2,0,0,0,2,0],
  [2,0,2,2,0,0,1,1,0,2,1,2,0,2,1,0,0,0,2]
]

def cert1194n : CertifiedBoard :=
  ⟨seed1194, by apply FastValid.valid; decide +kernel⟩

def cert1194r : CertifiedBoard :=
  ⟨seed1194.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1195 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,2,0,1,1,1,0,2,1],
  [1,1,0,0,0,0,2,0,1,2,0,0,1,1,1],
  [2,1,0,0,2,2,0,0,1,1,0,1,0,0,2,0,2],
  [1,1,2,1,0,1,2,0,2,0,1,0,2,1,2,0,2,1,1]
]

def cert1195n : CertifiedBoard :=
  ⟨seed1195, by apply FastValid.valid; decide +kernel⟩

def cert1195r : CertifiedBoard :=
  ⟨seed1195.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1196 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,2,0,1,1,1,2,0,2],
  [0,1,0,2,0,0,0,2,0,1,2,1,1,0,1],
  [1,0,1,0,2,1,2,0,0,1,1,0,0,0,2,1,0],
  [0,2,1,0,0,1,1,1,0,0,2,0,2,2,0,1,2,0,2]
]

def cert1196n : CertifiedBoard :=
  ⟨seed1196, by apply FastValid.valid; decide +kernel⟩

def cert1196r : CertifiedBoard :=
  ⟨seed1196.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1197 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,2,0,1,1,1,2,0,2],
  [1,1,0,0,1,0,1,2,0,2,1,0,2,1,1],
  [1,0,0,2,0,2,0,0,0,0,2,0,0,1,1,1,0],
  [1,2,0,1,1,0,2,1,0,1,0,0,2,2,0,1,2,1,2]
]

def cert1197n : CertifiedBoard :=
  ⟨seed1197, by apply FastValid.valid; decide +kernel⟩

def cert1197r : CertifiedBoard :=
  ⟨seed1197.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1198 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,2,0,1,1,2,0,2,0],
  [2,0,0,1,1,0,2,1,2,1,0,1,0,0,2],
  [1,1,0,2,0,1,0,0,0,0,2,1,0,0,1,1,1],
  [0,0,2,0,1,2,0,2,2,0,2,1,1,1,0,1,2,0,0]
]

def cert1198n : CertifiedBoard :=
  ⟨seed1198, by apply FastValid.valid; decide +kernel⟩

def cert1198r : CertifiedBoard :=
  ⟨seed1198.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1199 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,2,0,1,2,0,2,1,1],
  [2,0,0,1,1,1,1,0,1,0,1,1,2,0,0],
  [0,0,2,1,0,0,2,1,0,0,0,1,1,0,2,2,0],
  [1,1,0,2,0,2,0,1,2,1,2,0,2,0,1,0,0,0,2]
]

def cert1199n : CertifiedBoard :=
  ⟨seed1199, by apply FastValid.valid; decide +kernel⟩

def cert1199r : CertifiedBoard :=
  ⟨seed1199.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1200 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,2,0,2,1,1,0,2,1],
  [2,1,0,1,1,1,2,0,0,2,0,1,1,1,0],
  [1,0,0,2,1,0,0,0,1,0,0,0,1,2,0,0,2],
  [0,1,1,0,1,2,1,2,0,1,0,2,2,0,2,0,2,0,1]
]

def cert1200n : CertifiedBoard :=
  ⟨seed1200, by apply FastValid.valid; decide +kernel⟩

def cert1200r : CertifiedBoard :=
  ⟨seed1200.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1201 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,2,0,2,1,1,0,2,1],
  [2,1,2,0,1,0,0,0,1,1,1,0,1,2,0],
  [1,0,1,1,1,0,0,2,2,0,0,2,0,0,0,1,0],
  [2,0,2,0,1,2,1,0,0,2,0,1,1,2,0,2,1,0,2]
]

def cert1201n : CertifiedBoard :=
  ⟨seed1201, by apply FastValid.valid; decide +kernel⟩

def cert1201r : CertifiedBoard :=
  ⟨seed1201.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1202 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,2,0,2,1,1,1,0,0],
  [1,0,2,0,1,0,2,1,0,1,1,1,0,1,0],
  [0,0,0,1,2,0,1,1,2,1,2,0,2,0,0,2,0],
  [2,0,2,2,0,0,2,1,0,0,1,2,0,1,1,0,0,0,2]
]

def cert1202n : CertifiedBoard :=
  ⟨seed1202, by apply FastValid.valid; decide +kernel⟩

def cert1202r : CertifiedBoard :=
  ⟨seed1202.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1203 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,2,0,2,1,1,1,0,0],
  [1,2,0,1,1,1,2,0,0,2,0,0,0,2,1],
  [0,0,2,1,2,1,0,0,1,0,0,0,1,1,0,1,2],
  [2,1,0,2,0,1,2,0,2,0,2,2,0,1,1,0,1,0,2]
]

def cert1203n : CertifiedBoard :=
  ⟨seed1203, by apply FastValid.valid; decide +kernel⟩

def cert1203r : CertifiedBoard :=
  ⟨seed1203.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1204 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,0,0,2,0,1,0,1,1,1,0],
  [1,0,0,1,0,0,2,1,2,2,0,1,1,1,0],
  [2,1,2,0,2,1,0,2,2,0,2,0,1,2,0,2,1],
  [2,1,1,0,2,2,1,0,1,2,0,0,2,0,0,1,1,2,1]
]

def cert1204n : CertifiedBoard :=
  ⟨seed1204, by apply FastValid.valid; decide +kernel⟩

def cert1204r : CertifiedBoard :=
  ⟨seed1204.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1205 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,0,0,2,0,1,0,1,1,2,0],
  [1,2,0,0,1,0,0,2,1,0,1,2,2,1,2],
  [2,0,2,0,2,0,1,1,0,2,1,0,0,1,2,1,1],
  [1,1,0,2,2,0,2,2,0,0,2,1,2,0,1,1,1,1,0]
]

def cert1205n : CertifiedBoard :=
  ⟨seed1205, by apply FastValid.valid; decide +kernel⟩

def cert1205r : CertifiedBoard :=
  ⟨seed1205.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1206 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,0,0,2,0,1,0,2,2,1,1],
  [1,1,0,0,2,2,0,2,1,0,1,1,2,2,0],
  [2,0,1,2,0,1,2,0,2,0,0,1,1,1,0,1,0],
  [0,0,2,0,2,1,0,0,1,1,1,0,2,1,2,1,2,0,0]
]

def cert1206n : CertifiedBoard :=
  ⟨seed1206, by apply FastValid.valid; decide +kernel⟩

def cert1206r : CertifiedBoard :=
  ⟨seed1206.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1207 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,0,0,2,0,1,1,0,2,1,1],
  [1,0,0,1,1,0,0,2,2,0,1,0,1,2,1],
  [2,1,0,2,1,2,0,0,2,2,1,2,2,0,0,1,0],
  [1,1,1,0,1,1,1,2,0,1,2,0,2,0,2,0,2,1,0]
]

def cert1207n : CertifiedBoard :=
  ⟨seed1207, by apply FastValid.valid; decide +kernel⟩

def cert1207r : CertifiedBoard :=
  ⟨seed1207.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1208 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,0,0,2,0,1,1,1,0,1,2],
  [0,1,0,2,2,0,0,2,1,2,0,2,0,1,1],
  [1,1,0,0,2,2,1,0,0,1,2,0,2,1,2,1,0],
  [1,2,2,0,1,0,2,0,0,1,1,1,2,0,2,1,1,0,1]
]

def cert1208n : CertifiedBoard :=
  ⟨seed1208, by apply FastValid.valid; decide +kernel⟩

def cert1208r : CertifiedBoard :=
  ⟨seed1208.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1209 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,0,0,2,0,2,1,1,1,0,1],
  [2,1,0,1,0,2,0,1,1,2,2,0,0,1,0],
  [0,1,2,1,0,0,2,0,1,1,0,2,1,2,0,2,2],
  [2,2,0,1,1,1,0,0,2,1,2,0,0,1,2,0,2,2,1]
]

def cert1209n : CertifiedBoard :=
  ⟨seed1209, by apply FastValid.valid; decide +kernel⟩

def cert1209r : CertifiedBoard :=
  ⟨seed1209.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1210 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,0,0,2,1,1,0,1,1,0,2],
  [2,0,2,1,0,0,1,2,1,0,2,0,0,2,0],
  [2,0,1,1,1,1,0,1,1,2,0,2,1,2,0,2,0],
  [0,2,2,0,1,2,2,0,1,0,0,2,2,1,2,0,0,1,0]
]

def cert1210n : CertifiedBoard :=
  ⟨seed1210, by apply FastValid.valid; decide +kernel⟩

def cert1210r : CertifiedBoard :=
  ⟨seed1210.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1211 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,0,0,2,1,1,1,1,0,1,1],
  [0,1,0,1,0,0,2,1,2,0,2,0,1,1,0],
  [0,2,0,0,1,2,0,2,2,0,2,2,1,2,1,0,2],
  [1,1,0,2,1,0,0,1,1,2,0,0,2,0,1,2,2,0,1]
]

def cert1211n : CertifiedBoard :=
  ⟨seed1211, by apply FastValid.valid; decide +kernel⟩

def cert1211r : CertifiedBoard :=
  ⟨seed1211.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1212 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,0,0,2,1,1,1,1,0,2,1],
  [1,1,0,1,0,2,0,1,2,0,1,1,0,1,0],
  [0,2,0,2,2,0,2,2,0,0,2,1,2,1,0,0,2],
  [2,1,2,0,0,1,2,0,2,0,1,1,2,2,1,0,0,1,1]
]

def cert1212n : CertifiedBoard :=
  ⟨seed1212, by apply FastValid.valid; decide +kernel⟩

def cert1212r : CertifiedBoard :=
  ⟨seed1212.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1213 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,0,0,2,1,1,1,1,0,2,1],
  [2,1,0,2,0,0,2,2,0,1,0,0,1,1,0],
  [1,2,0,2,2,1,0,0,2,0,1,1,0,1,2,0,2],
  [0,2,0,1,0,1,2,1,2,0,2,1,2,2,0,0,1,1,2]
]

def cert1213n : CertifiedBoard :=
  ⟨seed1213, by apply FastValid.valid; decide +kernel⟩

def cert1213r : CertifiedBoard :=
  ⟨seed1213.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1214 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,0,0,2,1,1,1,1,2,0,1],
  [0,1,1,0,1,0,2,2,0,1,2,2,1,0,0],
  [0,2,1,2,1,2,0,0,1,2,0,0,2,1,0,0,2],
  [0,0,1,1,0,1,0,2,2,0,2,0,2,0,2,0,1,1,0]
]

def cert1214n : CertifiedBoard :=
  ⟨seed1214, by apply FastValid.valid; decide +kernel⟩

def cert1214r : CertifiedBoard :=
  ⟨seed1214.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1215 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,0,0,2,1,1,1,1,2,0,2],
  [0,1,1,0,2,0,1,2,1,2,2,0,1,1,0],
  [0,2,1,0,0,2,2,0,1,1,0,2,0,2,0,0,1],
  [1,0,0,1,2,0,0,2,1,2,0,2,2,1,0,1,0,1,0]
]

def cert1215n : CertifiedBoard :=
  ⟨seed1215, by apply FastValid.valid; decide +kernel⟩

def cert1215r : CertifiedBoard :=
  ⟨seed1215.map List.reverse, by apply FastValid.valid; decide +kernel⟩

end TBoards.Extended
