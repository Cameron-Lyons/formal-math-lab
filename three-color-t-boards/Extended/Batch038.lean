import Extended.Batch034

/- Generated from extended_seeds.json. Published seeds 0–4:
   Qiyuan Ma, DOI 10.5281/zenodo.23631079, CC-BY-4.0. -/

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.Extended

def seed1216 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,0,0,2,1,1,1,2,0,1,1],
  [1,1,0,2,0,0,2,0,1,0,0,2,1,2,0],
  [2,0,2,0,2,1,2,0,2,2,0,1,0,1,1,1,0],
  [0,0,1,1,0,1,2,2,1,0,2,2,0,0,1,2,1,0,0]
]

def cert1216n : CertifiedBoard :=
  ⟨seed1216, by apply FastValid.valid; decide +kernel⟩

def cert1216r : CertifiedBoard :=
  ⟨seed1216.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1217 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,0,0,2,1,1,1,2,0,2,0],
  [1,1,0,0,2,0,1,2,1,2,2,1,0,1,0],
  [2,0,1,2,0,0,2,2,0,1,1,1,0,0,1,0,2],
  [0,2,2,0,0,1,1,0,2,1,2,0,2,0,2,1,0,1,1]
]

def cert1217n : CertifiedBoard :=
  ⟨seed1217, by apply FastValid.valid; decide +kernel⟩

def cert1217r : CertifiedBoard :=
  ⟨seed1217.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1218 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,0,0,2,1,1,1,2,0,2,2],
  [2,2,0,0,2,2,0,1,1,0,0,1,1,0,2],
  [0,1,1,1,0,0,2,0,1,2,1,0,2,0,1,0,1],
  [0,2,1,2,0,2,0,2,1,2,2,1,0,1,2,0,0,1,0]
]

def cert1218n : CertifiedBoard :=
  ⟨seed1218, by apply FastValid.valid; decide +kernel⟩

def cert1218r : CertifiedBoard :=
  ⟨seed1218.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1219 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,0,2,0,0,1,0,2,1,1,1],
  [1,1,0,1,0,0,2,0,0,0,2,2,0,2,1],
  [2,1,2,1,0,0,1,1,0,2,1,2,0,2,2,1,0],
  [1,0,1,1,2,2,0,1,2,0,2,0,1,2,0,1,1,1,0]
]

def cert1219n : CertifiedBoard :=
  ⟨seed1219, by apply FastValid.valid; decide +kernel⟩

def cert1219r : CertifiedBoard :=
  ⟨seed1219.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1220 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,0,2,0,0,1,1,1,0,1,1],
  [0,1,0,2,2,0,2,0,1,2,0,1,1,1,0],
  [1,1,0,0,2,2,1,2,0,0,0,2,1,2,2,0,2],
  [0,2,1,0,1,0,2,0,2,1,0,0,1,2,1,1,2,0,1]
]

def cert1220n : CertifiedBoard :=
  ⟨seed1220, by apply FastValid.valid; decide +kernel⟩

def cert1220r : CertifiedBoard :=
  ⟨seed1220.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1221 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,0,2,0,0,2,1,1,0,2,1],
  [2,1,0,2,1,0,1,0,0,1,0,0,1,1,1],
  [1,1,2,0,2,2,0,0,0,2,0,2,2,0,1,2,1],
  [2,1,2,2,1,2,0,1,1,0,1,2,0,2,0,1,1,1,0]
]

def cert1221n : CertifiedBoard :=
  ⟨seed1221, by apply FastValid.valid; decide +kernel⟩

def cert1221r : CertifiedBoard :=
  ⟨seed1221.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1222 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,0,2,0,1,1,1,1,2,0,1],
  [0,1,0,1,0,2,1,2,2,0,0,0,1,1,0],
  [0,2,1,2,0,2,2,1,0,2,2,0,0,1,2,1,0],
  [1,0,0,2,1,1,0,1,2,0,2,0,2,0,1,1,0,0,2]
]

def cert1222n : CertifiedBoard :=
  ⟨seed1222, by apply FastValid.valid; decide +kernel⟩

def cert1222r : CertifiedBoard :=
  ⟨seed1222.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1223 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,0,2,0,1,1,1,1,2,0,2],
  [1,1,0,0,2,2,1,2,2,0,0,0,1,1,0],
  [0,2,1,2,0,0,2,0,2,1,1,0,2,1,0,0,1],
  [0,1,0,1,0,2,0,2,2,0,1,2,0,1,2,1,0,1,1]
]

def cert1223n : CertifiedBoard :=
  ⟨seed1223, by apply FastValid.valid; decide +kernel⟩

def cert1223r : CertifiedBoard :=
  ⟨seed1223.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1224 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,0,2,0,1,1,1,2,0,2,0],
  [1,1,0,0,1,1,0,2,1,0,0,2,1,1,0],
  [1,2,2,0,2,0,0,0,2,1,2,0,0,1,2,1,2],
  [2,0,2,2,1,0,2,2,0,1,2,0,1,0,1,0,1,1,1]
]

def cert1224n : CertifiedBoard :=
  ⟨seed1224, by apply FastValid.valid; decide +kernel⟩

def cert1224r : CertifiedBoard :=
  ⟨seed1224.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1225 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,0,2,0,1,2,0,2,2,1,1],
  [2,0,0,1,0,0,2,1,0,1,1,1,2,2,0],
  [1,2,0,2,0,2,2,0,1,0,1,1,0,0,1,1,0],
  [1,1,1,0,2,1,0,2,0,0,0,2,1,2,0,1,2,1,2]
]

def cert1225n : CertifiedBoard :=
  ⟨seed1225, by apply FastValid.valid; decide +kernel⟩

def cert1225r : CertifiedBoard :=
  ⟨seed1225.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1226 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,0,2,0,1,2,1,1,1,0,1],
  [0,1,0,1,0,2,1,2,0,1,1,0,0,2,1],
  [0,0,1,2,0,2,2,1,0,2,1,2,2,0,2,0,0],
  [2,1,0,0,0,2,0,2,2,0,1,1,1,2,0,0,1,1,0]
]

def cert1226n : CertifiedBoard :=
  ⟨seed1226, by apply FastValid.valid; decide +kernel⟩

def cert1226r : CertifiedBoard :=
  ⟨seed1226.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1227 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,0,2,0,1,2,1,1,2,0,1],
  [0,2,1,2,0,2,2,0,2,1,2,0,2,0,0],
  [0,1,0,1,1,1,0,2,0,1,1,1,0,0,2,1,0],
  [0,0,1,0,1,2,2,0,0,1,1,0,0,0,2,2,1,0,2]
]

def cert1227n : CertifiedBoard :=
  ⟨seed1227, by apply FastValid.valid; decide +kernel⟩

def cert1227r : CertifiedBoard :=
  ⟨seed1227.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1228 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,0,2,0,1,2,2,1,1,1,0],
  [0,1,2,0,1,0,2,1,2,0,1,1,1,0,1],
  [0,2,0,0,2,2,0,2,0,2,1,2,1,0,0,1,0],
  [1,0,2,2,0,0,1,1,0,1,1,2,0,2,1,0,0,0,2]
]

def cert1228n : CertifiedBoard :=
  ⟨seed1228, by apply FastValid.valid; decide +kernel⟩

def cert1228r : CertifiedBoard :=
  ⟨seed1228.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1229 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,0,2,0,1,2,2,1,1,1,0],
  [1,1,1,0,0,2,0,1,1,2,0,2,1,2,0],
  [2,2,0,0,0,1,0,1,1,0,0,2,0,1,0,2,2],
  [2,0,2,2,0,2,1,0,1,2,1,0,2,1,2,0,0,1,1]
]

def cert1229n : CertifiedBoard :=
  ⟨seed1229, by apply FastValid.valid; decide +kernel⟩

def cert1229r : CertifiedBoard :=
  ⟨seed1229.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1230 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,0,2,0,1,2,2,1,1,1,2],
  [0,1,1,0,0,2,2,0,2,0,2,1,2,0,1],
  [1,2,0,0,0,1,0,2,1,2,0,0,1,0,1,1,0],
  [1,0,0,2,0,2,1,0,1,1,1,0,2,2,0,1,2,1,0]
]

def cert1230n : CertifiedBoard :=
  ⟨seed1230, by apply FastValid.valid; decide +kernel⟩

def cert1230r : CertifiedBoard :=
  ⟨seed1230.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1231 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,0,2,0,1,2,2,1,1,1,2],
  [0,1,1,0,0,2,2,0,2,0,2,1,2,0,1],
  [1,2,0,0,0,1,0,2,1,2,0,0,1,0,1,1,0],
  [1,0,0,2,0,2,2,0,1,1,1,0,2,1,0,1,2,1,0]
]

def cert1231n : CertifiedBoard :=
  ⟨seed1231, by apply FastValid.valid; decide +kernel⟩

def cert1231r : CertifiedBoard :=
  ⟨seed1231.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1232 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,0,2,0,2,0,1,2,0,2,1],
  [1,0,0,1,0,0,2,2,1,2,0,1,1,2,1],
  [2,1,0,2,1,2,0,1,1,1,0,2,0,0,0,1,0],
  [2,1,1,1,0,1,1,0,1,2,2,0,2,2,0,0,2,1,0]
]

def cert1232n : CertifiedBoard :=
  ⟨seed1232, by apply FastValid.valid; decide +kernel⟩

def cert1232r : CertifiedBoard :=
  ⟨seed1232.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1233 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,0,2,0,2,0,1,2,0,2,1],
  [1,2,0,2,0,0,1,1,0,1,1,1,0,1,0],
  [2,1,0,2,2,1,2,0,0,0,2,1,2,1,0,0,1],
  [0,1,1,0,0,2,2,0,1,0,2,1,1,1,2,2,0,1,2]
]

def cert1233n : CertifiedBoard :=
  ⟨seed1233, by apply FastValid.valid; decide +kernel⟩

def cert1233r : CertifiedBoard :=
  ⟨seed1233.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1234 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,0,2,0,2,1,0,2,2,1,1],
  [2,0,0,2,2,0,1,1,1,0,0,1,2,2,0],
  [1,1,2,0,0,2,0,1,2,0,1,0,1,0,1,1,0],
  [0,1,1,1,0,2,0,2,1,2,0,2,1,2,1,0,0,0,1]
]

def cert1234n : CertifiedBoard :=
  ⟨seed1234, by apply FastValid.valid; decide +kernel⟩

def cert1234r : CertifiedBoard :=
  ⟨seed1234.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1235 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,0,2,0,2,2,0,1,1,1,0],
  [0,1,2,0,2,2,1,0,2,0,1,1,1,0,1],
  [0,0,2,1,1,0,1,2,2,0,2,1,2,1,0,0,0],
  [0,0,1,1,2,0,1,0,0,2,1,2,0,0,1,0,2,0,0]
]

def cert1235n : CertifiedBoard :=
  ⟨seed1235, by apply FastValid.valid; decide +kernel⟩

def cert1235r : CertifiedBoard :=
  ⟨seed1235.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1236 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,0,2,1,0,1,0,2,2,1,1],
  [2,0,2,1,0,2,0,0,2,0,0,2,1,2,0],
  [1,1,0,1,2,1,2,0,2,0,1,0,0,1,1,1,0],
  [0,1,2,2,0,1,1,1,2,0,2,2,0,1,1,0,0,0,1]
]

def cert1236n : CertifiedBoard :=
  ⟨seed1236, by apply FastValid.valid; decide +kernel⟩

def cert1236r : CertifiedBoard :=
  ⟨seed1236.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1237 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,0,2,1,0,2,0,2,1,1,0],
  [1,2,1,0,1,0,1,0,2,0,1,1,0,0,1],
  [1,1,1,2,2,0,2,2,0,0,2,0,0,0,2,1,2],
  [0,1,2,0,1,2,0,2,2,1,2,0,1,1,0,0,1,1,1]
]

def cert1237n : CertifiedBoard :=
  ⟨seed1237, by apply FastValid.valid; decide +kernel⟩

def cert1237r : CertifiedBoard :=
  ⟨seed1237.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1238 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,0,2,1,2,0,0,1,1,1,0],
  [0,2,0,0,1,1,2,2,1,2,0,1,1,1,0],
  [1,0,2,0,2,2,0,2,1,1,0,2,1,0,0,0,2],
  [0,1,0,0,2,0,2,2,0,1,2,0,1,2,1,0,1,0,1]
]

def cert1238n : CertifiedBoard :=
  ⟨seed1238, by apply FastValid.valid; decide +kernel⟩

def cert1238r : CertifiedBoard :=
  ⟨seed1238.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1239 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,0,2,1,2,0,0,2,0,1,1],
  [1,1,0,1,0,2,1,0,1,1,0,2,0,1,0],
  [0,1,2,1,0,0,2,2,0,2,0,2,2,1,2,0,1],
  [0,0,1,1,2,2,0,0,1,2,0,2,1,1,1,1,0,0,0]
]

def cert1239n : CertifiedBoard :=
  ⟨seed1239, by apply FastValid.valid; decide +kernel⟩

def cert1239r : CertifiedBoard :=
  ⟨seed1239.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1240 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,0,2,1,2,0,0,2,0,1,2],
  [1,2,1,2,0,1,1,0,1,0,0,1,1,1,0],
  [1,2,2,1,0,2,0,2,0,0,0,2,2,0,1,0,1],
  [0,1,1,1,2,0,2,2,0,2,1,0,2,1,1,0,0,1,2]
]

def cert1240n : CertifiedBoard :=
  ⟨seed1240, by apply FastValid.valid; decide +kernel⟩

def cert1240r : CertifiedBoard :=
  ⟨seed1240.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1241 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,0,2,1,2,0,0,2,1,1,1],
  [1,2,2,0,2,2,1,0,1,0,2,2,0,1,0],
  [1,1,0,2,0,0,1,2,1,0,0,1,1,0,0,0,2],
  [0,2,0,2,0,2,1,2,0,1,2,0,1,1,1,0,1,1,2]
]

def cert1241n : CertifiedBoard :=
  ⟨seed1241, by apply FastValid.valid; decide +kernel⟩

def cert1241r : CertifiedBoard :=
  ⟨seed1241.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1242 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,0,2,1,2,0,2,2,1,1,0],
  [2,0,0,2,0,1,1,1,1,0,1,2,1,0,2],
  [0,2,1,0,0,2,2,0,1,1,0,1,0,2,0,0,1],
  [0,1,1,2,2,0,2,0,1,0,0,0,1,2,0,2,1,2,0]
]

def cert1242n : CertifiedBoard :=
  ⟨seed1242, by apply FastValid.valid; decide +kernel⟩

def cert1242r : CertifiedBoard :=
  ⟨seed1242.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1243 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,1,0,0,0,0,2,0,1,1,2],
  [1,2,2,0,2,1,0,0,2,2,1,2,0,2,1],
  [1,1,1,0,1,0,2,0,0,1,2,0,0,2,1,1,0],
  [2,1,2,1,0,1,2,0,2,0,1,1,1,0,2,2,0,1,1]
]

def cert1243n : CertifiedBoard :=
  ⟨seed1243, by apply FastValid.valid; decide +kernel⟩

def cert1243r : CertifiedBoard :=
  ⟨seed1243.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1244 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,1,0,0,0,0,2,0,2,1,1],
  [1,2,0,2,2,0,0,2,0,1,1,0,2,0,1],
  [1,1,1,0,2,2,1,0,0,2,1,2,2,0,1,1,0],
  [0,1,2,1,0,1,2,0,0,1,0,1,1,1,2,0,2,1,2]
]

def cert1244n : CertifiedBoard :=
  ⟨seed1244, by apply FastValid.valid; decide +kernel⟩

def cert1244r : CertifiedBoard :=
  ⟨seed1244.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1245 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,1,0,0,0,0,2,0,2,2,1],
  [2,0,2,1,2,2,0,0,2,0,1,0,2,1,0],
  [2,1,1,0,1,1,1,0,0,1,2,0,1,1,2,0,1],
  [0,1,1,1,0,2,1,2,1,0,1,2,0,2,0,0,2,2,0]
]

def cert1245n : CertifiedBoard :=
  ⟨seed1245, by apply FastValid.valid; decide +kernel⟩

def cert1245r : CertifiedBoard :=
  ⟨seed1245.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1246 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,1,0,0,0,0,2,1,1,1,0],
  [2,2,0,2,1,0,0,1,1,0,1,1,1,0,2],
  [0,2,2,1,0,2,0,0,2,1,2,0,1,2,1,2,0],
  [2,0,1,1,2,2,0,1,0,1,2,0,2,0,2,0,0,2,2]
]

def cert1246n : CertifiedBoard :=
  ⟨seed1246, by apply FastValid.valid; decide +kernel⟩

def cert1246r : CertifiedBoard :=
  ⟨seed1246.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1247 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,1,0,0,0,0,2,1,1,2,0],
  [1,2,1,0,1,1,0,0,2,0,1,2,2,1,2],
  [2,0,2,2,0,2,0,0,1,0,2,1,0,1,1,1,0],
  [0,1,2,0,2,0,0,2,2,0,1,1,1,0,2,1,2,0,1]
]

def cert1247n : CertifiedBoard :=
  ⟨seed1247, by apply FastValid.valid; decide +kernel⟩

def cert1247r : CertifiedBoard :=
  ⟨seed1247.map List.reverse, by apply FastValid.valid; decide +kernel⟩

end TBoards.Extended
