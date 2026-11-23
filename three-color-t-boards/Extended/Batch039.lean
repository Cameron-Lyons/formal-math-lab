import Extended.Batch035

/- Generated from extended_seeds.json. Published seeds 0–4:
   Qiyuan Ma, DOI 10.5281/zenodo.23631079, CC-BY-4.0. -/

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.Extended

def seed1248 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,1,0,0,0,0,2,1,1,2,0],
  [2,0,0,2,2,0,0,1,1,0,1,2,2,1,0],
  [1,1,0,1,0,2,2,0,1,1,0,2,0,1,2,1,2],
  [1,2,0,2,1,0,0,2,0,2,1,2,0,2,0,1,1,1,1]
]

def cert1248n : CertifiedBoard :=
  ⟨seed1248, by apply FastValid.valid; decide +kernel⟩

def cert1248r : CertifiedBoard :=
  ⟨seed1248.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1249 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,1,0,0,0,0,2,1,1,2,0],
  [2,0,0,2,2,0,0,1,1,0,1,2,2,1,0],
  [1,1,0,1,0,2,2,0,1,1,0,2,0,1,2,1,2],
  [1,2,0,2,1,2,0,2,0,2,1,0,0,2,0,1,1,1,1]
]

def cert1249n : CertifiedBoard :=
  ⟨seed1249, by apply FastValid.valid; decide +kernel⟩

def cert1249r : CertifiedBoard :=
  ⟨seed1249.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1250 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,1,0,0,0,0,2,2,1,1,1],
  [1,2,0,2,1,0,0,2,2,0,2,1,2,2,0],
  [1,1,1,0,2,0,0,1,1,2,0,0,2,0,1,1,0],
  [2,0,1,2,1,0,1,0,1,1,0,2,0,1,2,0,2,1,2]
]

def cert1250n : CertifiedBoard :=
  ⟨seed1250, by apply FastValid.valid; decide +kernel⟩

def cert1250r : CertifiedBoard :=
  ⟨seed1250.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1251 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,1,0,0,0,0,2,2,1,1,1],
  [1,2,0,2,1,0,0,2,2,0,2,1,2,2,0],
  [1,1,1,0,2,0,0,1,1,2,0,0,2,0,1,1,0],
  [2,0,1,2,1,0,2,0,1,1,0,1,0,1,2,0,2,1,2]
]

def cert1251n : CertifiedBoard :=
  ⟨seed1251, by apply FastValid.valid; decide +kernel⟩

def cert1251r : CertifiedBoard :=
  ⟨seed1251.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1252 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,1,0,0,0,2,0,2,1,1,1],
  [1,1,0,2,1,2,0,2,2,1,0,1,2,1,0],
  [0,0,2,1,2,0,0,0,1,1,2,2,0,1,2,0,0],
  [1,0,0,2,2,0,1,1,0,1,1,1,0,2,0,2,0,1,0]
]

def cert1252n : CertifiedBoard :=
  ⟨seed1252, by apply FastValid.valid; decide +kernel⟩

def cert1252r : CertifiedBoard :=
  ⟨seed1252.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1253 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,1,0,0,0,2,0,2,2,1,1],
  [2,0,0,2,0,2,1,0,0,0,1,1,1,1,0],
  [0,2,1,2,0,1,1,2,0,1,0,1,2,1,2,2,0],
  [1,1,0,1,1,0,2,1,0,2,2,0,0,2,0,1,2,0,2]
]

def cert1253n : CertifiedBoard :=
  ⟨seed1253, by apply FastValid.valid; decide +kernel⟩

def cert1253r : CertifiedBoard :=
  ⟨seed1253.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1254 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,1,0,0,0,2,1,1,1,2,0],
  [2,0,2,1,2,1,0,2,2,1,2,0,1,1,0],
  [0,0,0,2,2,0,1,2,0,2,1,0,1,1,1,0,0],
  [2,0,0,1,0,2,0,1,1,0,1,2,2,0,0,2,0,2,0]
]

def cert1254n : CertifiedBoard :=
  ⟨seed1254, by apply FastValid.valid; decide +kernel⟩

def cert1254r : CertifiedBoard :=
  ⟨seed1254.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1255 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,1,0,0,0,2,1,1,1,2,0],
  [2,0,2,1,2,1,0,2,2,1,2,0,1,2,0],
  [0,0,0,2,1,0,1,1,0,2,2,0,1,1,1,0,0],
  [2,0,2,0,1,1,0,1,2,2,0,2,0,0,2,0,0,1,0]
]

def cert1255n : CertifiedBoard :=
  ⟨seed1255, by apply FastValid.valid; decide +kernel⟩

def cert1255r : CertifiedBoard :=
  ⟨seed1255.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1256 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,1,0,0,0,2,1,1,1,2,0],
  [2,1,2,0,1,1,0,0,2,2,0,2,0,2,2],
  [2,2,1,0,1,1,1,0,1,0,2,0,0,0,1,1,0],
  [2,0,1,2,2,0,1,2,1,2,0,2,1,0,2,0,0,2,1]
]

def cert1256n : CertifiedBoard :=
  ⟨seed1256, by apply FastValid.valid; decide +kernel⟩

def cert1256r : CertifiedBoard :=
  ⟨seed1256.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1257 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,1,0,0,0,2,1,1,2,0,1],
  [1,2,0,2,1,2,0,0,2,2,0,0,0,1,2],
  [2,1,0,1,1,1,1,0,2,0,2,0,1,0,0,2,1],
  [0,1,2,2,0,2,0,1,1,0,2,2,1,2,1,0,1,1,0]
]

def cert1257n : CertifiedBoard :=
  ⟨seed1257, by apply FastValid.valid; decide +kernel⟩

def cert1257r : CertifiedBoard :=
  ⟨seed1257.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1258 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,1,0,0,0,2,1,1,2,0,2],
  [2,1,2,0,0,2,1,0,1,2,0,0,0,2,1],
  [1,1,1,0,2,0,2,0,2,2,0,1,0,0,1,1,1],
  [0,2,0,1,1,0,1,1,0,2,2,1,2,2,0,1,2,1,0]
]

def cert1258n : CertifiedBoard :=
  ⟨seed1258, by apply FastValid.valid; decide +kernel⟩

def cert1258r : CertifiedBoard :=
  ⟨seed1258.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1259 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,1,0,0,2,0,1,1,1,2,0],
  [1,2,0,1,1,1,0,1,2,0,2,1,0,2,0],
  [2,0,0,0,1,2,2,0,0,0,2,1,1,0,2,1,2],
  [2,0,1,0,0,2,0,2,2,0,2,2,1,2,1,0,1,1,0]
]

def cert1259n : CertifiedBoard :=
  ⟨seed1259, by apply FastValid.valid; decide +kernel⟩

def cert1259r : CertifiedBoard :=
  ⟨seed1259.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1260 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,1,0,0,2,0,2,1,1,0,1],
  [0,1,1,0,0,0,1,0,2,2,1,2,0,2,1],
  [1,0,2,0,0,2,1,2,2,0,2,2,0,1,1,1,0],
  [2,1,0,1,2,0,1,1,1,2,0,0,0,2,0,1,2,1,0]
]

def cert1260n : CertifiedBoard :=
  ⟨seed1260, by apply FastValid.valid; decide +kernel⟩

def cert1260r : CertifiedBoard :=
  ⟨seed1260.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1261 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,1,0,0,2,0,2,2,1,1,1],
  [1,1,1,0,2,1,2,0,1,0,1,2,2,0,1],
  [0,1,2,0,0,2,1,2,0,2,0,0,0,0,2,1,0],
  [1,0,1,1,0,0,1,1,0,2,0,2,2,0,1,1,2,1,0]
]

def cert1261n : CertifiedBoard :=
  ⟨seed1261, by apply FastValid.valid; decide +kernel⟩

def cert1261r : CertifiedBoard :=
  ⟨seed1261.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1262 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,1,0,0,2,1,2,0,1,1,0],
  [1,2,1,2,0,1,0,0,0,0,2,2,0,0,2],
  [1,2,2,1,0,1,1,1,0,2,1,0,2,0,0,1,2],
  [0,2,1,1,1,0,1,2,0,2,0,2,0,2,2,0,1,1,2]
]

def cert1262n : CertifiedBoard :=
  ⟨seed1262, by apply FastValid.valid; decide +kernel⟩

def cert1262r : CertifiedBoard :=
  ⟨seed1262.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1263 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,1,0,0,2,2,0,1,1,1,2],
  [1,2,2,0,2,1,0,0,2,1,2,0,1,1,0],
  [0,2,0,2,0,0,0,0,2,2,1,0,1,1,1,0,1],
  [0,1,0,2,1,1,0,2,0,1,2,0,0,1,2,1,2,0,2]
]

def cert1263n : CertifiedBoard :=
  ⟨seed1263, by apply FastValid.valid; decide +kernel⟩

def cert1263r : CertifiedBoard :=
  ⟨seed1263.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1264 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,1,1,0,0,0,0,2,0,2,1],
  [1,1,1,0,0,2,0,0,2,0,2,2,0,1,0],
  [2,1,2,2,0,1,0,2,1,0,1,1,1,0,2,1,2],
  [1,2,0,1,1,2,0,2,2,1,0,1,2,0,0,1,2,1,1]
]

def cert1264n : CertifiedBoard :=
  ⟨seed1264, by apply FastValid.valid; decide +kernel⟩

def cert1264r : CertifiedBoard :=
  ⟨seed1264.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1265 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,1,1,0,0,0,2,2,1,1,0],
  [0,1,0,0,1,2,0,1,1,0,1,2,1,0,1],
  [2,1,2,2,0,0,0,2,2,0,2,1,2,0,0,2,1],
  [0,1,1,1,1,2,0,2,0,2,1,0,2,0,1,0,2,0,1]
]

def cert1265n : CertifiedBoard :=
  ⟨seed1265, by apply FastValid.valid; decide +kernel⟩

def cert1265r : CertifiedBoard :=
  ⟨seed1265.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1266 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,1,1,0,0,2,0,1,1,1,0],
  [0,0,2,2,0,1,0,1,0,2,1,2,1,0,0],
  [0,2,0,2,2,1,2,0,1,2,0,2,1,1,1,0,2],
  [2,1,0,1,1,2,0,2,0,0,0,0,1,2,2,0,0,2,1]
]

def cert1266n : CertifiedBoard :=
  ⟨seed1266, by apply FastValid.valid; decide +kernel⟩

def cert1266r : CertifiedBoard :=
  ⟨seed1266.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1267 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,1,1,1,0,2,0,2,1,1,1],
  [0,0,2,2,0,1,2,1,0,1,1,2,0,0,0],
  [1,1,0,0,0,2,0,2,2,0,2,1,2,0,0,2,1],
  [2,1,0,0,1,0,2,0,1,1,0,1,2,2,1,2,0,1,0]
]

def cert1267n : CertifiedBoard :=
  ⟨seed1267, by apply FastValid.valid; decide +kernel⟩

def cert1267r : CertifiedBoard :=
  ⟨seed1267.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1268 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,1,1,1,0,2,1,1,1,2,0],
  [0,1,2,0,0,2,0,0,2,1,2,0,2,0,2],
  [0,2,1,0,1,0,1,1,0,2,2,0,2,0,1,1,0],
  [2,0,1,2,1,2,2,0,1,0,0,0,2,2,1,0,0,0,1]
]

def cert1268n : CertifiedBoard :=
  ⟨seed1268, by apply FastValid.valid; decide +kernel⟩

def cert1268r : CertifiedBoard :=
  ⟨seed1268.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1269 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,1,1,1,0,2,1,1,1,2,0],
  [2,0,1,1,0,0,0,2,2,1,2,1,0,1,0],
  [0,2,1,2,0,2,1,0,0,2,2,0,1,0,2,0,0],
  [0,0,2,0,0,0,1,2,2,0,1,1,0,1,2,0,2,0,2]
]

def cert1269n : CertifiedBoard :=
  ⟨seed1269, by apply FastValid.valid; decide +kernel⟩

def cert1269r : CertifiedBoard :=
  ⟨seed1269.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1270 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,1,1,1,0,2,1,1,1,2,0],
  [2,1,2,0,0,2,0,0,2,1,0,0,0,2,1],
  [2,0,1,0,1,0,2,2,0,2,0,1,1,0,1,2,0],
  [2,0,2,0,2,2,0,1,1,0,0,0,1,2,1,2,2,1,0]
]

def cert1270n : CertifiedBoard :=
  ⟨seed1270, by apply FastValid.valid; decide +kernel⟩

def cert1270r : CertifiedBoard :=
  ⟨seed1270.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1271 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,1,2,0,0,0,0,2,0,1,1],
  [1,2,2,0,1,0,1,0,0,2,2,1,0,0,2],
  [1,1,1,1,2,0,1,1,0,2,0,2,2,0,0,1,2],
  [0,2,0,2,1,0,2,1,2,1,2,0,2,1,1,0,1,1,0]
]

def cert1271n : CertifiedBoard :=
  ⟨seed1271, by apply FastValid.valid; decide +kernel⟩

def cert1271r : CertifiedBoard :=
  ⟨seed1271.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1272 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,1,2,0,0,0,0,2,1,1,0],
  [1,0,0,1,1,0,1,0,0,2,2,1,2,2,0],
  [2,0,2,1,2,1,0,2,1,0,1,2,0,1,1,2,0],
  [2,0,2,0,1,0,2,0,2,2,0,0,2,0,1,1,1,1,0]
]

def cert1272n : CertifiedBoard :=
  ⟨seed1272, by apply FastValid.valid; decide +kernel⟩

def cert1272r : CertifiedBoard :=
  ⟨seed1272.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1273 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,1,2,0,0,0,0,2,2,1,1],
  [2,1,0,0,2,0,2,2,0,0,1,1,1,1,0],
  [1,1,2,1,2,0,1,0,2,0,2,0,1,0,0,2,1],
  [2,2,0,2,1,2,0,1,1,0,1,1,0,2,1,0,1,2,2]
]

def cert1273n : CertifiedBoard :=
  ⟨seed1273, by apply FastValid.valid; decide +kernel⟩

def cert1273r : CertifiedBoard :=
  ⟨seed1273.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1274 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,1,2,0,0,0,2,0,2,2,1],
  [2,1,0,2,1,2,0,0,1,1,0,1,1,1,0],
  [0,1,2,1,0,1,1,2,0,2,0,2,2,0,1,0,0],
  [0,0,2,1,1,1,0,0,0,2,0,1,0,2,1,2,2,0,1]
]

def cert1274n : CertifiedBoard :=
  ⟨seed1274, by apply FastValid.valid; decide +kernel⟩

def cert1274r : CertifiedBoard :=
  ⟨seed1274.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1275 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,1,2,0,0,0,2,1,1,2,0],
  [0,2,0,1,1,0,1,0,2,0,1,1,1,0,1],
  [2,0,0,2,1,2,2,0,2,2,1,2,1,0,0,1,0],
  [0,1,2,0,2,0,1,1,1,0,2,2,0,2,1,0,0,0,2]
]

def cert1275n : CertifiedBoard :=
  ⟨seed1275, by apply FastValid.valid; decide +kernel⟩

def cert1275r : CertifiedBoard :=
  ⟨seed1275.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1276 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,1,2,0,0,2,0,1,1,2,0],
  [2,0,2,0,1,0,1,1,0,2,1,2,2,1,2],
  [0,2,0,0,0,2,1,0,0,0,1,2,1,1,1,1,0],
  [1,2,0,2,2,0,2,1,0,1,0,0,2,2,0,1,1,0,2]
]

def cert1276n : CertifiedBoard :=
  ⟨seed1276, by apply FastValid.valid; decide +kernel⟩

def cert1276r : CertifiedBoard :=
  ⟨seed1276.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1277 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,1,2,0,0,2,0,1,1,2,0],
  [2,2,0,1,1,1,1,0,1,2,0,1,0,1,0],
  [0,2,2,1,2,1,0,0,0,1,1,0,0,2,0,2,2],
  [2,0,2,1,1,0,2,1,0,2,1,2,2,0,0,0,2,0,2]
]

def cert1277n : CertifiedBoard :=
  ⟨seed1277, by apply FastValid.valid; decide +kernel⟩

def cert1277r : CertifiedBoard :=
  ⟨seed1277.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1278 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,1,2,0,0,2,0,2,1,1,0],
  [0,1,0,2,0,1,2,0,0,0,2,2,0,2,1],
  [2,1,2,2,0,1,1,1,1,0,1,0,2,0,1,1,0],
  [1,0,1,1,2,0,2,1,2,1,0,0,2,2,1,0,0,0,1]
]

def cert1278n : CertifiedBoard :=
  ⟨seed1278, by apply FastValid.valid; decide +kernel⟩

def cert1278r : CertifiedBoard :=
  ⟨seed1278.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1279 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,1,2,0,1,1,1,1,0,1,2],
  [1,2,2,0,2,0,2,0,0,2,1,0,1,1,2],
  [0,0,0,2,1,0,2,1,1,0,2,2,0,1,0,0,0],
  [1,2,0,0,2,0,2,2,1,2,1,2,0,1,1,0,0,1,0]
]

def cert1279n : CertifiedBoard :=
  ⟨seed1279, by apply FastValid.valid; decide +kernel⟩

def cert1279r : CertifiedBoard :=
  ⟨seed1279.map List.reverse, by apply FastValid.valid; decide +kernel⟩

end TBoards.Extended
