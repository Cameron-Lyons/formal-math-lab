import Extended.Batch036

/- Generated from extended_seeds.json. Published seeds 0–4:
   Qiyuan Ma, DOI 10.5281/zenodo.23631079, CC-BY-4.0. -/

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.Extended

def seed1280 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,1,2,0,1,2,1,1,2,0,2],
  [0,0,0,2,0,0,0,1,1,1,1,0,1,1,0],
  [0,1,0,2,2,1,2,0,2,1,2,2,0,0,2,0,1],
  [0,2,1,0,0,2,0,2,2,0,1,0,2,1,0,1,1,0,0]
]

def cert1280n : CertifiedBoard :=
  ⟨seed1280, by apply FastValid.valid; decide +kernel⟩

def cert1280r : CertifiedBoard :=
  ⟨seed1280.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1281 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,1,2,0,1,2,2,1,1,1,2],
  [1,2,1,2,0,2,0,1,0,1,1,1,0,0,0],
  [0,0,2,1,2,0,0,2,2,0,2,0,0,0,1,1,0],
  [0,0,2,0,1,1,0,1,0,2,2,0,2,1,0,2,1,0,0]
]

def cert1281n : CertifiedBoard :=
  ⟨seed1281, by apply FastValid.valid; decide +kernel⟩

def cert1281r : CertifiedBoard :=
  ⟨seed1281.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1282 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,1,2,0,2,0,0,2,2,1,1],
  [2,1,2,0,0,0,0,1,1,0,1,2,0,1,0],
  [1,1,1,1,0,0,2,0,2,1,0,2,0,2,2,0,1],
  [0,1,1,0,0,2,1,0,1,1,2,2,0,1,0,2,1,2,1]
]

def cert1282n : CertifiedBoard :=
  ⟨seed1282, by apply FastValid.valid; decide +kernel⟩

def cert1282r : CertifiedBoard :=
  ⟨seed1282.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1283 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,1,2,0,2,0,1,1,2,0,2],
  [2,1,0,0,1,1,1,0,1,1,1,0,2,2,1],
  [2,0,1,0,1,0,0,0,2,1,2,2,0,0,0,2,0],
  [0,2,2,0,0,2,1,2,0,1,2,1,1,0,2,0,2,1,0]
]

def cert1283n : CertifiedBoard :=
  ⟨seed1283, by apply FastValid.valid; decide +kernel⟩

def cert1283r : CertifiedBoard :=
  ⟨seed1283.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1284 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,1,2,1,0,1,0,2,1,1,0],
  [0,2,1,2,0,0,0,0,2,0,1,1,1,0,1],
  [0,1,1,2,0,1,0,2,2,0,2,1,2,2,0,0,2],
  [0,2,0,1,1,1,0,0,1,2,0,2,0,2,2,1,0,0,2]
]

def cert1284n : CertifiedBoard :=
  ⟨seed1284, by apply FastValid.valid; decide +kernel⟩

def cert1284r : CertifiedBoard :=
  ⟨seed1284.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1285 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,1,2,1,0,1,0,2,2,1,1],
  [2,0,1,1,0,0,0,2,2,0,2,0,1,1,0],
  [1,1,2,0,0,0,1,0,1,2,0,0,2,1,2,2,0],
  [0,2,0,2,1,0,0,2,1,2,0,2,0,1,1,1,1,0,2]
]

def cert1285n : CertifiedBoard :=
  ⟨seed1285, by apply FastValid.valid; decide +kernel⟩

def cert1285r : CertifiedBoard :=
  ⟨seed1285.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1286 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,1,2,1,0,1,1,1,0,2,0],
  [2,0,1,0,2,1,1,0,1,0,0,0,1,1,0],
  [1,2,0,2,0,1,2,0,2,2,0,0,2,1,2,2,0],
  [2,0,0,2,0,1,1,1,2,0,2,1,0,0,0,2,2,1,2]
]

def cert1286n : CertifiedBoard :=
  ⟨seed1286, by apply FastValid.valid; decide +kernel⟩

def cert1286r : CertifiedBoard :=
  ⟨seed1286.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1287 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,1,2,1,0,1,1,2,0,2,0],
  [2,1,2,0,0,0,2,1,2,0,0,0,2,1,0],
  [2,0,1,0,2,0,2,1,1,1,1,0,0,1,1,0,2],
  [0,2,2,0,1,1,0,1,2,2,0,2,0,1,0,0,2,2,1]
]

def cert1287n : CertifiedBoard :=
  ⟨seed1287, by apply FastValid.valid; decide +kernel⟩

def cert1287r : CertifiedBoard :=
  ⟨seed1287.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1288 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,1,2,1,0,2,1,1,1,2,0],
  [2,0,2,0,0,2,1,2,0,1,1,1,0,1,0],
  [0,0,0,2,2,0,1,2,2,1,2,0,1,0,0,0,1],
  [0,1,1,0,1,1,0,2,0,2,0,0,2,2,0,2,1,0,0]
]

def cert1288n : CertifiedBoard :=
  ⟨seed1288, by apply FastValid.valid; decide +kernel⟩

def cert1288r : CertifiedBoard :=
  ⟨seed1288.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1289 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,1,2,1,0,2,1,1,1,2,0],
  [2,0,2,1,2,2,1,2,0,2,0,0,0,2,0],
  [0,0,0,1,1,0,1,2,0,1,1,0,1,0,2,1,0],
  [2,0,2,2,0,1,0,0,2,0,1,1,1,0,0,2,2,0,0]
]

def cert1289n : CertifiedBoard :=
  ⟨seed1289, by apply FastValid.valid; decide +kernel⟩

def cert1289r : CertifiedBoard :=
  ⟨seed1289.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1290 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,1,2,1,2,0,0,0,2,1,1],
  [1,1,0,1,1,1,2,2,1,2,0,2,0,1,0],
  [0,0,0,2,0,2,1,0,1,2,0,1,0,2,2,0,0],
  [0,2,1,0,2,2,0,2,0,1,1,1,0,0,1,1,0,0,2]
]

def cert1290n : CertifiedBoard :=
  ⟨seed1290, by apply FastValid.valid; decide +kernel⟩

def cert1290r : CertifiedBoard :=
  ⟨seed1290.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1291 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,1,2,1,2,0,0,0,2,1,1],
  [1,1,0,1,1,1,2,2,1,2,0,2,0,1,0],
  [0,0,0,2,0,2,1,0,1,2,0,1,0,2,2,0,0],
  [2,1,0,0,2,2,0,2,0,1,1,1,0,0,1,1,0,2,1]
]

def cert1291n : CertifiedBoard :=
  ⟨seed1291, by apply FastValid.valid; decide +kernel⟩

def cert1291r : CertifiedBoard :=
  ⟨seed1291.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1292 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,1,2,1,2,0,0,2,1,1,1],
  [0,0,0,2,0,1,2,2,1,2,0,2,1,0,0],
  [2,1,0,1,1,0,0,2,0,1,0,1,0,2,0,2,1],
  [1,1,2,0,1,1,1,0,2,2,0,2,2,0,0,0,1,1,0]
]

def cert1292n : CertifiedBoard :=
  ⟨seed1292, by apply FastValid.valid; decide +kernel⟩

def cert1292r : CertifiedBoard :=
  ⟨seed1292.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1293 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,1,2,1,2,0,0,2,1,1,1],
  [1,1,1,0,0,0,0,2,0,2,0,2,0,2,1],
  [0,1,1,0,0,2,1,0,2,2,0,1,0,2,2,1,0],
  [2,1,2,2,0,0,1,2,0,1,1,2,0,1,1,0,1,0,1]
]

def cert1293n : CertifiedBoard :=
  ⟨seed1293, by apply FastValid.valid; decide +kernel⟩

def cert1293r : CertifiedBoard :=
  ⟨seed1293.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1294 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,1,2,1,2,0,0,2,1,1,2],
  [2,0,2,0,0,0,0,2,0,1,0,1,1,1,0],
  [0,1,1,0,2,1,0,2,2,1,2,0,2,1,0,0,1],
  [1,2,0,1,0,1,2,2,0,2,2,0,1,1,1,0,0,2,0]
]

def cert1294n : CertifiedBoard :=
  ⟨seed1294, by apply FastValid.valid; decide +kernel⟩

def cert1294r : CertifiedBoard :=
  ⟨seed1294.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1295 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,1,2,1,2,0,2,0,2,1,1],
  [2,0,1,0,1,0,1,1,0,0,0,1,1,1,0],
  [2,2,1,2,2,0,0,2,1,0,2,1,0,0,0,2,0],
  [1,1,1,2,0,1,2,0,0,2,0,2,2,0,1,1,0,2,2]
]

def cert1295n : CertifiedBoard :=
  ⟨seed1295, by apply FastValid.valid; decide +kernel⟩

def cert1295r : CertifiedBoard :=
  ⟨seed1295.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1296 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,1,2,1,2,0,2,0,2,1,1],
  [2,0,1,0,1,0,1,1,0,0,0,1,1,1,0],
  [2,2,1,2,2,0,0,2,1,0,2,1,0,0,0,2,0],
  [1,1,1,2,0,1,2,0,2,2,0,0,2,0,1,1,0,2,2]
]

def cert1296n : CertifiedBoard :=
  ⟨seed1296, by apply FastValid.valid; decide +kernel⟩

def cert1296r : CertifiedBoard :=
  ⟨seed1296.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1297 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,1,2,1,2,0,2,1,1,1,2],
  [0,0,0,2,0,1,1,1,0,0,2,1,0,0,0],
  [1,2,0,2,2,1,2,2,0,0,1,0,1,0,2,1,0],
  [0,0,2,2,0,1,2,0,2,0,1,1,0,1,1,0,2,0,0]
]

def cert1297n : CertifiedBoard :=
  ⟨seed1297, by apply FastValid.valid; decide +kernel⟩

def cert1297r : CertifiedBoard :=
  ⟨seed1297.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1298 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,1,2,1,2,0,2,2,1,1,2],
  [1,2,0,0,1,1,1,1,0,0,2,0,1,0,1],
  [2,0,0,0,2,1,0,0,0,2,2,0,1,1,0,2,0],
  [0,1,2,0,2,0,2,1,0,1,0,2,1,2,2,0,1,1,0]
]

def cert1298n : CertifiedBoard :=
  ⟨seed1298, by apply FastValid.valid; decide +kernel⟩

def cert1298r : CertifiedBoard :=
  ⟨seed1298.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1299 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,1,2,2,0,1,0,2,1,1,1],
  [1,0,0,1,1,1,2,0,2,0,0,0,2,1,0],
  [0,0,0,2,1,2,0,0,2,2,1,2,0,1,2,1,0],
  [1,1,0,1,0,1,1,0,2,0,2,0,2,2,0,1,1,0,0]
]

def cert1299n : CertifiedBoard :=
  ⟨seed1299, by apply FastValid.valid; decide +kernel⟩

def cert1299r : CertifiedBoard :=
  ⟨seed1299.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1300 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,1,2,2,0,1,1,0,2,2,1],
  [0,1,0,2,0,0,2,0,0,0,2,1,1,1,1],
  [2,1,0,0,1,1,0,0,0,2,2,0,2,1,2,0,1],
  [1,1,2,1,2,0,2,0,1,0,1,2,0,2,1,0,1,1,0]
]

def cert1300n : CertifiedBoard :=
  ⟨seed1300, by apply FastValid.valid; decide +kernel⟩

def cert1300r : CertifiedBoard :=
  ⟨seed1300.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1301 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,1,2,2,0,2,1,1,1,2,0],
  [0,1,0,1,0,0,2,2,0,1,1,1,0,2,2],
  [2,0,0,2,0,1,1,0,1,2,0,2,0,0,1,1,0],
  [2,2,1,0,2,1,2,1,0,0,0,0,2,0,2,1,2,0,1]
]

def cert1301n : CertifiedBoard :=
  ⟨seed1301, by apply FastValid.valid; decide +kernel⟩

def cert1301r : CertifiedBoard :=
  ⟨seed1301.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1302 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,1,2,2,0,2,1,1,1,2,0],
  [2,0,1,0,0,0,2,1,0,1,1,1,0,2,1],
  [0,1,1,0,0,2,0,1,2,0,0,2,0,2,2,1,0],
  [2,1,2,1,2,0,2,2,0,0,0,1,1,0,2,0,1,0,1]
]

def cert1302n : CertifiedBoard :=
  ⟨seed1302, by apply FastValid.valid; decide +kernel⟩

def cert1302r : CertifiedBoard :=
  ⟨seed1302.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1303 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,2,0,0,0,0,2,1,1,1,0],
  [1,1,1,0,2,2,0,2,0,0,1,1,0,0,2],
  [2,2,0,2,1,0,1,2,0,2,1,2,1,0,0,1,1],
  [0,2,0,1,1,2,0,1,0,2,2,1,2,0,1,0,1,2,2]
]

def cert1303n : CertifiedBoard :=
  ⟨seed1303, by apply FastValid.valid; decide +kernel⟩

def cert1303r : CertifiedBoard :=
  ⟨seed1303.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1304 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,2,0,0,0,0,2,1,1,1,2],
  [0,2,1,0,2,0,0,1,0,1,2,1,2,0,2],
  [1,2,0,1,1,0,2,2,0,2,0,1,1,1,0,0,1],
  [0,1,0,1,1,0,0,2,2,1,2,0,1,2,2,0,2,1,0]
]

def cert1304n : CertifiedBoard :=
  ⟨seed1304, by apply FastValid.valid; decide +kernel⟩

def cert1304r : CertifiedBoard :=
  ⟨seed1304.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1305 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,2,0,0,0,0,2,2,1,1,1],
  [1,1,0,0,1,2,0,2,2,0,2,0,2,1,0],
  [2,1,2,1,0,1,0,2,0,1,1,0,1,1,2,0,0],
  [0,0,1,2,0,1,0,0,2,1,2,2,0,1,1,1,0,2,1]
]

def cert1305n : CertifiedBoard :=
  ⟨seed1305, by apply FastValid.valid; decide +kernel⟩

def cert1305r : CertifiedBoard :=
  ⟨seed1305.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1306 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,2,0,0,0,0,2,2,1,1,2],
  [1,2,0,0,2,1,0,2,2,0,1,2,2,0,2],
  [0,1,0,1,0,1,1,1,0,2,0,1,1,1,0,0,1],
  [0,2,0,2,1,2,0,1,2,1,2,0,2,1,0,0,1,1,0]
]

def cert1306n : CertifiedBoard :=
  ⟨seed1306, by apply FastValid.valid; decide +kernel⟩

def cert1306r : CertifiedBoard :=
  ⟨seed1306.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1307 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,2,0,0,0,0,2,2,1,1,2],
  [1,2,0,0,2,1,0,2,2,0,1,2,2,0,2],
  [0,1,0,1,0,1,1,1,0,2,0,1,1,1,0,0,1],
  [0,2,1,2,0,2,0,1,2,1,2,0,2,1,0,0,1,1,0]
]

def cert1307n : CertifiedBoard :=
  ⟨seed1307, by apply FastValid.valid; decide +kernel⟩

def cert1307r : CertifiedBoard :=
  ⟨seed1307.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1308 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,2,0,0,0,1,0,2,1,1,1],
  [1,0,0,2,2,1,0,1,1,0,2,0,2,1,0],
  [1,2,0,2,0,2,2,0,1,2,2,0,1,0,1,1,0],
  [1,1,1,0,0,0,1,1,2,0,1,2,0,0,2,1,2,1,2]
]

def cert1308n : CertifiedBoard :=
  ⟨seed1308, by apply FastValid.valid; decide +kernel⟩

def cert1308r : CertifiedBoard :=
  ⟨seed1308.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1309 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,2,0,0,0,1,1,1,2,0,1],
  [2,0,2,2,0,2,0,0,2,1,2,2,1,2,0],
  [0,1,1,0,2,1,0,1,0,1,2,1,1,0,0,0,1],
  [0,1,1,1,0,2,2,0,1,0,0,2,0,1,2,0,2,1,0]
]

def cert1309n : CertifiedBoard :=
  ⟨seed1309, by apply FastValid.valid; decide +kernel⟩

def cert1309r : CertifiedBoard :=
  ⟨seed1309.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1310 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,2,0,0,2,0,2,1,1,1,0],
  [0,1,1,0,0,0,2,2,1,0,1,2,1,0,1],
  [2,1,2,2,0,2,0,1,2,0,1,0,0,1,0,2,1],
  [1,1,2,0,2,2,0,1,1,0,2,1,2,0,0,0,1,1,1]
]

def cert1310n : CertifiedBoard :=
  ⟨seed1310, by apply FastValid.valid; decide +kernel⟩

def cert1310r : CertifiedBoard :=
  ⟨seed1310.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1311 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,2,0,0,2,0,2,1,1,1,2],
  [0,0,0,2,2,1,0,2,2,0,1,1,0,0,0],
  [1,1,0,1,0,1,2,1,2,0,2,1,2,0,0,1,1],
  [1,2,2,0,1,2,0,1,1,1,0,0,1,0,2,0,2,1,0]
]

def cert1311n : CertifiedBoard :=
  ⟨seed1311, by apply FastValid.valid; decide +kernel⟩

def cert1311r : CertifiedBoard :=
  ⟨seed1311.map List.reverse, by apply FastValid.valid; decide +kernel⟩

end TBoards.Extended
