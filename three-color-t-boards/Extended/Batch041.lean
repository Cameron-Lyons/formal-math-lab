import Extended.Batch037

/- Generated from extended_seeds.json. Published seeds 0–4:
   Qiyuan Ma, DOI 10.5281/zenodo.23631079, CC-BY-4.0. -/

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.Extended

def seed1312 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,2,0,0,2,0,2,2,1,1,1],
  [1,1,1,0,2,1,2,0,2,0,1,2,0,1,0],
  [0,1,2,1,0,0,0,0,1,0,2,1,2,0,2,1,0],
  [1,0,1,1,2,2,0,0,2,2,0,1,1,0,1,1,0,0,1]
]

def cert1312n : CertifiedBoard :=
  ⟨seed1312, by apply FastValid.valid; decide +kernel⟩

def cert1312r : CertifiedBoard :=
  ⟨seed1312.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1313 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,2,0,0,2,1,0,1,2,0,1],
  [2,1,2,0,0,1,0,1,1,0,0,0,0,1,0],
  [1,1,2,2,1,0,2,1,2,0,2,0,2,2,0,1,1],
  [0,1,1,1,1,0,0,2,2,0,2,1,1,0,2,0,1,2,1]
]

def cert1313n : CertifiedBoard :=
  ⟨seed1313, by apply FastValid.valid; decide +kernel⟩

def cert1313r : CertifiedBoard :=
  ⟨seed1313.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1314 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,2,0,0,2,1,2,0,2,2,1],
  [2,1,0,0,2,0,2,1,1,1,0,1,1,2,1],
  [0,0,0,0,1,0,2,0,1,2,2,0,1,1,0,1,0],
  [2,1,0,2,2,0,1,1,1,0,0,1,2,0,2,1,2,0,0]
]

def cert1314n : CertifiedBoard :=
  ⟨seed1314, by apply FastValid.valid; decide +kernel⟩

def cert1314r : CertifiedBoard :=
  ⟨seed1314.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1315 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,2,0,0,2,2,0,1,1,1,0],
  [1,2,0,2,2,1,2,0,2,0,1,1,1,0,1],
  [2,1,0,1,0,2,1,2,0,0,0,1,0,0,0,2,1],
  [0,1,2,2,0,1,1,2,1,1,0,2,0,2,1,0,0,1,2]
]

def cert1315n : CertifiedBoard :=
  ⟨seed1315, by apply FastValid.valid; decide +kernel⟩

def cert1315r : CertifiedBoard :=
  ⟨seed1315.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1316 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,2,0,0,2,2,0,2,1,1,0],
  [1,2,0,2,0,1,0,0,0,1,1,1,1,0,1],
  [1,2,2,1,0,2,1,2,0,0,2,1,0,0,0,1,2],
  [0,1,0,1,2,1,2,0,1,1,0,2,0,2,2,0,1,1,2]
]

def cert1316n : CertifiedBoard :=
  ⟨seed1316, by apply FastValid.valid; decide +kernel⟩

def cert1316r : CertifiedBoard :=
  ⟨seed1316.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1317 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,2,0,1,0,1,1,2,0,2,2],
  [0,0,2,0,2,1,0,0,2,1,0,2,1,1,1],
  [1,1,0,2,0,1,1,0,0,1,2,2,0,1,2,0,0],
  [2,2,0,2,2,1,2,1,2,0,0,0,0,1,1,1,0,1,0]
]

def cert1317n : CertifiedBoard :=
  ⟨seed1317, by apply FastValid.valid; decide +kernel⟩

def cert1317r : CertifiedBoard :=
  ⟨seed1317.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1318 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,2,0,1,0,2,1,1,2,0,2],
  [2,0,0,2,2,1,2,0,1,1,1,0,1,1,0],
  [0,2,1,0,0,0,1,1,1,0,0,0,2,1,2,2,0],
  [2,0,2,0,2,0,0,1,2,1,0,1,0,2,2,0,1,2,0]
]

def cert1318n : CertifiedBoard :=
  ⟨seed1318, by apply FastValid.valid; decide +kernel⟩

def cert1318r : CertifiedBoard :=
  ⟨seed1318.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1319 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,2,0,1,1,1,1,0,2,1,1],
  [2,0,2,0,2,0,0,0,2,1,0,0,1,2,0],
  [0,1,2,0,2,2,1,0,1,0,1,0,2,1,2,0,1],
  [1,1,0,0,0,1,1,2,1,2,2,0,0,2,2,0,1,1,0]
]

def cert1319n : CertifiedBoard :=
  ⟨seed1319, by apply FastValid.valid; decide +kernel⟩

def cert1319r : CertifiedBoard :=
  ⟨seed1319.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1320 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,2,0,1,1,1,1,0,2,2,1],
  [2,1,0,0,2,1,2,1,2,2,0,0,1,1,0],
  [0,0,0,2,0,1,2,0,1,2,0,2,1,0,0,0,1],
  [0,1,0,1,1,2,0,2,0,2,1,1,0,1,0,2,2,0,0]
]

def cert1320n : CertifiedBoard :=
  ⟨seed1320, by apply FastValid.valid; decide +kernel⟩

def cert1320r : CertifiedBoard :=
  ⟨seed1320.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1321 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,2,0,1,1,1,1,2,0,1,1],
  [2,1,0,0,2,1,2,2,0,0,2,2,0,2,1],
  [0,0,0,0,1,1,0,0,1,2,0,2,0,2,1,1,0],
  [1,1,0,2,0,1,2,1,0,1,0,1,0,2,2,1,2,0,0]
]

def cert1321n : CertifiedBoard :=
  ⟨seed1321, by apply FastValid.valid; decide +kernel⟩

def cert1321r : CertifiedBoard :=
  ⟨seed1321.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1322 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,2,0,1,1,1,1,2,0,2,2],
  [2,2,0,2,2,1,2,1,0,0,2,0,0,0,1],
  [0,1,1,0,2,1,1,0,1,0,1,0,2,1,0,0,0],
  [0,0,2,1,2,0,1,2,2,0,2,0,0,1,2,0,1,1,0]
]

def cert1322n : CertifiedBoard :=
  ⟨seed1322, by apply FastValid.valid; decide +kernel⟩

def cert1322r : CertifiedBoard :=
  ⟨seed1322.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1323 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,2,0,1,1,2,0,1,1,1,0],
  [1,1,0,0,2,2,0,0,0,0,1,0,0,2,2],
  [2,0,2,1,2,0,2,0,2,0,1,1,1,0,2,1,1],
  [2,2,1,0,1,2,0,0,1,0,2,1,2,1,0,1,2,2,0]
]

def cert1323n : CertifiedBoard :=
  ⟨seed1323, by apply FastValid.valid; decide +kernel⟩

def cert1323r : CertifiedBoard :=
  ⟨seed1323.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1324 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,2,0,1,1,2,0,2,1,1,0],
  [1,2,1,2,0,1,0,0,0,0,1,1,1,0,1],
  [0,1,2,0,2,0,2,1,0,0,2,1,2,2,0,0,2],
  [0,2,0,0,1,1,1,0,1,0,2,2,1,0,2,2,0,1,2]
]

def cert1324n : CertifiedBoard :=
  ⟨seed1324, by apply FastValid.valid; decide +kernel⟩

def cert1324r : CertifiedBoard :=
  ⟨seed1324.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1325 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,2,0,1,1,2,0,2,1,1,0],
  [2,1,0,0,2,2,0,0,0,0,1,1,1,0,1],
  [1,2,0,2,0,2,0,1,0,2,1,0,0,2,1,2,1],
  [0,1,0,1,1,1,0,2,2,0,0,1,2,0,1,2,2,1,2]
]

def cert1325n : CertifiedBoard :=
  ⟨seed1325, by apply FastValid.valid; decide +kernel⟩

def cert1325r : CertifiedBoard :=
  ⟨seed1325.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1326 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,2,0,1,1,2,2,1,1,1,0],
  [0,1,2,0,0,1,1,1,0,2,1,0,0,0,2],
  [0,2,1,2,0,2,2,0,0,2,0,2,1,0,1,0,1],
  [1,0,2,0,2,2,0,1,1,0,0,0,1,2,1,2,0,1,0]
]

def cert1326n : CertifiedBoard :=
  ⟨seed1326, by apply FastValid.valid; decide +kernel⟩

def cert1326r : CertifiedBoard :=
  ⟨seed1326.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1327 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,2,0,1,2,0,2,2,1,1,2],
  [1,2,1,2,0,1,1,1,0,1,1,1,0,0,0],
  [0,0,0,1,0,2,1,2,2,0,0,2,1,0,0,2,0],
  [2,0,2,2,0,0,1,2,0,2,0,1,0,1,1,0,2,1,0]
]

def cert1327n : CertifiedBoard :=
  ⟨seed1327, by apply FastValid.valid; decide +kernel⟩

def cert1327r : CertifiedBoard :=
  ⟨seed1327.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1328 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,2,0,2,1,1,1,1,2,0,1],
  [0,1,2,0,0,0,1,2,2,0,1,1,0,0,2],
  [2,1,0,0,1,1,0,1,0,2,2,0,0,0,2,2,1],
  [0,2,1,0,2,1,2,1,2,0,2,0,2,0,1,0,1,1,0]
]

def cert1328n : CertifiedBoard :=
  ⟨seed1328, by apply FastValid.valid; decide +kernel⟩

def cert1328r : CertifiedBoard :=
  ⟨seed1328.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1329 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,2,0,2,1,1,1,2,0,2,1],
  [2,1,2,0,0,1,0,1,2,0,0,0,2,0,1],
  [0,1,2,2,1,0,0,0,1,1,0,2,2,0,1,1,0],
  [2,0,1,0,2,2,0,2,1,2,1,0,1,1,1,0,0,2,0]
]

def cert1329n : CertifiedBoard :=
  ⟨seed1329, by apply FastValid.valid; decide +kernel⟩

def cert1329r : CertifiedBoard :=
  ⟨seed1329.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1330 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,2,1,0,0,0,0,1,1,2,0],
  [2,0,2,1,0,1,0,0,1,0,1,2,2,1,2],
  [1,1,0,2,0,0,2,0,2,2,0,0,2,1,1,1,1],
  [1,2,1,2,0,1,1,0,2,0,2,2,0,1,2,0,1,1,0]
]

def cert1330n : CertifiedBoard :=
  ⟨seed1330, by apply FastValid.valid; decide +kernel⟩

def cert1330r : CertifiedBoard :=
  ⟨seed1330.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1331 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,2,1,0,0,0,2,1,1,1,2],
  [1,2,2,0,1,2,1,0,0,2,2,0,0,0,1],
  [2,1,2,0,1,1,0,1,1,0,2,0,2,0,0,1,0],
  [0,1,1,1,0,1,2,0,2,0,1,0,2,2,1,2,0,2,1]
]

def cert1331n : CertifiedBoard :=
  ⟨seed1331, by apply FastValid.valid; decide +kernel⟩

def cert1331r : CertifiedBoard :=
  ⟨seed1331.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1332 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,2,1,0,0,0,2,2,1,1,0],
  [0,1,1,0,2,0,2,2,0,1,1,1,1,0,1],
  [0,2,1,2,1,0,2,0,2,1,2,2,0,0,0,1,0],
  [1,0,0,1,2,0,1,0,1,1,2,0,1,2,0,0,2,0,2]
]

def cert1332n : CertifiedBoard :=
  ⟨seed1332, by apply FastValid.valid; decide +kernel⟩

def cert1332r : CertifiedBoard :=
  ⟨seed1332.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1333 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,2,1,0,0,1,0,1,1,0,2],
  [1,2,0,1,1,1,1,0,0,0,1,1,0,1,2],
  [0,2,0,2,2,0,1,2,2,0,2,0,0,2,1,2,0],
  [2,0,0,0,2,2,1,2,1,1,2,0,1,0,2,0,2,1,0]
]

def cert1333n : CertifiedBoard :=
  ⟨seed1333, by apply FastValid.valid; decide +kernel⟩

def cert1333r : CertifiedBoard :=
  ⟨seed1333.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1334 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,2,1,0,0,1,0,1,1,2,0],
  [2,0,0,2,1,1,1,0,0,0,1,2,0,2,2],
  [0,1,2,0,2,1,2,2,0,1,0,2,0,1,1,1,0],
  [2,2,0,2,0,0,0,2,2,1,2,1,0,2,0,1,1,0,1]
]

def cert1334n : CertifiedBoard :=
  ⟨seed1334, by apply FastValid.valid; decide +kernel⟩

def cert1334r : CertifiedBoard :=
  ⟨seed1334.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1335 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,2,1,0,0,1,0,2,1,1,1],
  [1,1,1,0,2,0,0,1,1,0,0,0,0,2,0],
  [2,0,1,2,1,2,0,2,1,2,2,0,0,2,2,1,0],
  [0,1,2,0,2,2,0,2,0,1,1,0,1,0,1,1,2,0,1]
]

def cert1335n : CertifiedBoard :=
  ⟨seed1335, by apply FastValid.valid; decide +kernel⟩

def cert1335r : CertifiedBoard :=
  ⟨seed1335.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1336 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,2,1,0,0,1,1,2,0,2,0],
  [1,2,0,1,1,1,1,0,2,0,2,2,0,1,0],
  [0,1,0,2,0,1,2,2,0,2,1,0,1,2,0,0,1],
  [2,0,0,2,2,1,2,1,1,0,1,1,0,0,0,0,2,1,2]
]

def cert1336n : CertifiedBoard :=
  ⟨seed1336, by apply FastValid.valid; decide +kernel⟩

def cert1336r : CertifiedBoard :=
  ⟨seed1336.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1337 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,2,1,0,0,1,2,0,2,2,1],
  [2,1,2,0,1,2,1,0,0,0,0,2,1,1,0],
  [0,1,1,1,0,1,1,2,0,0,1,0,2,0,2,0,2],
  [0,2,2,0,0,2,0,1,0,2,1,2,2,0,1,1,1,0,1]
]

def cert1337n : CertifiedBoard :=
  ⟨seed1337, by apply FastValid.valid; decide +kernel⟩

def cert1337r : CertifiedBoard :=
  ⟨seed1337.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1338 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,2,1,0,0,1,2,0,2,2,1],
  [2,1,2,0,2,0,2,0,0,0,0,1,1,1,0],
  [2,1,1,1,0,2,1,0,1,1,0,0,2,0,0,2,1],
  [1,1,2,0,1,0,1,2,1,2,2,0,1,0,2,2,0,1,1]
]

def cert1338n : CertifiedBoard :=
  ⟨seed1338, by apply FastValid.valid; decide +kernel⟩

def cert1338r : CertifiedBoard :=
  ⟨seed1338.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1339 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,2,1,2,1,1,0,1,1,1,0],
  [1,2,2,0,1,2,0,2,0,0,1,0,0,2,1],
  [2,1,0,2,0,0,0,0,2,1,2,0,1,0,0,1,2],
  [1,2,0,2,2,1,0,2,0,2,2,0,1,1,1,0,1,1,2]
]

def cert1339n : CertifiedBoard :=
  ⟨seed1339, by apply FastValid.valid; decide +kernel⟩

def cert1339r : CertifiedBoard :=
  ⟨seed1339.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1340 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,2,1,2,1,1,0,1,1,2,0],
  [0,1,0,0,2,2,0,1,2,2,0,1,1,0,1],
  [2,0,2,0,1,0,2,1,0,0,1,2,0,0,2,1,0],
  [2,0,2,2,1,2,0,0,0,0,1,1,1,1,0,2,0,2,0]
]

def cert1340n : CertifiedBoard :=
  ⟨seed1340, by apply FastValid.valid; decide +kernel⟩

def cert1340r : CertifiedBoard :=
  ⟨seed1340.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1341 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,2,1,2,1,1,0,1,1,2,0],
  [2,0,2,0,2,0,0,0,2,0,1,1,1,0,2],
  [0,1,2,0,1,1,1,0,0,2,2,0,1,2,0,0,1],
  [0,2,2,0,2,1,0,0,0,1,0,2,1,2,2,1,0,1,0]
]

def cert1341n : CertifiedBoard :=
  ⟨seed1341, by apply FastValid.valid; decide +kernel⟩

def cert1341r : CertifiedBoard :=
  ⟨seed1341.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1342 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,2,1,2,1,1,1,0,2,0,2],
  [0,0,2,2,0,1,2,0,1,1,0,0,1,0,1],
  [0,2,0,1,1,2,0,2,1,2,0,0,2,1,0,1,0],
  [0,1,1,1,0,0,0,0,1,2,2,1,0,2,2,0,2,0,0]
]

def cert1342n : CertifiedBoard :=
  ⟨seed1342, by apply FastValid.valid; decide +kernel⟩

def cert1342r : CertifiedBoard :=
  ⟨seed1342.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1343 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,2,1,2,1,1,1,1,0,1,2],
  [1,2,2,0,0,0,2,2,0,1,0,0,1,1,2],
  [0,1,2,0,1,0,0,2,0,2,1,0,2,0,0,0,1],
  [1,2,0,2,1,2,0,2,2,1,0,2,0,1,1,0,1,1,0]
]

def cert1343n : CertifiedBoard :=
  ⟨seed1343, by apply FastValid.valid; decide +kernel⟩

def cert1343r : CertifiedBoard :=
  ⟨seed1343.map List.reverse, by apply FastValid.valid; decide +kernel⟩

end TBoards.Extended
