import Extended.Batch038

/- Generated from extended_seeds.json. Published seeds 0–4:
   Qiyuan Ma, DOI 10.5281/zenodo.23631079, CC-BY-4.0. -/

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.Extended

def seed1344 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,2,1,2,1,1,1,1,0,2,0],
  [0,1,2,0,0,1,1,2,2,0,2,0,2,1,0],
  [1,0,0,0,0,2,0,0,2,2,1,2,0,1,1,0,1],
  [2,0,1,0,2,2,0,1,1,0,1,2,0,2,1,0,0,1,0]
]

def cert1344n : CertifiedBoard :=
  ⟨seed1344, by apply FastValid.valid; decide +kernel⟩

def cert1344r : CertifiedBoard :=
  ⟨seed1344.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1345 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,2,1,2,1,1,1,1,0,2,0],
  [1,1,0,2,2,1,0,1,0,0,0,2,0,1,1],
  [2,0,2,0,0,1,2,2,0,1,0,0,2,1,2,0,0],
  [0,0,0,1,1,0,1,1,2,0,1,2,0,2,2,0,2,1,0]
]

def cert1345n : CertifiedBoard :=
  ⟨seed1345, by apply FastValid.valid; decide +kernel⟩

def cert1345r : CertifiedBoard :=
  ⟨seed1345.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1346 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,2,1,2,1,1,1,1,0,2,0],
  [1,2,2,0,2,2,0,2,0,1,1,0,2,1,0],
  [0,0,0,1,2,0,1,1,0,1,0,0,2,2,1,0,0],
  [2,0,0,2,0,0,0,1,2,0,1,0,1,1,2,0,2,1,2]
]

def cert1346n : CertifiedBoard :=
  ⟨seed1346, by apply FastValid.valid; decide +kernel⟩

def cert1346r : CertifiedBoard :=
  ⟨seed1346.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1347 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,2,1,2,1,1,1,1,0,2,2],
  [0,1,1,0,2,0,2,1,0,0,2,0,0,0,1],
  [0,2,2,0,1,0,1,1,2,0,2,0,2,1,0,1,0],
  [2,2,0,1,2,0,0,1,2,2,1,2,0,1,1,0,0,0,2]
]

def cert1347n : CertifiedBoard :=
  ⟨seed1347, by apply FastValid.valid; decide +kernel⟩

def cert1347r : CertifiedBoard :=
  ⟨seed1347.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1348 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,2,1,2,1,1,1,1,2,0,1],
  [0,1,1,0,2,1,0,1,2,0,1,0,2,2,0],
  [0,1,0,0,0,1,2,2,0,0,0,2,0,2,2,1,0],
  [2,0,0,2,1,2,0,2,0,2,0,1,1,0,0,1,1,0,1]
]

def cert1348n : CertifiedBoard :=
  ⟨seed1348, by apply FastValid.valid; decide +kernel⟩

def cert1348r : CertifiedBoard :=
  ⟨seed1348.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1349 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,2,1,2,1,1,1,1,2,0,1],
  [0,1,1,0,2,2,0,2,0,0,0,2,0,1,0],
  [1,0,1,2,0,0,0,1,1,0,0,2,2,1,2,2,0],
  [2,0,2,0,1,2,0,2,1,0,0,1,0,1,1,0,2,1,0]
]

def cert1349n : CertifiedBoard :=
  ⟨seed1349, by apply FastValid.valid; decide +kernel⟩

def cert1349r : CertifiedBoard :=
  ⟨seed1349.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1350 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,2,1,2,1,1,1,1,2,0,1],
  [0,1,2,0,0,1,0,1,1,0,0,2,1,2,0],
  [1,0,0,0,0,2,2,0,2,0,2,0,1,2,2,1,0],
  [2,0,0,1,1,0,1,1,0,2,2,0,2,1,0,2,0,1,0]
]

def cert1350n : CertifiedBoard :=
  ⟨seed1350, by apply FastValid.valid; decide +kernel⟩

def cert1350r : CertifiedBoard :=
  ⟨seed1350.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1351 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,2,1,2,1,1,1,1,2,0,2],
  [0,1,2,0,0,0,0,1,1,0,0,2,2,0,1],
  [0,2,1,0,1,1,0,2,2,0,0,1,0,2,1,2,0],
  [2,0,2,0,2,0,1,0,1,1,0,0,2,0,1,2,2,1,0]
]

def cert1351n : CertifiedBoard :=
  ⟨seed1351, by apply FastValid.valid; decide +kernel⟩

def cert1351r : CertifiedBoard :=
  ⟨seed1351.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1352 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,2,1,2,1,1,1,1,2,0,2],
  [0,1,2,0,0,0,2,0,1,1,0,0,1,1,0],
  [2,0,1,0,2,1,0,2,1,2,2,0,2,0,0,0,1],
  [0,2,2,0,2,2,1,0,1,2,0,1,1,0,1,0,0,2,0]
]

def cert1352n : CertifiedBoard :=
  ⟨seed1352, by apply FastValid.valid; decide +kernel⟩

def cert1352r : CertifiedBoard :=
  ⟨seed1352.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1353 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,2,1,2,2,1,0,1,1,1,2],
  [1,2,1,2,0,2,0,1,2,0,1,0,0,2,0],
  [2,0,0,1,2,0,0,0,1,1,0,0,0,2,1,1,0],
  [1,0,2,2,0,2,1,0,1,1,1,0,2,0,2,2,0,1,0]
]

def cert1353n : CertifiedBoard :=
  ⟨seed1353, by apply FastValid.valid; decide +kernel⟩

def cert1353r : CertifiedBoard :=
  ⟨seed1353.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1354 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,2,1,2,2,1,0,2,1,1,0],
  [0,1,1,0,1,1,1,1,2,1,2,0,0,0,1],
  [2,0,1,2,0,2,0,1,0,0,0,2,0,0,2,2,0],
  [2,0,2,0,2,2,0,1,1,0,2,1,0,1,0,0,1,2,0]
]

def cert1354n : CertifiedBoard :=
  ⟨seed1354, by apply FastValid.valid; decide +kernel⟩

def cert1354r : CertifiedBoard :=
  ⟨seed1354.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1355 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,2,1,2,2,1,0,2,1,1,0],
  [0,2,0,0,1,1,1,1,2,1,2,0,1,0,0],
  [2,2,0,1,0,1,2,0,0,0,0,2,0,1,1,0,2],
  [0,0,1,2,0,2,2,0,2,0,2,1,0,1,1,0,0,2,2]
]

def cert1355n : CertifiedBoard :=
  ⟨seed1355, by apply FastValid.valid; decide +kernel⟩

def cert1355r : CertifiedBoard :=
  ⟨seed1355.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1356 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,2,1,2,2,1,0,2,1,1,0],
  [1,1,1,0,0,0,0,1,2,1,0,1,1,0,2],
  [2,0,0,2,0,0,2,2,0,2,2,0,1,0,0,1,1],
  [0,2,0,2,0,2,1,2,0,1,1,1,2,0,1,0,1,2,0]
]

def cert1356n : CertifiedBoard :=
  ⟨seed1356, by apply FastValid.valid; decide +kernel⟩

def cert1356r : CertifiedBoard :=
  ⟨seed1356.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1357 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,2,1,2,2,1,0,2,1,1,0],
  [2,0,1,1,0,1,1,1,2,0,1,1,1,0,2],
  [0,0,0,1,2,1,0,0,0,2,2,0,2,0,0,2,0],
  [0,2,0,2,2,0,1,0,1,0,0,1,2,0,2,1,2,0,0]
]

def cert1357n : CertifiedBoard :=
  ⟨seed1357, by apply FastValid.valid; decide +kernel⟩

def cert1357r : CertifiedBoard :=
  ⟨seed1357.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1358 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,0,2,1,2,2,1,0,2,1,1,1],
  [1,1,1,0,0,0,0,1,2,0,2,2,0,1,0],
  [1,1,0,0,2,2,0,0,1,1,0,2,0,2,0,0,2],
  [0,2,0,2,1,2,0,1,0,1,2,1,0,1,1,2,0,1,1]
]

def cert1358n : CertifiedBoard :=
  ⟨seed1358, by apply FastValid.valid; decide +kernel⟩

def cert1358r : CertifiedBoard :=
  ⟨seed1358.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1359 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,1,1,0,0,0,0,2,0,2,1,1],
  [0,1,0,2,0,2,0,1,1,0,0,2,2,0,1],
  [2,1,2,0,0,1,0,2,1,2,1,0,1,2,0,2,1],
  [1,1,1,1,0,0,1,2,0,1,1,2,2,0,0,2,2,1,0]
]

def cert1359n : CertifiedBoard :=
  ⟨seed1359, by apply FastValid.valid; decide +kernel⟩

def cert1359r : CertifiedBoard :=
  ⟨seed1359.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1360 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,1,1,0,0,0,0,2,1,1,1,0],
  [0,2,1,2,1,0,1,0,0,1,2,0,1,2,0],
  [2,0,0,1,1,2,2,0,0,2,1,2,0,1,0,2,2],
  [2,2,1,0,2,0,2,0,2,0,2,2,0,1,1,1,0,0,2]
]

def cert1360n : CertifiedBoard :=
  ⟨seed1360, by apply FastValid.valid; decide +kernel⟩

def cert1360r : CertifiedBoard :=
  ⟨seed1360.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1361 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,1,1,0,0,0,0,2,1,1,1,2],
  [1,2,2,0,2,1,0,2,0,1,2,1,2,0,1],
  [0,2,0,2,0,0,1,1,0,0,1,2,0,0,2,1,0],
  [0,1,0,2,2,1,2,0,1,0,1,1,1,0,0,2,2,0,2]
]

def cert1361n : CertifiedBoard :=
  ⟨seed1361, by apply FastValid.valid; decide +kernel⟩

def cert1361r : CertifiedBoard :=
  ⟨seed1361.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1362 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,1,1,0,0,0,0,2,1,1,1,2],
  [2,0,0,1,1,1,0,2,0,1,2,2,0,2,0],
  [0,0,2,2,0,1,2,1,0,2,1,2,0,1,1,0,0],
  [1,2,0,2,2,1,2,0,2,0,0,1,0,0,2,1,0,1,0]
]

def cert1362n : CertifiedBoard :=
  ⟨seed1362, by apply FastValid.valid; decide +kernel⟩

def cert1362r : CertifiedBoard :=
  ⟨seed1362.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1363 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,1,1,0,0,0,0,2,2,1,1,0],
  [1,2,2,0,2,1,2,0,0,2,0,1,2,1,0],
  [0,1,1,2,0,2,1,0,0,1,0,2,0,1,2,0,1],
  [1,0,2,0,0,1,1,1,1,0,1,0,0,2,2,0,2,1,2]
]

def cert1363n : CertifiedBoard :=
  ⟨seed1363, by apply FastValid.valid; decide +kernel⟩

def cert1363r : CertifiedBoard :=
  ⟨seed1363.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1364 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,1,1,0,0,0,0,2,2,1,1,0],
  [2,1,0,2,1,2,0,0,1,1,2,0,2,0,2],
  [2,0,1,0,1,2,0,2,0,1,1,1,1,0,0,2,0],
  [0,2,1,2,2,0,0,1,0,2,2,0,1,2,1,0,0,2,1]
]

def cert1364n : CertifiedBoard :=
  ⟨seed1364, by apply FastValid.valid; decide +kernel⟩

def cert1364r : CertifiedBoard :=
  ⟨seed1364.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1365 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,1,1,0,0,0,0,2,2,1,1,1],
  [0,1,2,0,1,1,0,0,1,0,2,1,2,1,0],
  [2,2,0,2,0,2,0,0,2,2,0,1,2,0,1,0,1],
  [1,1,2,0,0,2,0,2,1,0,0,1,1,1,0,2,1,2,2]
]

def cert1365n : CertifiedBoard :=
  ⟨seed1365, by apply FastValid.valid; decide +kernel⟩

def cert1365r : CertifiedBoard :=
  ⟨seed1365.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1366 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,1,1,0,0,0,0,2,2,1,1,1],
  [2,0,0,2,0,1,0,2,0,0,2,0,2,1,0],
  [1,1,2,0,2,1,2,2,0,1,1,0,0,1,2,0,1],
  [0,1,1,1,0,0,1,2,0,2,1,2,1,0,1,0,2,2,0]
]

def cert1366n : CertifiedBoard :=
  ⟨seed1366, by apply FastValid.valid; decide +kernel⟩

def cert1366r : CertifiedBoard :=
  ⟨seed1366.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1367 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,1,1,0,0,0,0,2,2,1,1,2],
  [0,2,0,1,2,1,0,2,0,0,1,2,2,0,2],
  [0,1,0,0,1,1,1,1,0,2,2,0,2,0,1,1,0],
  [1,2,0,0,2,1,2,0,1,0,0,2,1,2,0,2,1,0,1]
]

def cert1367n : CertifiedBoard :=
  ⟨seed1367, by apply FastValid.valid; decide +kernel⟩

def cert1367r : CertifiedBoard :=
  ⟨seed1367.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1368 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,1,1,0,0,0,1,0,0,0,2,0],
  [1,2,1,2,2,0,0,2,0,1,0,2,2,1,0],
  [2,1,0,2,1,1,0,1,1,2,0,0,1,2,0,2,1],
  [2,0,2,0,2,1,2,0,1,1,1,1,0,0,2,2,0,1,2]
]

def cert1368n : CertifiedBoard :=
  ⟨seed1368, by apply FastValid.valid; decide +kernel⟩

def cert1368r : CertifiedBoard :=
  ⟨seed1368.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1369 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,1,1,0,0,0,1,0,0,0,2,1],
  [2,1,0,1,1,1,0,2,1,2,0,2,0,2,0],
  [1,2,0,0,1,2,2,0,1,2,0,1,0,2,2,1,0],
  [2,0,2,0,0,2,1,1,0,0,2,2,0,1,1,1,2,1,2]
]

def cert1369n : CertifiedBoard :=
  ⟨seed1369, by apply FastValid.valid; decide +kernel⟩

def cert1369r : CertifiedBoard :=
  ⟨seed1369.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1370 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,1,1,0,0,0,1,0,0,2,1,1],
  [1,2,2,0,2,1,0,2,1,0,0,1,2,1,2],
  [0,2,0,2,0,2,2,0,0,0,2,0,1,1,1,1,0],
  [1,1,0,2,2,1,2,0,1,0,1,1,2,0,1,2,0,0,2]
]

def cert1370n : CertifiedBoard :=
  ⟨seed1370, by apply FastValid.valid; decide +kernel⟩

def cert1370r : CertifiedBoard :=
  ⟨seed1370.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1371 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,1,1,0,0,0,1,0,2,2,1,1],
  [2,0,2,1,2,1,0,0,2,0,2,0,2,1,0],
  [1,1,0,1,2,0,1,1,0,2,1,2,0,0,0,2,0],
  [0,1,2,2,0,0,2,2,0,1,1,1,1,2,0,1,0,0,1]
]

def cert1371n : CertifiedBoard :=
  ⟨seed1371, by apply FastValid.valid; decide +kernel⟩

def cert1371r : CertifiedBoard :=
  ⟨seed1371.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1372 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,1,1,0,0,0,1,1,0,2,0,1],
  [2,1,2,0,0,2,2,0,1,2,0,0,0,1,0],
  [0,1,2,1,1,0,0,2,1,2,2,1,0,2,0,2,1],
  [2,0,2,0,2,1,0,1,1,1,1,2,0,1,0,0,2,2,0]
]

def cert1372n : CertifiedBoard :=
  ⟨seed1372, by apply FastValid.valid; decide +kernel⟩

def cert1372r : CertifiedBoard :=
  ⟨seed1372.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1373 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,1,1,0,0,0,1,1,2,0,2,0],
  [2,0,2,1,2,1,2,0,0,2,0,1,0,0,2],
  [0,2,1,0,2,1,1,1,1,0,2,2,0,0,1,1,0],
  [0,2,2,1,0,1,2,2,0,1,0,0,0,2,0,1,2,0,2]
]

def cert1373n : CertifiedBoard :=
  ⟨seed1373, by apply FastValid.valid; decide +kernel⟩

def cert1373r : CertifiedBoard :=
  ⟨seed1373.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1374 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,1,1,0,0,0,1,1,2,0,2,2],
  [1,2,0,2,1,0,0,2,0,2,0,1,1,1,0],
  [2,0,0,2,1,1,1,0,2,0,0,0,1,2,1,2,0],
  [2,2,1,0,1,2,2,0,1,0,2,2,0,1,0,0,2,1,2]
]

def cert1374n : CertifiedBoard :=
  ⟨seed1374, by apply FastValid.valid; decide +kernel⟩

def cert1374r : CertifiedBoard :=
  ⟨seed1374.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1375 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,1,1,0,0,0,2,1,1,0,0,1],
  [0,1,0,1,2,1,0,0,1,2,0,0,2,1,0],
  [2,1,2,2,0,2,2,0,1,1,1,2,0,0,0,2,2],
  [2,2,1,2,0,1,0,2,0,2,0,1,1,1,0,2,0,2,1]
]

def cert1375n : CertifiedBoard :=
  ⟨seed1375, by apply FastValid.valid; decide +kernel⟩

def cert1375r : CertifiedBoard :=
  ⟨seed1375.map List.reverse, by apply FastValid.valid; decide +kernel⟩

end TBoards.Extended
