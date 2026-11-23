import Extended.Batch040

/- Generated from extended_seeds.json. Published seeds 0–4:
   Qiyuan Ma, DOI 10.5281/zenodo.23631079, CC-BY-4.0. -/

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.Extended

def seed1408 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,1,1,1,0,0,1,1,1,0,2,2],
  [2,0,0,1,2,1,0,2,0,2,0,1,1,2,0],
  [2,0,2,1,2,0,1,0,0,0,2,0,0,2,1,1,0],
  [2,2,1,0,0,0,2,2,0,1,0,1,2,0,2,1,2,2,0]
]

def cert1408n : CertifiedBoard :=
  ⟨seed1408, by apply FastValid.valid; decide +kernel⟩

def cert1408r : CertifiedBoard :=
  ⟨seed1408.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1409 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,1,1,1,0,0,1,1,1,2,0,1],
  [0,2,1,2,1,2,0,0,1,2,2,0,2,1,0],
  [1,0,0,0,2,0,0,2,2,0,2,1,1,0,0,0,2],
  [0,1,0,2,0,1,2,0,2,2,1,0,2,0,1,0,1,1,0]
]

def cert1409n : CertifiedBoard :=
  ⟨seed1409, by apply FastValid.valid; decide +kernel⟩

def cert1409r : CertifiedBoard :=
  ⟨seed1409.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1410 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,1,1,1,0,0,1,1,1,2,0,1],
  [2,0,0,1,2,1,0,2,1,2,0,2,0,1,0],
  [0,0,0,2,0,1,2,2,0,2,1,1,0,2,2,0,0],
  [0,1,0,1,1,0,0,0,2,1,0,0,2,0,2,2,1,2,0]
]

def cert1410n : CertifiedBoard :=
  ⟨seed1410, by apply FastValid.valid; decide +kernel⟩

def cert1410r : CertifiedBoard :=
  ⟨seed1410.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1411 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,1,1,1,0,0,1,1,1,2,0,1],
  [2,0,2,0,1,2,2,0,2,0,0,0,0,1,0],
  [0,0,2,2,1,2,1,1,0,2,1,0,0,2,1,2,0],
  [0,1,1,0,2,2,0,2,1,0,1,2,0,1,0,0,2,0,0]
]

def cert1411n : CertifiedBoard :=
  ⟨seed1411, by apply FastValid.valid; decide +kernel⟩

def cert1411r : CertifiedBoard :=
  ⟨seed1411.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1412 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,1,1,1,0,0,1,1,1,2,0,2],
  [1,2,0,2,0,1,0,0,1,2,2,0,1,1,0],
  [0,2,1,1,0,2,1,2,0,0,0,2,2,0,0,2,0],
  [2,0,1,2,1,0,2,0,2,1,0,1,0,0,0,2,2,1,2]
]

def cert1412n : CertifiedBoard :=
  ⟨seed1412, by apply FastValid.valid; decide +kernel⟩

def cert1412r : CertifiedBoard :=
  ⟨seed1412.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1413 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,1,1,1,0,0,1,1,1,2,0,2],
  [1,2,1,2,2,0,2,2,0,0,2,0,1,1,0],
  [0,1,0,0,0,2,0,2,2,1,0,0,0,2,1,0,1],
  [0,2,0,1,0,2,1,1,0,2,1,2,0,0,1,2,0,1,2]
]

def cert1413n : CertifiedBoard :=
  ⟨seed1413, by apply FastValid.valid; decide +kernel⟩

def cert1413r : CertifiedBoard :=
  ⟨seed1413.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1414 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,1,1,1,0,0,1,1,2,0,1,2],
  [0,1,0,1,2,0,2,0,2,0,0,2,1,0,0],
  [0,0,2,1,2,1,1,0,2,2,1,0,2,2,0,1,0],
  [1,2,0,0,0,2,1,2,2,0,2,0,1,1,1,0,0,0,1]
]

def cert1414n : CertifiedBoard :=
  ⟨seed1414, by apply FastValid.valid; decide +kernel⟩

def cert1414r : CertifiedBoard :=
  ⟨seed1414.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1415 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,1,1,1,0,0,1,2,0,2,1,1],
  [2,0,0,2,1,2,0,0,1,1,0,2,0,1,0],
  [2,2,1,0,0,0,0,2,1,2,1,0,1,2,0,2,0],
  [1,1,1,2,2,0,1,1,0,0,2,2,0,2,0,1,0,2,2]
]

def cert1415n : CertifiedBoard :=
  ⟨seed1415, by apply FastValid.valid; decide +kernel⟩

def cert1415r : CertifiedBoard :=
  ⟨seed1415.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1416 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,1,1,1,0,0,2,0,2,1,1,0],
  [0,0,0,1,2,2,0,1,1,1,0,2,1,0,2],
  [0,2,2,0,0,2,2,1,2,0,1,0,1,2,1,0,0],
  [2,0,2,0,1,0,0,0,1,1,2,0,2,1,2,0,0,2,0]
]

def cert1416n : CertifiedBoard :=
  ⟨seed1416, by apply FastValid.valid; decide +kernel⟩

def cert1416r : CertifiedBoard :=
  ⟨seed1416.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1417 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,1,1,1,0,0,2,0,2,1,1,0],
  [0,2,1,2,2,0,0,1,0,2,0,1,2,0,2],
  [1,1,0,0,2,2,1,0,1,0,2,0,0,0,1,1,2],
  [1,2,1,2,0,1,2,0,2,1,0,0,0,2,2,0,1,1,1]
]

def cert1417n : CertifiedBoard :=
  ⟨seed1417, by apply FastValid.valid; decide +kernel⟩

def cert1417r : CertifiedBoard :=
  ⟨seed1417.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1418 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,1,1,1,0,0,2,0,2,1,1,1],
  [2,0,2,1,2,0,0,2,2,1,0,0,2,1,0],
  [1,1,0,0,0,0,1,1,0,2,2,0,0,1,2,2,0],
  [0,1,2,1,2,0,2,0,1,0,2,0,1,0,1,1,2,0,1]
]

def cert1418n : CertifiedBoard :=
  ⟨seed1418, by apply FastValid.valid; decide +kernel⟩

def cert1418r : CertifiedBoard :=
  ⟨seed1418.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1419 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,1,1,1,0,0,2,0,2,2,1,1],
  [2,0,2,2,0,0,2,1,2,0,0,0,1,2,0],
  [2,0,1,1,0,2,0,2,1,0,0,1,0,1,1,1,0],
  [1,1,2,0,1,0,2,0,1,2,1,0,0,0,2,1,2,2,0]
]

def cert1419n : CertifiedBoard :=
  ⟨seed1419, by apply FastValid.valid; decide +kernel⟩

def cert1419r : CertifiedBoard :=
  ⟨seed1419.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1420 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,1,1,1,0,0,2,1,1,1,0,2],
  [2,1,0,2,0,0,2,0,1,2,1,2,0,2,1],
  [0,2,2,0,0,1,0,0,0,1,1,2,2,1,0,0,0],
  [0,0,2,0,2,2,0,2,1,2,0,1,2,0,1,0,1,1,0]
]

def cert1420n : CertifiedBoard :=
  ⟨seed1420, by apply FastValid.valid; decide +kernel⟩

def cert1420r : CertifiedBoard :=
  ⟨seed1420.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1421 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,1,1,1,0,0,2,1,1,1,2,0],
  [0,0,0,1,2,1,0,1,0,0,2,0,1,2,0],
  [2,0,0,2,0,2,2,0,1,1,0,2,1,2,2,1,0],
  [2,0,2,2,0,1,1,0,2,1,2,0,2,0,0,0,1,0,0]
]

def cert1421n : CertifiedBoard :=
  ⟨seed1421, by apply FastValid.valid; decide +kernel⟩

def cert1421r : CertifiedBoard :=
  ⟨seed1421.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1422 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,1,1,1,0,0,2,1,1,1,2,0],
  [2,0,0,1,2,0,1,0,1,2,1,2,2,1,0],
  [0,2,1,2,0,2,0,0,2,1,0,0,0,0,1,0,2],
  [0,2,0,2,0,1,1,0,0,2,2,0,2,2,0,1,1,0,2]
]

def cert1422n : CertifiedBoard :=
  ⟨seed1422, by apply FastValid.valid; decide +kernel⟩

def cert1422r : CertifiedBoard :=
  ⟨seed1422.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1423 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,1,1,1,0,0,2,1,1,1,2,0],
  [2,0,0,2,0,1,1,0,1,2,1,2,2,1,0],
  [0,2,2,0,2,0,1,2,0,0,2,1,0,0,0,0,1],
  [0,1,1,0,2,0,2,2,0,1,0,0,1,0,2,1,2,0,2]
]

def cert1423n : CertifiedBoard :=
  ⟨seed1423, by apply FastValid.valid; decide +kernel⟩

def cert1423r : CertifiedBoard :=
  ⟨seed1423.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1424 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,1,1,1,0,0,2,1,1,2,0,2],
  [0,0,0,2,0,0,2,0,1,2,0,2,0,2,1],
  [2,1,2,0,0,0,1,1,0,1,1,1,0,2,2,1,0],
  [0,2,2,0,1,0,2,1,2,2,0,1,2,1,0,0,1,0,0]
]

def cert1424n : CertifiedBoard :=
  ⟨seed1424, by apply FastValid.valid; decide +kernel⟩

def cert1424r : CertifiedBoard :=
  ⟨seed1424.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1425 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,1,2,0,0,0,0,2,1,1,2,0],
  [2,1,2,0,2,2,0,0,1,1,1,0,0,2,1],
  [2,0,1,0,0,2,0,2,0,2,0,1,1,0,1,1,1],
  [1,1,0,2,1,0,0,1,0,2,2,1,2,2,0,1,2,1,0]
]

def cert1425n : CertifiedBoard :=
  ⟨seed1425, by apply FastValid.valid; decide +kernel⟩

def cert1425r : CertifiedBoard :=
  ⟨seed1425.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1426 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,1,2,0,0,0,0,2,2,1,1,0],
  [1,1,1,0,0,2,2,0,0,1,1,2,1,0,2],
  [0,1,2,2,0,1,0,2,1,2,0,2,0,1,0,0,1],
  [0,2,1,2,0,2,0,1,1,1,0,0,2,0,2,1,0,1,1]
]

def cert1426n : CertifiedBoard :=
  ⟨seed1426, by apply FastValid.valid; decide +kernel⟩

def cert1426r : CertifiedBoard :=
  ⟨seed1426.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1427 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,1,2,0,0,0,0,2,2,1,1,1],
  [1,1,0,2,0,2,1,2,0,2,0,1,2,1,0],
  [2,0,1,1,0,0,2,1,2,0,0,1,0,0,2,1,0],
  [1,0,2,2,0,2,0,1,1,1,0,0,1,0,1,1,2,2,0]
]

def cert1427n : CertifiedBoard :=
  ⟨seed1427, by apply FastValid.valid; decide +kernel⟩

def cert1427r : CertifiedBoard :=
  ⟨seed1427.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1428 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,1,2,0,0,0,0,2,2,1,1,2],
  [1,2,1,0,0,2,2,0,2,0,2,0,2,0,1],
  [0,1,2,0,1,0,1,1,0,0,1,1,1,0,2,1,0],
  [2,0,1,0,0,2,1,2,2,0,0,1,1,1,0,2,1,2,0]
]

def cert1428n : CertifiedBoard :=
  ⟨seed1428, by apply FastValid.valid; decide +kernel⟩

def cert1428r : CertifiedBoard :=
  ⟨seed1428.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1429 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,1,2,0,0,0,1,0,0,2,2,1],
  [2,2,0,1,1,0,1,0,0,2,2,0,1,1,0],
  [1,1,1,2,0,2,1,0,0,2,0,2,0,2,0,1,1],
  [2,1,2,1,0,2,1,1,1,0,2,1,2,0,0,0,1,2,2]
]

def cert1429n : CertifiedBoard :=
  ⟨seed1429, by apply FastValid.valid; decide +kernel⟩

def cert1429r : CertifiedBoard :=
  ⟨seed1429.map List.reverse, by apply FastValid.valid; decide +kernel⟩

end TBoards.Extended
