import Extended.Batch039

/- Generated from extended_seeds.json. Published seeds 0–4:
   Qiyuan Ma, DOI 10.5281/zenodo.23631079, CC-BY-4.0. -/

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.Extended

def seed1376 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,1,1,0,0,0,2,1,1,1,0,2],
  [0,2,0,1,1,1,0,2,2,1,2,2,0,2,1],
  [0,1,0,0,1,2,0,2,0,2,0,1,2,0,0,1,0],
  [2,1,2,1,0,0,2,2,0,1,1,2,0,0,0,2,1,0,1]
]

def cert1376n : CertifiedBoard :=
  ⟨seed1376, by apply FastValid.valid; decide +kernel⟩

def cert1376r : CertifiedBoard :=
  ⟨seed1376.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1377 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,1,1,0,0,0,2,1,1,1,2,0],
  [2,0,0,1,1,1,0,2,2,1,2,2,0,2,0],
  [0,2,1,0,1,2,1,0,0,0,1,0,2,2,0,1,0],
  [2,0,1,2,0,0,2,0,2,1,2,0,1,1,0,0,2,0,2]
]

def cert1377n : CertifiedBoard :=
  ⟨seed1377, by apply FastValid.valid; decide +kernel⟩

def cert1377r : CertifiedBoard :=
  ⟨seed1377.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1378 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,1,1,0,0,0,2,1,1,2,0,1],
  [0,1,0,1,2,1,2,0,1,2,0,2,0,2,0],
  [0,2,0,0,1,1,1,1,0,0,2,2,0,2,2,1,0],
  [2,0,0,0,2,1,2,2,0,1,1,0,0,1,0,2,1,0,2]
]

def cert1378n : CertifiedBoard :=
  ⟨seed1378, by apply FastValid.valid; decide +kernel⟩

def cert1378r : CertifiedBoard :=
  ⟨seed1378.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1379 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,1,1,0,0,2,0,2,1,1,1,0],
  [0,0,0,1,1,1,0,1,2,0,1,2,1,0,2],
  [0,2,0,2,1,2,2,0,1,0,0,2,0,2,1,0,2],
  [0,2,2,1,2,0,0,2,2,0,1,0,0,1,1,2,0,0,0]
]

def cert1379n : CertifiedBoard :=
  ⟨seed1379, by apply FastValid.valid; decide +kernel⟩

def cert1379r : CertifiedBoard :=
  ⟨seed1379.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1380 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,1,1,0,0,2,0,2,1,1,1,2],
  [1,2,2,0,1,1,0,1,2,0,2,0,0,0,1],
  [0,1,0,0,2,1,2,0,1,2,0,0,0,2,0,2,1],
  [2,1,2,1,0,2,2,0,1,1,1,0,0,1,0,2,2,1,0]
]

def cert1380n : CertifiedBoard :=
  ⟨seed1380, by apply FastValid.valid; decide +kernel⟩

def cert1380r : CertifiedBoard :=
  ⟨seed1380.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1381 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,1,1,0,0,2,0,2,2,1,1,0],
  [2,1,2,0,1,0,1,0,2,0,1,2,1,0,0],
  [0,0,2,0,2,2,0,2,1,0,0,1,1,1,1,0,2],
  [0,2,1,2,0,0,0,1,1,2,2,0,1,2,0,0,0,2,1]
]

def cert1381n : CertifiedBoard :=
  ⟨seed1381, by apply FastValid.valid; decide +kernel⟩

def cert1381r : CertifiedBoard :=
  ⟨seed1381.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1382 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,1,1,0,0,2,1,0,0,1,2,0],
  [0,0,0,1,2,1,0,2,0,2,0,2,1,1,0],
  [1,2,0,1,1,1,2,2,0,1,0,2,2,1,2,0,0],
  [2,0,0,0,2,0,1,1,1,0,1,0,0,2,2,0,2,1,2]
]

def cert1382n : CertifiedBoard :=
  ⟨seed1382, by apply FastValid.valid; decide +kernel⟩

def cert1382r : CertifiedBoard :=
  ⟨seed1382.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1383 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,1,1,0,0,2,2,0,2,0,1,2],
  [1,2,0,2,1,0,1,0,2,1,2,0,0,0,0],
  [0,1,1,0,0,1,2,0,1,1,2,2,1,0,2,0,1],
  [0,0,2,0,2,2,0,0,2,1,2,1,1,1,1,0,0,1,0]
]

def cert1383n : CertifiedBoard :=
  ⟨seed1383, by apply FastValid.valid; decide +kernel⟩

def cert1383r : CertifiedBoard :=
  ⟨seed1383.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1384 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,1,1,0,0,2,2,0,2,1,1,1],
  [2,0,0,1,1,1,0,0,0,1,0,2,0,1,0],
  [1,1,0,2,1,2,0,2,2,0,0,0,2,0,2,1,2],
  [1,2,1,0,1,2,2,1,0,0,2,0,1,1,2,0,1,2,0]
]

def cert1384n : CertifiedBoard :=
  ⟨seed1384, by apply FastValid.valid; decide +kernel⟩

def cert1384r : CertifiedBoard :=
  ⟨seed1384.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1385 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,1,1,1,0,0,0,0,2,0,2,2],
  [1,2,1,2,0,1,0,0,2,0,0,1,1,1,0],
  [2,2,0,1,1,2,0,0,1,0,2,2,0,2,1,0,1],
  [0,1,2,0,1,2,2,1,0,2,0,2,1,1,0,0,2,1,2]
]

def cert1385n : CertifiedBoard :=
  ⟨seed1385, by apply FastValid.valid; decide +kernel⟩

def cert1385r : CertifiedBoard :=
  ⟨seed1385.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1386 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,1,1,1,0,0,0,0,2,1,1,0],
  [0,2,1,2,0,2,0,2,1,0,1,2,1,2,0],
  [2,0,0,1,1,1,0,2,2,1,0,0,2,2,0,1,0],
  [1,0,0,2,0,1,2,2,0,2,0,0,1,1,2,0,1,0,2]
]

def cert1386n : CertifiedBoard :=
  ⟨seed1386, by apply FastValid.valid; decide +kernel⟩

def cert1386r : CertifiedBoard :=
  ⟨seed1386.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1387 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,1,1,1,0,0,0,0,2,1,1,0],
  [2,1,2,0,1,2,1,0,0,1,0,2,0,2,1],
  [1,0,0,2,0,1,1,2,0,2,0,0,2,2,0,2,1],
  [2,1,0,2,2,1,2,2,0,1,1,1,0,1,2,0,0,1,0]
]

def cert1387n : CertifiedBoard :=
  ⟨seed1387, by apply FastValid.valid; decide +kernel⟩

def cert1387r : CertifiedBoard :=
  ⟨seed1387.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1388 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,1,1,1,0,0,0,0,2,1,1,2],
  [2,0,0,1,2,1,2,0,1,0,2,0,2,0,1],
  [1,2,0,2,0,1,2,0,2,2,0,0,1,1,0,1,0],
  [0,1,1,1,0,2,1,0,0,2,2,1,0,0,2,1,2,2,0]
]

def cert1388n : CertifiedBoard :=
  ⟨seed1388, by apply FastValid.valid; decide +kernel⟩

def cert1388r : CertifiedBoard :=
  ⟨seed1388.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1389 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,1,1,1,0,0,0,0,2,2,1,1],
  [0,0,2,2,0,1,0,0,1,1,0,0,1,2,2],
  [2,2,0,2,0,2,0,0,2,1,2,1,0,1,1,1,0],
  [1,1,2,0,1,2,0,1,0,2,1,0,2,1,2,0,2,0,0]
]

def cert1389n : CertifiedBoard :=
  ⟨seed1389, by apply FastValid.valid; decide +kernel⟩

def cert1389r : CertifiedBoard :=
  ⟨seed1389.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1390 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,1,1,1,0,0,0,0,2,2,1,1],
  [0,1,2,0,2,1,0,1,0,0,1,2,0,1,0],
  [0,2,0,0,1,1,2,1,2,2,0,2,0,2,2,0,1],
  [1,1,0,0,2,1,2,0,1,1,1,0,2,1,0,2,0,0,2]
]

def cert1390n : CertifiedBoard :=
  ⟨seed1390, by apply FastValid.valid; decide +kernel⟩

def cert1390r : CertifiedBoard :=
  ⟨seed1390.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1391 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,1,1,1,0,0,0,2,1,1,1,2],
  [0,2,1,2,1,2,0,2,1,0,2,0,0,0,2],
  [0,0,1,2,2,1,0,0,2,2,0,0,1,0,1,1,0],
  [1,2,0,1,2,0,1,1,0,2,0,2,2,0,2,0,1,0,0]
]

def cert1391n : CertifiedBoard :=
  ⟨seed1391, by apply FastValid.valid; decide +kernel⟩

def cert1391r : CertifiedBoard :=
  ⟨seed1391.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1392 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,1,1,1,0,0,0,2,1,1,2,0],
  [0,0,0,2,1,2,1,2,0,0,1,2,2,1,0],
  [2,0,2,0,1,2,0,2,0,1,0,1,0,2,0,1,1],
  [1,1,1,0,0,1,1,0,2,2,0,2,1,0,0,2,2,0,0]
]

def cert1392n : CertifiedBoard :=
  ⟨seed1392, by apply FastValid.valid; decide +kernel⟩

def cert1392r : CertifiedBoard :=
  ⟨seed1392.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1393 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,1,1,1,0,0,0,2,2,1,1,0],
  [1,2,0,2,1,2,1,0,0,1,2,0,1,2,0],
  [2,2,0,1,0,0,0,1,1,0,1,0,2,0,0,2,2],
  [2,0,2,1,2,2,0,0,2,0,2,1,0,2,0,1,1,1,2]
]

def cert1393n : CertifiedBoard :=
  ⟨seed1393, by apply FastValid.valid; decide +kernel⟩

def cert1393r : CertifiedBoard :=
  ⟨seed1393.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1394 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,1,1,1,0,0,0,2,2,1,1,0],
  [2,0,2,2,0,1,1,0,1,1,1,2,1,0,0],
  [0,2,1,0,2,0,1,2,0,2,0,0,0,2,1,2,0],
  [0,0,1,2,2,0,2,1,2,0,0,1,0,2,0,1,0,0,2]
]

def cert1394n : CertifiedBoard :=
  ⟨seed1394, by apply FastValid.valid; decide +kernel⟩

def cert1394r : CertifiedBoard :=
  ⟨seed1394.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1395 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,1,1,1,0,0,0,2,2,1,1,1],
  [0,0,0,1,2,0,2,1,2,0,2,1,2,1,0],
  [2,0,1,0,1,0,0,2,0,0,2,0,1,1,2,2,0],
  [1,1,0,2,0,2,1,0,0,1,1,0,2,2,0,1,2,0,0]
]

def cert1395n : CertifiedBoard :=
  ⟨seed1395, by apply FastValid.valid; decide +kernel⟩

def cert1395r : CertifiedBoard :=
  ⟨seed1395.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1396 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,1,1,1,0,0,0,2,2,1,1,2],
  [1,2,1,2,0,2,0,2,0,0,2,0,0,0,1],
  [0,1,2,0,1,2,0,1,0,0,1,1,1,0,2,2,0],
  [2,0,1,1,0,1,0,2,1,0,0,2,1,2,2,0,2,1,0]
]

def cert1396n : CertifiedBoard :=
  ⟨seed1396, by apply FastValid.valid; decide +kernel⟩

def cert1396r : CertifiedBoard :=
  ⟨seed1396.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1397 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,1,1,1,0,0,0,2,2,1,1,2],
  [1,2,1,2,2,0,2,2,0,1,2,0,1,0,0],
  [0,0,0,1,1,1,0,0,2,0,2,0,2,1,0,1,0],
  [0,1,1,0,2,1,2,0,0,2,1,0,2,0,1,2,0,0,1]
]

def cert1397n : CertifiedBoard :=
  ⟨seed1397, by apply FastValid.valid; decide +kernel⟩

def cert1397r : CertifiedBoard :=
  ⟨seed1397.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1398 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,1,1,1,0,0,1,0,0,0,2,2],
  [2,0,0,2,1,2,0,2,2,0,1,0,1,2,0],
  [2,2,1,0,2,1,0,2,1,1,0,0,0,1,1,1,0],
  [2,0,2,0,1,1,2,2,0,1,2,1,2,0,0,2,0,2,0]
]

def cert1398n : CertifiedBoard :=
  ⟨seed1398, by apply FastValid.valid; decide +kernel⟩

def cert1398r : CertifiedBoard :=
  ⟨seed1398.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1399 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,1,1,1,0,0,1,0,0,2,2,1],
  [2,1,0,2,1,2,2,0,2,0,1,1,1,2,0],
  [0,0,0,0,2,0,2,1,1,0,2,2,0,1,1,0,0],
  [2,0,0,1,0,1,2,0,1,2,1,2,0,2,0,0,2,1,0]
]

def cert1399n : CertifiedBoard :=
  ⟨seed1399, by apply FastValid.valid; decide +kernel⟩

def cert1399r : CertifiedBoard :=
  ⟨seed1399.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1400 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,1,1,1,0,0,1,0,2,0,2,1],
  [2,1,2,0,0,0,2,0,2,1,0,0,2,2,0],
  [2,0,1,1,0,1,0,0,2,2,1,0,2,1,1,1,0],
  [0,0,0,1,2,1,2,2,0,1,2,0,1,1,2,0,2,0,0]
]

def cert1400n : CertifiedBoard :=
  ⟨seed1400, by apply FastValid.valid; decide +kernel⟩

def cert1400r : CertifiedBoard :=
  ⟨seed1400.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1401 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,1,1,1,0,0,1,0,2,2,1,1],
  [0,0,0,1,2,0,0,2,2,0,2,0,2,1,0],
  [1,1,0,2,1,2,0,1,0,0,2,0,1,1,2,2,0],
  [2,0,2,0,0,0,2,1,2,1,0,1,2,0,1,1,1,0,0]
]

def cert1401n : CertifiedBoard :=
  ⟨seed1401, by apply FastValid.valid; decide +kernel⟩

def cert1401r : CertifiedBoard :=
  ⟨seed1401.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1402 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,1,1,1,0,0,1,1,0,0,2,1],
  [2,1,2,0,2,0,1,0,1,2,1,0,2,2,0],
  [2,0,1,0,2,0,2,1,0,0,0,0,2,2,1,1,0],
  [0,2,0,2,1,2,0,1,2,2,0,0,1,1,1,2,0,0,2]
]

def cert1402n : CertifiedBoard :=
  ⟨seed1402, by apply FastValid.valid; decide +kernel⟩

def cert1402r : CertifiedBoard :=
  ⟨seed1402.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1403 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,1,1,1,0,0,1,1,0,2,1,1],
  [0,0,2,1,2,2,0,2,0,2,1,2,0,1,0],
  [1,1,0,0,0,0,2,2,0,2,2,1,0,0,2,0,1],
  [0,1,2,0,0,1,0,2,0,1,1,1,2,1,0,1,2,0,0]
]

def cert1403n : CertifiedBoard :=
  ⟨seed1403, by apply FastValid.valid; decide +kernel⟩

def cert1403r : CertifiedBoard :=
  ⟨seed1403.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1404 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,1,1,1,0,0,1,1,0,2,1,1],
  [0,0,2,1,2,2,0,2,0,2,1,2,0,1,0],
  [1,1,0,0,0,0,2,2,0,2,2,1,0,0,2,0,1],
  [0,1,2,1,0,1,0,2,0,1,1,1,2,0,0,1,2,0,0]
]

def cert1404n : CertifiedBoard :=
  ⟨seed1404, by apply FastValid.valid; decide +kernel⟩

def cert1404r : CertifiedBoard :=
  ⟨seed1404.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1405 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,1,1,1,0,0,1,1,1,0,0,0],
  [0,0,2,2,0,1,0,0,1,2,1,2,0,2,0],
  [2,1,0,2,2,1,2,2,0,0,0,2,1,1,0,2,1],
  [2,0,2,0,1,2,0,2,0,1,0,1,1,2,0,0,2,1,0]
]

def cert1405n : CertifiedBoard :=
  ⟨seed1405, by apply FastValid.valid; decide +kernel⟩

def cert1405r : CertifiedBoard :=
  ⟨seed1405.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1406 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,1,1,1,0,0,1,1,1,0,2,0],
  [2,0,0,1,2,1,2,0,0,2,0,2,0,1,0],
  [0,0,2,2,0,1,2,2,1,0,2,1,2,0,1,0,1],
  [0,1,1,0,0,0,2,1,1,2,0,2,2,0,2,1,0,0,0]
]

def cert1406n : CertifiedBoard :=
  ⟨seed1406, by apply FastValid.valid; decide +kernel⟩

def cert1406r : CertifiedBoard :=
  ⟨seed1406.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1407 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [1,0,1,1,1,0,0,1,1,1,0,2,1],
  [2,0,0,1,2,0,2,0,0,0,2,0,2,0,1],
  [2,1,1,0,1,0,0,2,2,0,1,1,2,0,2,2,0],
  [0,1,2,1,0,2,1,0,0,0,2,1,2,2,1,2,0,1,0]
]

def cert1407n : CertifiedBoard :=
  ⟨seed1407, by apply FastValid.valid; decide +kernel⟩

def cert1407r : CertifiedBoard :=
  ⟨seed1407.map List.reverse, by apply FastValid.valid; decide +kernel⟩

end TBoards.Extended
