import Extended.Batch008

/- Generated from extended_seeds.json. Published seeds 0–4:
   Qiyuan Ma, DOI 10.5281/zenodo.23631079, CC-BY-4.0. -/

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.Extended

def seed0384 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,1,0,0,2,1,1,1,0,0],
  [2,0,1,1,1,2,2,0,0,0,2,0,2,1,0],
  [0,2,1,2,0,1,0,1,1,0,1,0,2,2,1,2,0],
  [1,0,2,2,0,2,0,0,1,1,0,0,0,2,0,1,2,0,2]
]

def cert0384n : CertifiedBoard :=
  ⟨seed0384, by apply FastValid.valid; decide +kernel⟩

def cert0384r : CertifiedBoard :=
  ⟨seed0384.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0385 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,1,0,0,2,1,1,2,0,2],
  [0,0,1,1,0,1,0,2,0,1,1,1,1,0,0],
  [2,1,0,1,2,2,0,1,0,2,2,0,0,2,0,2,1],
  [0,2,1,2,0,2,2,1,2,0,1,1,0,0,2,0,0,0,0]
]

def cert0385n : CertifiedBoard :=
  ⟨seed0385, by apply FastValid.valid; decide +kernel⟩

def cert0385r : CertifiedBoard :=
  ⟨seed0385.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0386 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,1,0,0,2,1,1,2,0,2],
  [0,2,0,2,0,1,0,1,0,1,2,2,1,0,0],
  [0,1,1,0,2,2,0,2,1,2,0,1,1,1,0,0,1],
  [2,0,1,1,1,0,2,0,0,0,2,1,2,0,0,0,2,2,0]
]

def cert0386n : CertifiedBoard :=
  ⟨seed0386, by apply FastValid.valid; decide +kernel⟩

def cert0386r : CertifiedBoard :=
  ⟨seed0386.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0387 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,1,2,0,1,0,0,0,2,1],
  [2,1,0,2,1,1,1,2,0,2,0,0,2,2,0],
  [2,0,2,0,2,0,1,1,0,1,1,1,0,1,1,0,0],
  [1,0,2,2,1,2,0,1,2,2,0,0,0,2,1,0,0,1,0]
]

def cert0387n : CertifiedBoard :=
  ⟨seed0387, by apply FastValid.valid; decide +kernel⟩

def cert0387r : CertifiedBoard :=
  ⟨seed0387.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0388 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,1,2,0,1,0,1,1,1,0],
  [1,1,0,1,2,0,0,0,2,0,1,1,1,0,2],
  [1,0,0,2,0,2,2,0,2,2,1,2,2,0,1,0,0],
  [0,2,1,0,0,2,1,1,2,0,2,1,0,2,0,0,0,1,1]
]

def cert0388n : CertifiedBoard :=
  ⟨seed0388, by apply FastValid.valid; decide +kernel⟩

def cert0388r : CertifiedBoard :=
  ⟨seed0388.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0389 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,1,2,0,1,0,2,2,1,1],
  [1,0,2,1,0,0,2,1,2,2,0,2,0,0,0],
  [2,2,0,0,2,1,0,1,1,1,1,0,0,0,1,1,0],
  [1,1,2,0,1,0,1,2,0,1,1,0,0,2,0,2,0,2,2]
]

def cert0389n : CertifiedBoard :=
  ⟨seed0389, by apply FastValid.valid; decide +kernel⟩

def cert0389r : CertifiedBoard :=
  ⟨seed0389.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0390 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,1,2,0,1,0,2,2,1,1],
  [2,0,1,0,0,0,2,1,2,2,0,2,0,1,2],
  [1,2,0,0,0,1,1,0,1,1,1,0,0,2,1,0,0],
  [1,1,1,2,0,2,2,0,0,2,0,2,1,0,1,1,0,2,0]
]

def cert0390n : CertifiedBoard :=
  ⟨seed0390, by apply FastValid.valid; decide +kernel⟩

def cert0390r : CertifiedBoard :=
  ⟨seed0390.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0391 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,1,2,0,1,0,2,2,1,1],
  [2,1,0,1,1,1,1,2,0,1,0,1,1,0,0],
  [0,0,0,2,2,0,2,1,0,0,2,0,1,2,2,0,0],
  [1,1,0,2,0,2,1,2,0,0,1,1,0,0,0,2,0,2,1]
]

def cert0391n : CertifiedBoard :=
  ⟨seed0391, by apply FastValid.valid; decide +kernel⟩

def cert0391r : CertifiedBoard :=
  ⟨seed0391.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0392 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,1,2,0,1,1,0,0,2,1],
  [1,0,1,1,1,2,2,1,0,0,0,1,0,1,0],
  [2,2,0,2,0,1,2,0,2,1,2,0,0,2,1,0,0],
  [2,1,1,1,0,2,0,0,0,2,0,2,2,0,1,1,0,2,2]
]

def cert0392n : CertifiedBoard :=
  ⟨seed0392, by apply FastValid.valid; decide +kernel⟩

def cert0392r : CertifiedBoard :=
  ⟨seed0392.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0393 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,1,2,0,1,1,1,0,0,0],
  [2,0,2,0,1,1,1,2,0,2,1,0,1,1,0],
  [1,0,2,2,1,0,0,0,2,1,2,0,0,1,2,2,0],
  [0,1,0,0,2,2,0,0,2,1,1,0,1,0,2,0,2,0,1]
]

def cert0393n : CertifiedBoard :=
  ⟨seed0393, by apply FastValid.valid; decide +kernel⟩

def cert0393r : CertifiedBoard :=
  ⟨seed0393.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0394 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,1,2,0,1,2,0,2,1,1],
  [1,1,0,1,1,1,1,2,0,2,0,2,2,0,0],
  [2,0,1,0,0,0,2,1,0,2,2,1,0,0,0,1,0],
  [1,0,1,1,0,2,0,0,2,0,1,1,0,0,2,1,2,2,0]
]

def cert0394n : CertifiedBoard :=
  ⟨seed0394, by apply FastValid.valid; decide +kernel⟩

def cert0394r : CertifiedBoard :=
  ⟨seed0394.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0395 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,1,2,0,1,2,0,2,1,1],
  [2,0,1,0,0,0,0,2,1,0,1,1,2,2,0],
  [0,2,2,0,0,2,0,0,1,1,0,1,1,1,1,0,2],
  [1,1,0,2,0,2,2,1,2,0,1,0,0,2,0,2,1,0,0]
]

def cert0395n : CertifiedBoard :=
  ⟨seed0395, by apply FastValid.valid; decide +kernel⟩

def cert0395r : CertifiedBoard :=
  ⟨seed0395.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0396 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,1,2,0,1,2,0,2,2,1],
  [2,1,2,0,2,0,0,2,1,0,0,2,1,1,0],
  [0,1,1,1,1,0,1,0,0,0,0,1,1,2,2,0,0],
  [1,0,1,0,0,2,0,2,1,0,2,2,0,1,1,0,2,0,1]
]

def cert0396n : CertifiedBoard :=
  ⟨seed0396, by apply FastValid.valid; decide +kernel⟩

def cert0396r : CertifiedBoard :=
  ⟨seed0396.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0397 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,1,2,0,2,0,1,1,1,2],
  [0,1,0,1,2,0,2,0,2,1,2,2,0,0,0],
  [1,2,0,1,1,0,2,1,1,0,1,0,0,2,0,0,1],
  [1,1,1,0,0,0,2,2,1,0,0,2,1,0,2,2,0,1,1]
]

def cert0397n : CertifiedBoard :=
  ⟨seed0397, by apply FastValid.valid; decide +kernel⟩

def cert0397r : CertifiedBoard :=
  ⟨seed0397.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0398 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,1,2,0,2,1,1,0,2,0],
  [1,0,1,1,1,1,0,1,0,0,2,0,2,1,0],
  [2,0,2,0,1,2,2,0,1,1,0,2,2,0,1,0,0],
  [2,2,1,2,0,0,0,0,2,1,0,0,1,1,2,0,0,2,2]
]

def cert0398n : CertifiedBoard :=
  ⟨seed0398, by apply FastValid.valid; decide +kernel⟩

def cert0398r : CertifiedBoard :=
  ⟨seed0398.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0399 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,1,2,0,2,1,1,0,2,0],
  [2,0,2,1,0,0,2,2,0,1,0,0,2,1,2],
  [1,2,0,1,1,1,0,0,0,2,0,0,1,1,1,0,1],
  [0,1,1,2,0,2,0,1,0,2,2,1,0,1,2,2,0,0,0]
]

def cert0399n : CertifiedBoard :=
  ⟨seed0399, by apply FastValid.valid; decide +kernel⟩

def cert0399r : CertifiedBoard :=
  ⟨seed0399.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0400 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,1,2,0,2,1,1,1,0,2],
  [2,0,0,1,2,0,1,1,0,1,1,1,0,0,0],
  [0,2,0,2,0,2,1,2,2,0,1,0,0,2,1,0,1],
  [0,1,1,2,0,1,0,0,0,2,2,0,0,2,2,1,0,2,0]
]

def cert0400n : CertifiedBoard :=
  ⟨seed0400, by apply FastValid.valid; decide +kernel⟩

def cert0400r : CertifiedBoard :=
  ⟨seed0400.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0401 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,1,2,2,1,0,0,0,2,0],
  [0,0,2,2,0,2,1,1,1,0,2,1,2,0,0],
  [2,0,1,0,2,1,0,1,2,0,0,1,1,1,0,1,1],
  [1,1,2,0,2,0,1,0,0,2,2,0,2,0,1,1,0,0,0]
]

def cert0401n : CertifiedBoard :=
  ⟨seed0401, by apply FastValid.valid; decide +kernel⟩

def cert0401r : CertifiedBoard :=
  ⟨seed0401.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0402 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,1,2,2,1,0,0,0,2,1],
  [2,1,0,2,0,2,1,1,0,0,2,1,2,0,0],
  [0,2,0,2,0,1,1,1,1,0,1,0,1,1,2,0,0],
  [0,0,1,1,0,2,2,0,1,2,0,1,0,0,0,2,2,0,2]
]

def cert0402n : CertifiedBoard :=
  ⟨seed0402, by apply FastValid.valid; decide +kernel⟩

def cert0402r : CertifiedBoard :=
  ⟨seed0402.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0403 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,1,2,2,1,0,0,2,0,1],
  [1,0,1,1,0,1,1,1,2,0,2,1,1,0,0],
  [0,1,0,2,0,2,2,0,0,2,1,2,0,1,2,0,0],
  [0,0,2,1,0,2,0,2,2,0,1,1,1,0,0,0,0,1,0]
]

def cert0403n : CertifiedBoard :=
  ⟨seed0403, by apply FastValid.valid; decide +kernel⟩

def cert0403r : CertifiedBoard :=
  ⟨seed0403.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0404 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,1,2,2,1,0,0,2,1,1],
  [1,1,0,1,1,1,0,2,0,2,1,0,1,0,0],
  [0,0,2,1,2,0,0,0,2,2,0,1,2,0,1,0,2],
  [0,2,0,1,1,1,0,0,1,1,2,0,2,0,2,2,0,0,0]
]

def cert0404n : CertifiedBoard :=
  ⟨seed0404, by apply FastValid.valid; decide +kernel⟩

def cert0404r : CertifiedBoard :=
  ⟨seed0404.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0405 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,1,2,2,1,0,1,1,0,0],
  [1,0,0,2,0,1,1,2,0,1,1,1,0,1,0],
  [0,1,2,0,2,2,0,0,0,2,2,0,2,1,2,0,1],
  [0,0,1,0,2,1,1,1,0,2,0,2,0,0,0,2,1,0,0]
]

def cert0405n : CertifiedBoard :=
  ⟨seed0405, by apply FastValid.valid; decide +kernel⟩

def cert0405r : CertifiedBoard :=
  ⟨seed0405.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0406 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,1,2,2,1,0,1,1,0,0],
  [2,1,0,0,0,2,1,1,1,0,1,1,1,0,2],
  [0,2,0,2,1,2,0,2,0,0,2,0,1,0,0,2,1],
  [2,0,2,2,0,1,2,0,0,0,1,0,2,2,0,1,1,2,0]
]

def cert0406n : CertifiedBoard :=
  ⟨seed0406, by apply FastValid.valid; decide +kernel⟩

def cert0406r : CertifiedBoard :=
  ⟨seed0406.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0407 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,1,2,2,1,0,1,1,1,0],
  [0,2,2,0,0,0,0,2,2,0,1,1,1,0,1],
  [0,1,1,2,0,0,2,1,0,2,1,2,0,1,0,0,2],
  [1,0,2,0,2,0,2,0,1,2,0,2,1,1,0,0,1,0,0]
]

def cert0407n : CertifiedBoard :=
  ⟨seed0407, by apply FastValid.valid; decide +kernel⟩

def cert0407r : CertifiedBoard :=
  ⟨seed0407.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0408 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,1,2,2,1,0,1,1,1,2],
  [0,2,0,2,1,1,1,0,2,0,1,0,0,0,2],
  [2,1,0,0,2,2,0,1,2,0,1,1,0,1,0,0,0],
  [1,2,0,2,2,0,2,0,0,2,1,2,0,0,1,1,0,2,1]
]

def cert0408n : CertifiedBoard :=
  ⟨seed0408, by apply FastValid.valid; decide +kernel⟩

def cert0408r : CertifiedBoard :=
  ⟨seed0408.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0409 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,1,2,2,1,0,1,1,1,2],
  [1,2,0,0,0,2,1,1,0,0,1,1,1,0,0],
  [2,0,0,0,2,1,0,2,0,1,0,1,2,0,2,2,0],
  [2,0,1,1,0,2,2,0,2,0,1,0,0,2,1,2,0,2,0]
]

def cert0409n : CertifiedBoard :=
  ⟨seed0409, by apply FastValid.valid; decide +kernel⟩

def cert0409r : CertifiedBoard :=
  ⟨seed0409.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0410 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,1,2,2,1,0,1,1,1,2],
  [1,2,0,1,0,0,0,2,0,0,1,1,1,0,2],
  [0,2,1,1,0,0,2,1,2,0,2,0,1,2,0,0,0],
  [1,0,2,2,0,2,2,0,2,0,1,1,0,0,2,1,0,1,0]
]

def cert0410n : CertifiedBoard :=
  ⟨seed0410, by apply FastValid.valid; decide +kernel⟩

def cert0410r : CertifiedBoard :=
  ⟨seed0410.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0411 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,1,2,2,1,0,2,0,1,1],
  [0,0,1,0,0,2,1,1,1,0,2,2,0,0,0],
  [1,2,0,1,1,0,0,0,2,0,1,1,2,0,2,1,2],
  [1,1,1,0,1,2,0,0,2,0,2,2,0,2,1,0,1,0,0]
]

def cert0411n : CertifiedBoard :=
  ⟨seed0411, by apply FastValid.valid; decide +kernel⟩

def cert0411r : CertifiedBoard :=
  ⟨seed0411.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0412 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,1,2,2,1,0,2,0,2,2],
  [2,2,0,1,0,0,0,0,2,1,0,1,1,2,0],
  [2,1,1,1,0,0,2,0,0,1,1,0,1,1,1,0,0],
  [2,0,1,2,0,1,0,2,1,2,0,0,2,2,0,2,0,2,1]
]

def cert0412n : CertifiedBoard :=
  ⟨seed0412, by apply FastValid.valid; decide +kernel⟩

def cert0412r : CertifiedBoard :=
  ⟨seed0412.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0413 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,1,2,2,1,0,2,1,1,1],
  [0,1,0,0,0,2,0,1,1,0,2,2,0,1,2],
  [1,2,0,0,2,1,2,0,0,2,1,0,0,0,1,0,1],
  [1,1,1,0,1,1,2,0,2,0,2,0,2,2,0,1,1,0,0]
]

def cert0413n : CertifiedBoard :=
  ⟨seed0413, by apply FastValid.valid; decide +kernel⟩

def cert0413r : CertifiedBoard :=
  ⟨seed0413.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0414 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,1,2,2,1,0,2,1,1,1],
  [1,0,0,1,2,0,2,0,1,1,0,1,0,0,0],
  [1,2,0,1,1,0,0,2,2,0,0,2,2,0,2,1,0],
  [1,1,1,0,2,0,1,0,1,1,2,0,0,0,2,0,2,1,2]
]

def cert0414n : CertifiedBoard :=
  ⟨seed0414, by apply FastValid.valid; decide +kernel⟩

def cert0414r : CertifiedBoard :=
  ⟨seed0414.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0415 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,2,0,0,0,0,2,1,1,1],
  [0,0,1,1,0,1,1,0,2,1,2,0,2,1,2],
  [1,2,0,1,2,1,0,0,2,2,1,0,2,0,1,0,0],
  [1,1,1,0,1,1,2,0,0,2,0,2,0,2,2,0,1,0,0]
]

def cert0415n : CertifiedBoard :=
  ⟨seed0415, by apply FastValid.valid; decide +kernel⟩

def cert0415r : CertifiedBoard :=
  ⟨seed0415.map List.reverse, by apply FastValid.valid; decide +kernel⟩

end TBoards.Extended
