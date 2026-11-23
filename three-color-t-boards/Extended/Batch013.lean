import Extended.Batch009

/- Generated from extended_seeds.json. Published seeds 0–4:
   Qiyuan Ma, DOI 10.5281/zenodo.23631079, CC-BY-4.0. -/

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.Extended

def seed0416 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,2,0,0,0,0,2,1,1,1],
  [2,1,0,0,2,2,1,2,0,2,0,2,1,2,1],
  [1,1,2,0,0,2,0,1,0,0,1,1,0,1,1,0,0],
  [2,0,1,2,0,1,0,2,1,0,1,1,1,0,2,0,2,2,0]
]

def cert0416n : CertifiedBoard :=
  ⟨seed0416, by apply FastValid.valid; decide +kernel⟩

def cert0416r : CertifiedBoard :=
  ⟨seed0416.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0417 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,2,0,0,0,0,2,2,1,1],
  [1,0,1,1,1,0,2,2,0,0,1,1,2,1,0],
  [1,1,0,2,0,1,2,0,2,0,2,1,2,0,1,0,0],
  [2,0,2,1,2,0,1,1,1,0,1,0,0,2,1,0,0,2,0]
]

def cert0417n : CertifiedBoard :=
  ⟨seed0417, by apply FastValid.valid; decide +kernel⟩

def cert0417r : CertifiedBoard :=
  ⟨seed0417.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0418 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,2,0,0,0,0,2,2,1,1],
  [2,0,1,1,1,1,2,0,0,1,0,2,1,0,0],
  [1,1,0,0,2,1,2,0,2,1,2,1,0,1,0,2,0],
  [0,2,0,2,2,0,1,2,0,2,0,1,1,0,1,1,0,0,2]
]

def cert0418n : CertifiedBoard :=
  ⟨seed0418, by apply FastValid.valid; decide +kernel⟩

def cert0418r : CertifiedBoard :=
  ⟨seed0418.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0419 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,2,0,0,0,2,2,1,1,1],
  [0,1,0,1,1,0,0,2,2,0,2,1,2,0,1],
  [1,0,2,1,2,1,0,0,1,1,2,0,1,2,0,0,0],
  [1,1,1,0,1,0,2,0,1,1,0,0,2,0,2,0,2,1,0]
]

def cert0419n : CertifiedBoard :=
  ⟨seed0419, by apply FastValid.valid; decide +kernel⟩

def cert0419r : CertifiedBoard :=
  ⟨seed0419.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0420 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,2,0,0,0,2,2,1,1,1],
  [2,1,0,0,0,2,1,2,0,2,0,2,1,2,1],
  [1,1,2,0,0,2,0,1,0,0,1,1,0,1,1,0,0],
  [2,0,1,2,0,1,0,2,1,0,1,1,1,0,2,0,2,2,0]
]

def cert0420n : CertifiedBoard :=
  ⟨seed0420, by apply FastValid.valid; decide +kernel⟩

def cert0420r : CertifiedBoard :=
  ⟨seed0420.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0421 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,2,0,0,0,2,2,1,1,1],
  [2,2,0,1,1,2,0,0,1,1,0,1,0,0,0],
  [1,0,2,1,2,1,0,0,2,1,2,0,2,1,0,1,0],
  [1,1,0,2,0,1,1,1,0,0,2,0,2,0,1,2,0,2,2]
]

def cert0421n : CertifiedBoard :=
  ⟨seed0421, by apply FastValid.valid; decide +kernel⟩

def cert0421r : CertifiedBoard :=
  ⟨seed0421.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0422 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,2,0,0,2,0,1,1,0,2],
  [0,2,0,1,1,2,0,2,2,1,2,1,0,0,0],
  [1,0,2,2,0,1,0,0,2,1,1,1,1,0,1,1,0],
  [2,1,2,0,2,0,0,0,1,0,1,2,0,2,1,0,0,2,1]
]

def cert0422n : CertifiedBoard :=
  ⟨seed0422, by apply FastValid.valid; decide +kernel⟩

def cert0422r : CertifiedBoard :=
  ⟨seed0422.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0423 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,2,0,0,2,0,2,1,1,1],
  [1,1,0,1,0,2,0,2,2,1,0,1,1,0,0],
  [2,1,2,0,1,2,0,1,0,0,0,0,2,1,0,2,1],
  [0,1,1,1,0,0,2,2,0,2,0,0,1,1,2,1,2,0,1]
]

def cert0423n : CertifiedBoard :=
  ⟨seed0423, by apply FastValid.valid; decide +kernel⟩

def cert0423r : CertifiedBoard :=
  ⟨seed0423.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0424 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,2,0,0,2,1,1,0,0,0],
  [2,0,2,1,2,0,1,0,2,0,1,0,0,2,0],
  [1,0,1,1,1,1,2,0,2,2,1,2,1,0,1,1,0],
  [0,0,0,1,1,0,0,2,2,0,2,1,0,2,0,1,2,0,0]
]

def cert0424n : CertifiedBoard :=
  ⟨seed0424, by apply FastValid.valid; decide +kernel⟩

def cert0424r : CertifiedBoard :=
  ⟨seed0424.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0425 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,2,0,1,1,0,2,2,1,1],
  [1,2,0,1,2,0,2,1,2,0,0,2,0,0,0],
  [1,1,1,0,1,1,1,0,0,2,1,0,0,0,2,0,2],
  [0,2,0,2,1,2,1,0,0,1,0,1,0,2,2,0,1,1,2]
]

def cert0425n : CertifiedBoard :=
  ⟨seed0425, by apply FastValid.valid; decide +kernel⟩

def cert0425r : CertifiedBoard :=
  ⟨seed0425.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0426 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,2,0,1,1,0,2,2,1,1],
  [2,0,1,1,1,1,2,0,0,0,2,0,1,0,0],
  [1,1,0,0,2,1,2,0,2,2,0,0,0,1,1,0,2],
  [0,2,0,2,0,2,1,0,1,0,0,2,1,0,1,2,1,2,0]
]

def cert0426n : CertifiedBoard :=
  ⟨seed0426, by apply FastValid.valid; decide +kernel⟩

def cert0426r : CertifiedBoard :=
  ⟨seed0426.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0427 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,2,0,1,1,0,2,2,1,1],
  [2,0,1,1,1,1,2,0,0,0,2,0,1,0,0],
  [1,1,0,1,2,0,2,0,2,2,0,0,0,1,1,0,2],
  [0,2,1,0,0,2,1,0,1,0,0,2,0,2,1,2,1,2,0]
]

def cert0427n : CertifiedBoard :=
  ⟨seed0427, by apply FastValid.valid; decide +kernel⟩

def cert0427r : CertifiedBoard :=
  ⟨seed0427.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0428 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,2,0,1,1,1,0,2,1,1],
  [2,1,0,0,2,2,1,2,1,0,0,2,0,0,0],
  [1,1,1,0,1,0,0,2,0,1,0,2,0,2,2,0,1],
  [0,1,2,0,2,1,2,0,0,0,1,1,0,1,1,2,0,2,1]
]

def cert0428n : CertifiedBoard :=
  ⟨seed0428, by apply FastValid.valid; decide +kernel⟩

def cert0428r : CertifiedBoard :=
  ⟨seed0428.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0429 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,2,0,1,1,1,1,0,0,0],
  [1,0,1,0,0,2,2,0,2,1,2,1,0,0,2],
  [0,2,0,1,1,0,2,0,2,1,1,0,1,2,0,2,1],
  [2,1,2,0,0,0,2,0,1,1,2,0,0,1,0,2,2,1,0]
]

def cert0429n : CertifiedBoard :=
  ⟨seed0429, by apply FastValid.valid; decide +kernel⟩

def cert0429r : CertifiedBoard :=
  ⟨seed0429.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0430 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,2,0,1,1,1,1,0,0,0],
  [1,2,0,1,1,2,0,0,0,2,0,0,1,1,0],
  [1,0,0,2,1,2,0,2,0,2,2,1,0,1,2,1,2],
  [0,1,0,0,2,0,2,2,0,1,0,2,1,0,2,1,1,0,1]
]

def cert0430n : CertifiedBoard :=
  ⟨seed0430, by apply FastValid.valid; decide +kernel⟩

def cert0430r : CertifiedBoard :=
  ⟨seed0430.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0431 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,2,0,1,1,1,2,0,2,2],
  [2,2,0,1,0,2,0,2,1,0,0,0,2,1,1],
  [1,1,0,0,1,1,0,1,1,1,0,2,0,0,2,0,0],
  [0,1,2,1,0,0,0,2,1,2,0,2,2,1,2,0,1,0,1]
]

def cert0431n : CertifiedBoard :=
  ⟨seed0431, by apply FastValid.valid; decide +kernel⟩

def cert0431r : CertifiedBoard :=
  ⟨seed0431.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0432 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,2,0,2,0,0,2,1,1,0],
  [2,2,0,1,2,0,2,2,1,0,1,1,1,0,0],
  [1,0,0,0,1,0,1,1,1,2,0,2,0,1,1,0,2],
  [0,2,1,2,0,0,2,1,2,1,0,2,0,1,0,0,0,2,2]
]

def cert0432n : CertifiedBoard :=
  ⟨seed0432, by apply FastValid.valid; decide +kernel⟩

def cert0432r : CertifiedBoard :=
  ⟨seed0432.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0433 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,2,0,2,0,1,1,1,2,0],
  [1,0,2,0,0,2,2,0,1,1,1,0,0,0,1],
  [0,1,2,0,2,1,0,2,1,2,1,2,0,1,0,1,0],
  [2,0,2,1,1,0,0,2,2,1,0,1,1,0,0,0,2,0,0]
]

def cert0433n : CertifiedBoard :=
  ⟨seed0433, by apply FastValid.valid; decide +kernel⟩

def cert0433r : CertifiedBoard :=
  ⟨seed0433.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0434 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,2,0,2,1,0,1,1,0,0],
  [0,0,1,0,0,2,2,0,1,0,1,2,1,0,2],
  [0,2,1,2,0,1,1,1,2,0,0,2,1,1,1,0,2],
  [0,2,2,1,2,0,0,0,2,0,2,0,2,0,1,1,0,0,0]
]

def cert0434n : CertifiedBoard :=
  ⟨seed0434, by apply FastValid.valid; decide +kernel⟩

def cert0434r : CertifiedBoard :=
  ⟨seed0434.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0435 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,2,0,2,1,0,1,1,0,2],
  [0,0,1,0,0,2,2,0,1,0,1,2,1,0,0],
  [0,2,1,2,0,1,1,1,2,0,0,2,1,1,1,0,2],
  [0,2,2,1,2,0,0,0,2,0,2,0,2,0,1,1,0,0,0]
]

def cert0435n : CertifiedBoard :=
  ⟨seed0435, by apply FastValid.valid; decide +kernel⟩

def cert0435r : CertifiedBoard :=
  ⟨seed0435.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0436 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,2,0,2,1,0,1,1,0,2],
  [2,0,1,1,1,2,0,0,0,2,1,2,1,0,0],
  [0,2,0,2,0,1,1,1,0,2,0,2,1,1,0,1,0],
  [1,0,0,2,2,1,2,0,0,0,2,2,0,1,0,0,1,2,0]
]

def cert0436n : CertifiedBoard :=
  ⟨seed0436, by apply FastValid.valid; decide +kernel⟩

def cert0436r : CertifiedBoard :=
  ⟨seed0436.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0437 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,2,0,2,1,2,0,1,1,2],
  [1,2,0,0,0,0,2,1,1,1,1,0,0,2,2],
  [0,1,0,1,0,2,0,2,0,1,2,1,0,1,1,0,0],
  [2,2,0,0,2,1,0,2,2,1,2,0,2,0,1,1,0,0,1]
]

def cert0437n : CertifiedBoard :=
  ⟨seed0437, by apply FastValid.valid; decide +kernel⟩

def cert0437r : CertifiedBoard :=
  ⟨seed0437.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0438 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,2,0,2,1,2,0,1,1,2],
  [1,2,0,0,0,0,2,2,1,0,0,1,2,1,1],
  [1,1,1,1,0,0,2,0,2,0,1,0,1,0,2,0,0],
  [0,1,1,0,0,2,1,0,1,1,0,2,1,2,0,2,2,0,1]
]

def cert0438n : CertifiedBoard :=
  ⟨seed0438, by apply FastValid.valid; decide +kernel⟩

def cert0438r : CertifiedBoard :=
  ⟨seed0438.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0439 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,0,0,0,2,1,0,2,2,1,1],
  [2,1,0,0,0,1,0,1,1,1,0,0,1,2,1],
  [1,1,2,0,0,2,2,0,2,1,2,2,0,1,1,0,0],
  [2,0,2,0,2,1,2,0,1,1,1,0,1,2,0,1,0,2,0]
]

def cert0439n : CertifiedBoard :=
  ⟨seed0439, by apply FastValid.valid; decide +kernel⟩

def cert0439r : CertifiedBoard :=
  ⟨seed0439.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0440 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,0,0,0,2,2,0,1,1,0,0],
  [1,2,0,0,0,2,0,1,2,0,2,0,2,1,2],
  [1,1,1,1,0,2,2,1,0,0,1,0,1,1,2,1,1],
  [1,2,0,1,2,2,0,2,1,0,0,1,0,1,1,0,2,1,2]
]

def cert0440n : CertifiedBoard :=
  ⟨seed0440, by apply FastValid.valid; decide +kernel⟩

def cert0440r : CertifiedBoard :=
  ⟨seed0440.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0441 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,0,0,0,2,2,0,2,1,1,2],
  [1,0,2,2,1,2,0,0,0,1,0,2,1,0,0],
  [1,2,1,0,1,1,1,1,0,0,1,0,1,2,2,0,1],
  [0,1,1,0,0,2,0,1,2,0,2,0,2,1,2,0,1,1,0]
]

def cert0441n : CertifiedBoard :=
  ⟨seed0441, by apply FastValid.valid; decide +kernel⟩

def cert0441r : CertifiedBoard :=
  ⟨seed0441.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0442 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,0,0,2,0,1,1,0,1,1,2],
  [0,2,0,2,2,0,0,1,1,1,0,1,2,0,2],
  [2,1,0,2,1,1,1,0,2,1,0,0,1,0,0,2,1],
  [1,2,0,2,2,1,2,2,0,1,2,1,2,0,1,0,0,0,0]
]

def cert0442n : CertifiedBoard :=
  ⟨seed0442, by apply FastValid.valid; decide +kernel⟩

def cert0442r : CertifiedBoard :=
  ⟨seed0442.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0443 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,0,0,2,0,1,1,1,0,1,1],
  [1,2,0,2,2,0,0,0,2,1,0,0,1,2,2],
  [1,1,0,2,0,2,1,0,2,1,1,1,0,0,0,1,2],
  [2,2,0,2,2,1,2,0,1,1,2,1,2,0,1,0,1,0,0]
]

def cert0443n : CertifiedBoard :=
  ⟨seed0443, by apply FastValid.valid; decide +kernel⟩

def cert0443r : CertifiedBoard :=
  ⟨seed0443.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0444 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,0,0,2,0,2,1,1,1,0,1],
  [2,0,1,1,2,0,2,1,2,0,1,1,1,0,0],
  [1,0,2,1,2,2,1,0,0,0,0,1,2,1,0,2,0],
  [0,1,0,1,2,0,1,1,0,0,2,2,0,2,2,0,0,1,0]
]

def cert0444n : CertifiedBoard :=
  ⟨seed0444, by apply FastValid.valid; decide +kernel⟩

def cert0444r : CertifiedBoard :=
  ⟨seed0444.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0445 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,0,0,2,1,1,1,0,1,1,1],
  [1,2,0,2,1,0,0,1,2,1,0,1,1,0,0],
  [2,1,2,0,0,0,0,2,2,0,1,0,2,0,2,1,2],
  [1,1,2,0,2,0,1,1,0,2,2,0,1,0,0,1,2,2,1]
]

def cert0445n : CertifiedBoard :=
  ⟨seed0445, by apply FastValid.valid; decide +kernel⟩

def cert0445r : CertifiedBoard :=
  ⟨seed0445.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0446 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,0,0,2,1,1,1,1,0,1,2],
  [1,2,0,2,2,0,0,1,2,0,2,0,1,1,2],
  [1,2,2,1,2,0,1,0,1,0,0,1,1,0,0,0,0],
  [2,2,0,2,1,0,2,0,1,1,0,2,1,2,1,0,0,2,2]
]

def cert0446n : CertifiedBoard :=
  ⟨seed0446, by apply FastValid.valid; decide +kernel⟩

def cert0446r : CertifiedBoard :=
  ⟨seed0446.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0447 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,0,0,2,1,1,1,1,0,2,1],
  [2,1,0,0,1,0,1,2,1,2,2,0,0,0,0],
  [2,0,1,0,2,0,1,1,0,1,1,2,0,2,1,2,0],
  [0,1,1,0,0,2,2,0,2,0,1,2,0,2,2,1,0,0,1]
]

def cert0447n : CertifiedBoard :=
  ⟨seed0447, by apply FastValid.valid; decide +kernel⟩

def cert0447r : CertifiedBoard :=
  ⟨seed0447.map List.reverse, by apply FastValid.valid; decide +kernel⟩

end TBoards.Extended
