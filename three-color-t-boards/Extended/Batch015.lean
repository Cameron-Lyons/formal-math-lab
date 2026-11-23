import Extended.Batch011

/- Generated from extended_seeds.json. Published seeds 0–4:
   Qiyuan Ma, DOI 10.5281/zenodo.23631079, CC-BY-4.0. -/

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.Extended

def seed0480 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,0,1,2,1,1,1,2,0,1,1],
  [1,1,0,1,2,0,0,1,0,0,0,0,1,1,0],
  [2,0,2,1,2,2,1,0,0,2,2,0,2,1,2,0,0],
  [1,0,1,0,2,0,2,2,0,1,1,1,0,2,1,0,0,2,0]
]

def cert0480n : CertifiedBoard :=
  ⟨seed0480, by apply FastValid.valid; decide +kernel⟩

def cert0480r : CertifiedBoard :=
  ⟨seed0480.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0481 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,0,1,2,2,1,0,1,1,0,0],
  [1,0,1,1,2,0,2,1,1,1,0,0,0,1,0],
  [0,2,1,2,1,2,0,1,2,0,0,2,1,0,2,0,2],
  [2,2,0,1,1,1,0,2,2,0,2,0,0,1,0,0,0,2,2]
]

def cert0481n : CertifiedBoard :=
  ⟨seed0481, by apply FastValid.valid; decide +kernel⟩

def cert0481r : CertifiedBoard :=
  ⟨seed0481.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0482 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,0,1,2,2,1,0,1,1,2,0],
  [2,0,1,0,2,0,0,0,1,0,1,1,1,0,0],
  [2,1,1,0,0,1,2,0,0,2,1,2,1,2,0,2,1],
  [1,0,0,0,2,2,0,2,1,0,2,2,0,2,0,1,1,1,0]
]

def cert0482n : CertifiedBoard :=
  ⟨seed0482, by apply FastValid.valid; decide +kernel⟩

def cert0482r : CertifiedBoard :=
  ⟨seed0482.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0483 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,0,1,2,2,1,0,2,1,1,0],
  [0,1,0,0,1,1,1,1,2,1,0,1,1,0,2],
  [0,2,2,0,0,1,0,0,2,0,2,1,2,0,2,0,1],
  [1,0,1,2,0,2,1,2,0,1,1,0,0,0,0,2,2,0,0]
]

def cert0483n : CertifiedBoard :=
  ⟨seed0483, by apply FastValid.valid; decide +kernel⟩

def cert0483r : CertifiedBoard :=
  ⟨seed0483.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0484 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,0,1,2,2,1,0,2,1,1,2],
  [1,0,1,1,0,0,0,1,1,1,0,1,0,0,0],
  [1,2,1,2,0,2,2,0,0,2,1,2,0,0,2,1,0],
  [0,1,1,1,0,0,1,2,0,2,0,2,0,1,0,2,2,0,1]
]

def cert0484n : CertifiedBoard :=
  ⟨seed0484, by apply FastValid.valid; decide +kernel⟩

def cert0484r : CertifiedBoard :=
  ⟨seed0484.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0485 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,0,1,2,2,1,2,0,2,1,1],
  [0,2,1,0,1,1,1,1,2,0,1,0,2,0,2],
  [2,0,2,2,0,1,1,0,0,0,0,1,0,1,1,0,0],
  [1,1,0,0,1,2,0,0,2,2,0,0,2,1,2,1,0,2,0]
]

def cert0485n : CertifiedBoard :=
  ⟨seed0485, by apply FastValid.valid; decide +kernel⟩

def cert0485r : CertifiedBoard :=
  ⟨seed0485.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0486 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,0,2,0,0,0,2,2,1,1,0],
  [1,2,0,2,1,0,1,0,2,0,1,2,1,0,0],
  [0,1,1,1,0,2,1,2,0,0,1,1,1,2,2,0,1],
  [1,0,1,0,0,0,1,1,0,0,2,2,0,1,2,0,2,1,2]
]

def cert0486n : CertifiedBoard :=
  ⟨seed0486, by apply FastValid.valid; decide +kernel⟩

def cert0486r : CertifiedBoard :=
  ⟨seed0486.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0487 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,0,2,0,0,0,2,2,1,1,1],
  [1,1,0,0,1,0,2,2,0,1,1,2,1,0,0],
  [2,0,1,2,0,2,1,2,0,1,1,1,0,1,0,2,0],
  [1,0,0,1,1,0,1,2,0,2,1,2,2,0,0,0,2,1,0]
]

def cert0487n : CertifiedBoard :=
  ⟨seed0487, by apply FastValid.valid; decide +kernel⟩

def cert0487r : CertifiedBoard :=
  ⟨seed0487.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0488 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,0,2,0,0,0,2,2,1,1,2],
  [1,1,0,0,1,1,0,2,0,1,1,1,1,0,0],
  [1,2,2,0,0,1,2,0,2,1,2,1,0,0,0,2,1],
  [2,1,2,0,2,2,0,1,2,0,1,0,2,1,0,1,0,1,1]
]

def cert0488n : CertifiedBoard :=
  ⟨seed0488, by apply FastValid.valid; decide +kernel⟩

def cert0488r : CertifiedBoard :=
  ⟨seed0488.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0489 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,0,2,0,0,1,0,1,1,2,0],
  [1,0,2,2,1,0,0,2,1,0,0,2,1,1,0],
  [0,1,2,0,1,2,2,0,2,2,0,1,1,1,1,0,1],
  [2,0,0,0,0,1,1,0,2,0,2,1,2,1,2,0,1,0,0]
]

def cert0489n : CertifiedBoard :=
  ⟨seed0489, by apply FastValid.valid; decide +kernel⟩

def cert0489r : CertifiedBoard :=
  ⟨seed0489.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0490 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,0,2,0,1,1,1,1,2,0,1],
  [1,2,0,2,2,0,2,1,2,0,0,0,0,2,1],
  [0,1,1,0,2,1,1,0,1,0,2,0,1,0,0,1,2],
  [2,1,2,1,0,1,2,2,0,0,2,2,1,0,0,1,1,0,0]
]

def cert0490n : CertifiedBoard :=
  ⟨seed0490, by apply FastValid.valid; decide +kernel⟩

def cert0490r : CertifiedBoard :=
  ⟨seed0490.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0491 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,0,2,0,1,2,0,2,1,1,2],
  [0,1,0,2,2,0,1,1,1,1,0,2,1,0,1],
  [2,0,0,0,1,1,0,1,1,0,0,2,2,1,2,0,0],
  [1,2,0,2,1,2,2,0,1,2,1,0,0,0,1,0,0,2,0]
]

def cert0491n : CertifiedBoard :=
  ⟨seed0491, by apply FastValid.valid; decide +kernel⟩

def cert0491r : CertifiedBoard :=
  ⟨seed0491.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0492 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,0,2,0,1,2,1,1,0,0,1],
  [2,0,2,2,1,2,0,1,1,1,1,0,2,0,0],
  [0,1,1,0,2,1,0,1,0,0,2,1,2,0,2,1,0],
  [1,0,1,2,0,0,0,0,1,0,0,2,2,0,1,1,2,2,0]
]

def cert0492n : CertifiedBoard :=
  ⟨seed0492, by apply FastValid.valid; decide +kernel⟩

def cert0492r : CertifiedBoard :=
  ⟨seed0492.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0493 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,0,2,0,1,2,2,1,1,0,0],
  [2,1,0,2,2,0,2,0,0,0,1,2,0,2,1],
  [0,2,1,0,1,1,2,0,1,0,0,1,0,1,1,1,1],
  [1,1,0,2,1,2,1,2,0,0,0,2,2,0,1,1,0,0,2]
]

def cert0493n : CertifiedBoard :=
  ⟨seed0493, by apply FastValid.valid; decide +kernel⟩

def cert0493r : CertifiedBoard :=
  ⟨seed0493.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0494 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,0,2,0,1,2,2,1,1,1,2],
  [0,0,1,1,0,2,1,2,0,1,1,1,0,0,0],
  [2,2,0,0,2,1,0,1,0,2,1,2,1,0,1,0,0],
  [1,2,0,2,0,2,2,0,1,1,0,0,0,1,2,0,0,2,2]
]

def cert0494n : CertifiedBoard :=
  ⟨seed0494, by apply FastValid.valid; decide +kernel⟩

def cert0494r : CertifiedBoard :=
  ⟨seed0494.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0495 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,0,2,0,1,2,2,1,1,1,2],
  [1,2,0,2,1,2,0,0,0,0,1,2,1,0,1],
  [0,1,1,0,1,1,0,0,1,0,2,2,0,2,1,0,0],
  [0,2,0,0,2,1,2,0,1,1,1,0,2,2,0,1,0,0,2]
]

def cert0495n : CertifiedBoard :=
  ⟨seed0495, by apply FastValid.valid; decide +kernel⟩

def cert0495r : CertifiedBoard :=
  ⟨seed0495.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0496 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,0,2,1,0,0,2,2,1,1,1],
  [0,2,1,2,0,1,2,1,0,1,1,2,0,0,0],
  [1,1,0,2,0,1,0,0,1,2,0,1,1,0,2,0,2],
  [2,1,2,2,0,2,2,0,0,1,0,1,1,1,0,0,0,2,1]
]

def cert0496n : CertifiedBoard :=
  ⟨seed0496, by apply FastValid.valid; decide +kernel⟩

def cert0496r : CertifiedBoard :=
  ⟨seed0496.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0497 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,0,2,1,0,0,2,2,1,1,2],
  [0,0,1,1,0,1,2,1,0,0,0,1,1,1,1],
  [1,2,0,1,2,0,2,0,1,0,2,1,2,2,0,0,0],
  [1,1,0,2,0,1,1,0,1,0,0,2,1,2,0,2,2,0,0]
]

def cert0497n : CertifiedBoard :=
  ⟨seed0497, by apply FastValid.valid; decide +kernel⟩

def cert0497r : CertifiedBoard :=
  ⟨seed0497.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0498 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,0,2,1,0,1,1,0,2,1,1],
  [2,1,0,2,2,0,1,2,0,1,0,1,1,0,0],
  [1,1,1,1,0,0,0,2,0,2,2,0,0,0,2,1,2],
  [1,2,1,2,0,0,1,0,0,1,1,2,0,2,0,1,2,2,1]
]

def cert0498n : CertifiedBoard :=
  ⟨seed0498, by apply FastValid.valid; decide +kernel⟩

def cert0498r : CertifiedBoard :=
  ⟨seed0498.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0499 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,0,2,1,2,0,1,1,1,0,2],
  [2,0,2,1,1,0,1,0,0,1,2,1,0,1,2],
  [0,2,2,0,1,1,0,2,0,1,1,1,2,0,0,0,0],
  [1,2,0,2,1,0,0,2,2,1,2,2,0,0,1,0,0,2,0]
]

def cert0499n : CertifiedBoard :=
  ⟨seed0499, by apply FastValid.valid; decide +kernel⟩

def cert0499r : CertifiedBoard :=
  ⟨seed0499.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0500 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,1,0,0,0,0,2,0,2,2,1],
  [0,2,0,1,2,2,0,2,1,2,0,0,1,1,1],
  [2,1,0,0,1,1,0,1,1,2,1,1,0,1,2,0,0],
  [1,1,1,0,0,2,1,2,0,1,0,2,0,2,2,0,1,0,2]
]

def cert0500n : CertifiedBoard :=
  ⟨seed0500, by apply FastValid.valid; decide +kernel⟩

def cert0500r : CertifiedBoard :=
  ⟨seed0500.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0501 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,1,0,0,0,0,2,2,1,1,2],
  [0,1,1,0,1,0,0,2,0,1,1,1,1,0,0],
  [2,1,2,1,2,0,2,1,0,2,2,0,1,2,0,0,1],
  [1,2,0,0,1,1,0,1,2,2,0,2,0,2,0,1,0,2,1]
]

def cert0501n : CertifiedBoard :=
  ⟨seed0501, by apply FastValid.valid; decide +kernel⟩

def cert0501r : CertifiedBoard :=
  ⟨seed0501.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0502 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,1,0,0,0,0,2,2,1,1,2],
  [0,2,1,2,0,0,1,1,0,0,1,1,1,0,2],
  [1,2,0,1,0,1,0,1,2,2,0,2,1,2,1,0,0],
  [0,2,0,2,0,2,2,0,1,1,1,0,2,0,1,2,0,0,2]
]

def cert0502n : CertifiedBoard :=
  ⟨seed0502, by apply FastValid.valid; decide +kernel⟩

def cert0502r : CertifiedBoard :=
  ⟨seed0502.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0503 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,1,0,0,0,1,1,0,1,1,1],
  [1,1,0,1,2,0,2,2,0,1,0,0,2,0,0],
  [2,1,2,1,2,2,1,0,2,0,1,2,0,0,0,2,1],
  [2,0,2,1,1,1,2,0,2,0,1,1,0,0,1,0,2,2,0]
]

def cert0503n : CertifiedBoard :=
  ⟨seed0503, by apply FastValid.valid; decide +kernel⟩

def cert0503r : CertifiedBoard :=
  ⟨seed0503.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0504 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,1,0,0,0,1,1,1,0,0,0],
  [2,1,0,2,0,2,0,0,2,1,2,1,2,0,2],
  [1,2,0,1,0,2,1,1,0,1,2,0,1,0,1,1,2],
  [0,2,0,2,2,0,1,1,1,0,0,2,2,0,0,1,2,2,1]
]

def cert0504n : CertifiedBoard :=
  ⟨seed0504, by apply FastValid.valid; decide +kernel⟩

def cert0504r : CertifiedBoard :=
  ⟨seed0504.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0505 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,1,0,0,0,1,1,1,2,0,1],
  [0,2,0,1,2,0,2,1,2,2,0,2,2,0,0],
  [0,1,0,1,1,0,0,1,1,1,0,2,2,1,1,0,2],
  [0,0,2,0,0,2,1,0,1,2,1,2,0,2,0,1,0,0,0]
]

def cert0505n : CertifiedBoard :=
  ⟨seed0505, by apply FastValid.valid; decide +kernel⟩

def cert0505r : CertifiedBoard :=
  ⟨seed0505.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0506 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,1,0,0,0,1,2,0,1,1,1],
  [2,1,2,0,2,0,0,1,1,1,0,2,1,2,1],
  [1,1,2,2,1,0,0,2,2,0,1,0,0,0,2,0,0],
  [0,1,1,0,1,2,0,1,0,2,2,0,2,0,2,1,1,0,1]
]

def cert0506n : CertifiedBoard :=
  ⟨seed0506, by apply FastValid.valid; decide +kernel⟩

def cert0506r : CertifiedBoard :=
  ⟨seed0506.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0507 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,1,0,0,2,2,0,1,1,0,1],
  [2,0,1,0,2,0,2,1,1,2,0,1,0,0,0],
  [2,2,1,2,0,0,1,1,1,1,0,0,1,1,0,2,2],
  [0,1,2,0,0,0,2,0,2,1,2,1,0,1,2,2,0,2,0]
]

def cert0507n : CertifiedBoard :=
  ⟨seed0507, by apply FastValid.valid; decide +kernel⟩

def cert0507r : CertifiedBoard :=
  ⟨seed0507.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0508 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,1,0,0,2,2,0,1,1,1,2],
  [0,1,1,0,1,0,2,0,2,0,1,1,1,0,0],
  [0,0,1,2,2,0,2,2,1,0,2,1,2,0,1,0,1],
  [1,2,0,2,1,1,0,0,1,2,1,2,0,0,0,2,0,0,0]
]

def cert0508n : CertifiedBoard :=
  ⟨seed0508, by apply FastValid.valid; decide +kernel⟩

def cert0508r : CertifiedBoard :=
  ⟨seed0508.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0509 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,1,2,0,0,0,2,2,1,1,1],
  [1,1,0,0,1,0,2,1,0,2,0,1,1,0,0],
  [2,2,0,2,0,0,0,1,2,1,2,0,2,1,0,1,1],
  [1,1,0,1,0,0,2,2,0,1,1,1,2,0,2,0,1,2,2]
]

def cert0509n : CertifiedBoard :=
  ⟨seed0509, by apply FastValid.valid; decide +kernel⟩

def cert0509r : CertifiedBoard :=
  ⟨seed0509.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0510 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,1,2,0,0,1,0,1,1,1,2],
  [0,1,0,2,2,0,2,0,2,0,1,1,1,0,0],
  [1,2,0,1,1,0,2,2,1,2,0,0,0,2,1,0,1],
  [1,0,0,0,1,2,2,0,1,2,1,1,0,0,2,0,2,1,0]
]

def cert0510n : CertifiedBoard :=
  ⟨seed0510, by apply FastValid.valid; decide +kernel⟩

def cert0510r : CertifiedBoard :=
  ⟨seed0510.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0511 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,1,2,0,0,1,0,1,1,2,0],
  [2,0,1,1,1,1,0,2,2,0,0,2,0,1,0],
  [1,0,2,0,1,1,0,0,2,2,1,0,1,2,0,2,1],
  [2,1,0,0,0,1,2,2,0,2,0,2,1,2,1,1,0,0,0]
]

def cert0511n : CertifiedBoard :=
  ⟨seed0511, by apply FastValid.valid; decide +kernel⟩

def cert0511r : CertifiedBoard :=
  ⟨seed0511.map List.reverse, by apply FastValid.valid; decide +kernel⟩

end TBoards.Extended
