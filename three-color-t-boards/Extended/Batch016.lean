import Extended.Batch012

/- Generated from extended_seeds.json. Published seeds 0–4:
   Qiyuan Ma, DOI 10.5281/zenodo.23631079, CC-BY-4.0. -/

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.Extended

def seed0512 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,1,2,0,0,1,1,1,0,0,0],
  [1,1,0,1,2,2,1,0,0,0,2,0,0,2,1],
  [2,1,0,0,1,2,0,2,1,2,0,2,0,1,1,2,1],
  [2,1,1,0,2,0,2,2,0,1,0,1,0,2,2,0,1,1,1]
]

def cert0512n : CertifiedBoard :=
  ⟨seed0512, by apply FastValid.valid; decide +kernel⟩

def cert0512r : CertifiedBoard :=
  ⟨seed0512.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0513 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,1,2,0,0,1,1,2,0,1,1],
  [2,2,0,1,2,2,1,2,0,2,0,2,1,0,0],
  [1,0,2,0,2,1,1,1,0,1,1,0,0,0,0,1,0],
  [1,1,1,0,0,2,2,0,1,0,1,2,1,0,2,0,0,2,2]
]

def cert0513n : CertifiedBoard :=
  ⟨seed0513, by apply FastValid.valid; decide +kernel⟩

def cert0513r : CertifiedBoard :=
  ⟨seed0513.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0514 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,1,2,0,1,2,1,1,1,2,0],
  [1,2,0,1,1,1,0,1,0,1,1,0,0,1,0],
  [2,0,0,0,1,2,2,0,0,0,2,0,2,0,2,1,2],
  [1,0,2,1,0,0,2,0,1,1,0,2,2,0,2,2,1,0,0]
]

def cert0514n : CertifiedBoard :=
  ⟨seed0514, by apply FastValid.valid; decide +kernel⟩

def cert0514r : CertifiedBoard :=
  ⟨seed0514.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0515 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,1,2,0,1,2,1,1,2,0,1],
  [2,0,2,2,1,0,2,0,2,2,0,0,0,1,1],
  [1,1,0,0,1,1,1,0,0,2,0,2,1,0,1,0,0],
  [0,1,2,2,0,0,0,2,0,1,0,1,1,1,0,2,1,2,0]
]

def cert0515n : CertifiedBoard :=
  ⟨seed0515, by apply FastValid.valid; decide +kernel⟩

def cert0515r : CertifiedBoard :=
  ⟨seed0515.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0516 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,1,2,0,1,2,1,1,2,0,2],
  [1,2,0,0,1,0,2,1,0,0,2,0,1,0,1],
  [0,1,1,0,1,1,0,2,0,0,2,2,1,0,0,1,2],
  [0,2,0,2,1,2,2,0,2,2,0,1,1,1,1,0,0,0,0]
]

def cert0516n : CertifiedBoard :=
  ⟨seed0516, by apply FastValid.valid; decide +kernel⟩

def cert0516r : CertifiedBoard :=
  ⟨seed0516.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0517 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,1,2,0,1,2,2,1,1,0,1],
  [1,0,1,1,1,1,2,0,0,0,1,1,0,2,0],
  [2,0,2,1,0,0,0,2,0,2,0,1,2,1,2,0,0],
  [0,1,1,0,2,1,0,0,2,2,0,2,2,0,1,0,0,1,0]
]

def cert0517n : CertifiedBoard :=
  ⟨seed0517, by apply FastValid.valid; decide +kernel⟩

def cert0517r : CertifiedBoard :=
  ⟨seed0517.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0518 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,1,2,0,1,2,2,1,1,1,0],
  [0,2,1,2,0,2,2,0,0,0,1,2,1,0,1],
  [0,1,0,1,0,0,1,1,2,0,2,2,0,1,1,0,0],
  [1,0,0,0,2,0,1,1,1,0,2,0,2,0,0,2,1,0,2]
]

def cert0518n : CertifiedBoard :=
  ⟨seed0518, by apply FastValid.valid; decide +kernel⟩

def cert0518r : CertifiedBoard :=
  ⟨seed0518.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0519 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,1,2,0,1,2,2,1,1,1,2],
  [1,2,0,0,1,0,1,1,1,0,2,0,0,0,0],
  [2,0,2,0,2,1,0,1,1,0,0,1,1,0,2,2,0],
  [2,0,1,0,0,2,2,0,1,2,1,0,0,2,1,2,0,2,0]
]

def cert0519n : CertifiedBoard :=
  ⟨seed0519, by apply FastValid.valid; decide +kernel⟩

def cert0519r : CertifiedBoard :=
  ⟨seed0519.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0520 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,1,2,0,1,2,2,1,1,1,2],
  [2,0,0,2,0,0,1,1,1,0,1,1,0,0,0],
  [1,2,0,2,0,1,0,1,2,1,0,2,0,2,1,0,0],
  [0,0,2,2,0,2,2,0,1,0,0,0,1,1,0,2,1,2,0]
]

def cert0520n : CertifiedBoard :=
  ⟨seed0520, by apply FastValid.valid; decide +kernel⟩

def cert0520r : CertifiedBoard :=
  ⟨seed0520.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0521 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,1,2,0,2,0,0,1,1,1,2],
  [1,2,0,1,2,2,1,2,0,0,1,1,1,0,1],
  [0,1,0,0,2,0,2,2,0,1,0,1,2,1,0,0,0],
  [0,2,0,1,1,0,2,1,1,0,2,1,0,0,0,2,2,0,2]
]

def cert0521n : CertifiedBoard :=
  ⟨seed0521, by apply FastValid.valid; decide +kernel⟩

def cert0521r : CertifiedBoard :=
  ⟨seed0521.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0522 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,1,2,0,2,0,0,1,1,1,2],
  [1,2,0,1,2,2,1,2,0,0,1,1,1,0,1],
  [0,1,0,0,2,0,2,2,0,1,0,1,2,1,0,0,0],
  [2,2,0,1,1,0,2,1,1,0,2,1,0,0,0,2,0,2,2]
]

def cert0522n : CertifiedBoard :=
  ⟨seed0522, by apply FastValid.valid; decide +kernel⟩

def cert0522r : CertifiedBoard :=
  ⟨seed0522.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0523 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,1,2,0,2,2,0,1,1,1,2],
  [1,0,2,2,1,0,2,1,1,0,1,0,0,0,0],
  [0,2,1,0,0,1,1,0,1,2,1,2,2,0,0,1,0],
  [1,2,0,2,0,1,1,1,0,0,2,0,1,2,0,2,0,0,2]
]

def cert0523n : CertifiedBoard :=
  ⟨seed0523, by apply FastValid.valid; decide +kernel⟩

def cert0523r : CertifiedBoard :=
  ⟨seed0523.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0524 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,1,2,1,0,0,0,0,1,1,1],
  [1,0,0,2,2,0,2,0,2,1,0,1,2,0,0],
  [1,1,0,2,2,1,1,0,1,1,2,2,0,1,2,0,0],
  [0,0,2,1,2,0,1,0,0,1,1,1,0,2,0,2,0,1,0]
]

def cert0524n : CertifiedBoard :=
  ⟨seed0524, by apply FastValid.valid; decide +kernel⟩

def cert0524r : CertifiedBoard :=
  ⟨seed0524.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0525 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,1,2,1,0,0,0,1,1,0,1],
  [0,1,0,0,0,2,0,2,0,1,1,1,0,2,1],
  [2,1,2,2,0,2,1,1,0,2,2,0,1,0,1,2,0],
  [2,0,1,1,1,2,0,2,0,0,2,2,1,0,0,1,2,0,0]
]

def cert0525n : CertifiedBoard :=
  ⟨seed0525, by apply FastValid.valid; decide +kernel⟩

def cert0525r : CertifiedBoard :=
  ⟨seed0525.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0526 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,1,2,1,0,0,0,1,1,0,2],
  [1,0,1,0,1,1,2,2,0,2,0,2,1,2,0],
  [2,0,0,1,0,0,2,0,1,2,0,2,1,1,1,1,0],
  [0,2,0,1,1,0,2,2,1,0,0,0,2,2,0,1,2,0,0]
]

def cert0526n : CertifiedBoard :=
  ⟨seed0526, by apply FastValid.valid; decide +kernel⟩

def cert0526r : CertifiedBoard :=
  ⟨seed0526.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0527 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,1,2,1,0,0,0,1,1,1,0],
  [1,0,2,1,1,0,2,0,0,2,2,0,2,1,2],
  [1,1,1,0,1,2,2,0,1,0,1,2,0,2,0,0,0],
  [1,2,0,1,0,0,2,2,1,0,0,1,1,2,0,2,0,1,1]
]

def cert0527n : CertifiedBoard :=
  ⟨seed0527, by apply FastValid.valid; decide +kernel⟩

def cert0527r : CertifiedBoard :=
  ⟨seed0527.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0528 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,1,2,1,0,0,0,1,1,2,0],
  [0,1,0,2,2,0,2,1,2,0,2,0,0,0,1],
  [2,0,0,2,1,1,1,0,1,0,2,2,1,0,1,1,1],
  [1,1,0,0,2,0,1,2,2,0,2,0,1,2,0,1,1,0,0]
]

def cert0528n : CertifiedBoard :=
  ⟨seed0528, by apply FastValid.valid; decide +kernel⟩

def cert0528r : CertifiedBoard :=
  ⟨seed0528.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0529 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,1,2,1,0,0,0,1,2,0,1],
  [0,1,0,0,0,2,0,2,0,1,1,1,0,2,1],
  [2,1,2,2,0,2,1,1,0,2,2,0,1,0,1,1,0],
  [1,0,1,1,1,2,0,2,0,0,2,2,1,0,0,1,2,0,0]
]

def cert0529n : CertifiedBoard :=
  ⟨seed0529, by apply FastValid.valid; decide +kernel⟩

def cert0529r : CertifiedBoard :=
  ⟨seed0529.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0530 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,1,2,1,0,0,0,1,2,0,1],
  [2,0,2,1,1,1,2,0,1,0,1,1,1,0,0],
  [1,1,0,2,2,0,1,0,2,0,0,2,0,2,1,2,0],
  [0,1,2,2,0,2,0,0,2,2,1,0,0,0,1,1,0,1,1]
]

def cert0530n : CertifiedBoard :=
  ⟨seed0530, by apply FastValid.valid; decide +kernel⟩

def cert0530r : CertifiedBoard :=
  ⟨seed0530.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0531 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,1,2,1,0,0,2,0,1,1,0],
  [1,0,1,0,1,1,1,0,2,2,1,2,2,0,0],
  [0,2,1,0,0,1,2,0,1,1,2,0,0,1,2,0,2],
  [0,2,1,1,1,0,0,0,0,2,0,2,2,0,1,0,2,0,2]
]

def cert0531n : CertifiedBoard :=
  ⟨seed0531, by apply FastValid.valid; decide +kernel⟩

def cert0531r : CertifiedBoard :=
  ⟨seed0531.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0532 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,1,2,1,0,0,2,2,1,1,0],
  [0,2,1,0,1,2,0,2,2,0,1,1,1,0,2],
  [1,0,0,1,0,1,1,1,0,2,0,2,0,0,0,1,2],
  [1,2,0,0,2,1,2,2,0,1,1,2,0,2,0,1,0,0,0]
]

def cert0532n : CertifiedBoard :=
  ⟨seed0532, by apply FastValid.valid; decide +kernel⟩

def cert0532r : CertifiedBoard :=
  ⟨seed0532.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0533 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,1,2,1,0,0,2,2,1,1,1],
  [1,0,0,2,0,1,2,2,0,0,0,1,2,0,0],
  [1,1,0,1,0,1,1,1,0,2,0,2,2,0,2,1,0],
  [1,0,0,0,1,0,2,0,2,1,2,0,1,1,2,0,1,1,0]
]

def cert0533n : CertifiedBoard :=
  ⟨seed0533, by apply FastValid.valid; decide +kernel⟩

def cert0533r : CertifiedBoard :=
  ⟨seed0533.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0534 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,1,2,1,0,0,2,2,1,1,1],
  [2,1,0,2,0,1,1,1,0,0,0,1,0,0,0],
  [1,1,2,0,1,2,0,2,0,0,2,1,2,2,0,0,1],
  [0,1,1,0,2,2,0,1,1,0,1,0,1,2,0,2,0,2,1]
]

def cert0534n : CertifiedBoard :=
  ⟨seed0534, by apply FastValid.valid; decide +kernel⟩

def cert0534r : CertifiedBoard :=
  ⟨seed0534.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0535 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,1,2,1,0,1,0,0,0,1,2],
  [1,1,0,1,1,1,2,2,0,2,0,0,1,1,1],
  [0,0,2,1,2,0,1,2,0,2,2,1,0,2,0,0,0],
  [1,2,0,2,2,0,1,1,0,2,1,1,0,0,2,0,1,0,0]
]

def cert0535n : CertifiedBoard :=
  ⟨seed0535, by apply FastValid.valid; decide +kernel⟩

def cert0535r : CertifiedBoard :=
  ⟨seed0535.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0536 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,1,2,1,0,1,1,1,0,0,0],
  [2,1,0,1,1,1,2,0,1,2,2,0,0,2,1],
  [2,0,1,0,0,0,2,1,1,0,0,1,2,0,2,0,2],
  [0,2,2,0,1,0,2,0,2,0,0,1,1,0,2,2,1,2,0]
]

def cert0536n : CertifiedBoard :=
  ⟨seed0536, by apply FastValid.valid; decide +kernel⟩

def cert0536r : CertifiedBoard :=
  ⟨seed0536.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0537 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,1,2,1,0,1,2,0,2,2,1],
  [0,1,0,1,1,0,2,1,0,0,1,1,0,0,0],
  [2,1,2,2,0,0,2,1,1,1,0,2,0,2,0,0,1],
  [2,0,1,1,1,2,0,1,2,0,1,0,0,0,2,0,2,2,0]
]

def cert0537n : CertifiedBoard :=
  ⟨seed0537, by apply FastValid.valid; decide +kernel⟩

def cert0537r : CertifiedBoard :=
  ⟨seed0537.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0538 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,1,2,1,0,2,0,2,2,1,1],
  [0,2,1,2,0,0,1,0,0,0,1,1,1,0,0],
  [1,1,0,1,1,2,0,2,1,0,2,0,1,2,0,0,2],
  [0,0,0,2,2,0,2,0,1,2,2,0,1,1,1,0,1,0,0]
]

def cert0538n : CertifiedBoard :=
  ⟨seed0538, by apply FastValid.valid; decide +kernel⟩

def cert0538r : CertifiedBoard :=
  ⟨seed0538.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0539 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,1,2,1,0,2,1,1,0,0,0],
  [2,1,0,2,0,1,1,1,0,1,1,0,1,0,0],
  [1,2,0,2,2,1,2,2,0,0,1,0,0,2,0,2,1],
  [0,0,0,1,1,1,2,0,2,2,0,0,2,0,1,2,0,1,2]
]

def cert0539n : CertifiedBoard :=
  ⟨seed0539, by apply FastValid.valid; decide +kernel⟩

def cert0539r : CertifiedBoard :=
  ⟨seed0539.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0540 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,1,2,1,0,2,1,1,0,0,0],
  [2,1,2,0,1,2,0,1,1,1,1,0,0,2,1],
  [1,1,2,0,2,0,0,1,0,0,0,2,0,0,1,2,2],
  [2,2,0,2,0,2,2,0,1,1,0,2,2,1,0,1,0,1,1]
]

def cert0540n : CertifiedBoard :=
  ⟨seed0540, by apply FastValid.valid; decide +kernel⟩

def cert0540r : CertifiedBoard :=
  ⟨seed0540.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0541 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,1,2,1,0,2,1,1,1,0,1],
  [0,2,1,2,0,1,2,2,0,1,1,1,0,1,0],
  [0,1,1,2,0,2,0,0,0,1,0,0,0,2,2,0,2],
  [1,0,2,0,2,0,1,1,0,0,1,2,0,0,2,2,1,0,0]
]

def cert0541n : CertifiedBoard :=
  ⟨seed0541, by apply FastValid.valid; decide +kernel⟩

def cert0541r : CertifiedBoard :=
  ⟨seed0541.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0542 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,1,2,1,0,2,1,1,1,0,1],
  [1,1,0,0,0,2,2,0,2,0,2,0,0,1,0],
  [0,1,1,0,2,1,2,0,2,2,1,0,0,2,0,1,1],
  [1,0,1,2,0,1,1,1,2,0,1,2,2,0,0,1,0,0,0]
]

def cert0542n : CertifiedBoard :=
  ⟨seed0542, by apply FastValid.valid; decide +kernel⟩

def cert0542r : CertifiedBoard :=
  ⟨seed0542.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0543 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,1,2,1,0,2,1,1,2,0,1],
  [2,1,0,0,1,0,0,2,0,2,0,2,0,0,0],
  [1,1,1,0,2,2,0,1,0,1,1,0,1,2,0,2,1],
  [0,1,2,0,0,2,2,1,2,2,0,1,1,0,0,0,1,1,1]
]

def cert0543n : CertifiedBoard :=
  ⟨seed0543, by apply FastValid.valid; decide +kernel⟩

def cert0543r : CertifiedBoard :=
  ⟨seed0543.map List.reverse, by apply FastValid.valid; decide +kernel⟩

end TBoards.Extended
