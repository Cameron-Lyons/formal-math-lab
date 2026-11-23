import Extended.Batch013

/- Generated from extended_seeds.json. Published seeds 0–4:
   Qiyuan Ma, DOI 10.5281/zenodo.23631079, CC-BY-4.0. -/

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.Extended

def seed0544 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,1,2,1,0,2,1,1,2,0,1],
  [2,2,0,0,0,2,0,1,0,1,1,1,1,0,0],
  [0,1,1,0,2,1,0,0,1,0,1,2,2,0,0,2,2],
  [2,1,2,0,2,0,2,0,1,1,0,0,0,1,2,0,2,2,1]
]

def cert0544n : CertifiedBoard :=
  ⟨seed0544, by apply FastValid.valid; decide +kernel⟩

def cert0544r : CertifiedBoard :=
  ⟨seed0544.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0545 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,1,2,1,0,2,1,1,2,0,2],
  [0,2,0,0,0,0,1,2,0,1,1,1,0,1,2],
  [1,1,0,1,0,2,1,2,2,1,0,0,2,0,1,0,0],
  [1,2,0,2,2,0,2,0,1,1,1,0,0,2,2,0,0,1,1]
]

def cert0545n : CertifiedBoard :=
  ⟨seed0545, by apply FastValid.valid; decide +kernel⟩

def cert0545r : CertifiedBoard :=
  ⟨seed0545.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0546 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,1,2,1,0,2,1,1,2,0,2],
  [2,2,0,2,0,2,2,0,1,1,1,0,1,0,0],
  [0,0,1,2,0,1,1,1,0,1,2,0,0,1,1,0,0],
  [0,2,1,2,2,1,0,0,2,0,0,0,0,2,0,1,0,2,2]
]

def cert0546n : CertifiedBoard :=
  ⟨seed0546, by apply FastValid.valid; decide +kernel⟩

def cert0546r : CertifiedBoard :=
  ⟨seed0546.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0547 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,1,2,2,0,1,0,0,0,1,2],
  [0,0,1,1,1,1,2,0,0,0,2,1,2,1,1],
  [1,1,0,1,1,0,0,2,2,0,2,2,1,0,2,0,0],
  [1,2,0,2,0,1,2,0,1,1,0,2,0,2,1,0,1,0,0]
]

def cert0547n : CertifiedBoard :=
  ⟨seed0547, by apply FastValid.valid; decide +kernel⟩

def cert0547r : CertifiedBoard :=
  ⟨seed0547.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0548 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,1,2,2,0,1,0,0,1,1,0],
  [1,0,1,1,1,1,2,0,2,1,2,0,2,0,0],
  [1,0,0,1,2,0,0,2,0,1,2,1,1,0,2,2,0],
  [2,0,1,0,0,0,0,2,0,2,1,0,1,1,0,2,2,1,0]
]

def cert0548n : CertifiedBoard :=
  ⟨seed0548, by apply FastValid.valid; decide +kernel⟩

def cert0548r : CertifiedBoard :=
  ⟨seed0548.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0549 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,1,2,2,0,1,0,1,1,2,0],
  [2,0,1,1,1,1,0,2,1,0,1,2,1,1,0],
  [0,2,2,0,1,1,0,0,1,2,0,0,0,0,2,0,2],
  [1,0,2,0,2,0,2,1,2,0,0,1,0,0,2,2,1,0,0]
]

def cert0549n : CertifiedBoard :=
  ⟨seed0549, by apply FastValid.valid; decide +kernel⟩

def cert0549r : CertifiedBoard :=
  ⟨seed0549.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0550 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,1,2,2,0,1,0,1,2,0,2],
  [1,0,0,1,1,0,2,2,0,1,1,1,1,0,0],
  [0,2,1,2,0,0,2,1,1,0,1,2,1,0,0,2,0],
  [2,0,0,0,0,1,0,2,0,2,0,1,1,2,0,2,2,1,0]
]

def cert0550n : CertifiedBoard :=
  ⟨seed0550, by apply FastValid.valid; decide +kernel⟩

def cert0550r : CertifiedBoard :=
  ⟨seed0550.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0551 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,1,2,2,0,1,0,2,2,1,1],
  [2,0,1,0,1,1,1,2,0,0,1,2,0,1,2],
  [1,1,0,2,1,0,0,2,0,2,0,0,0,1,1,0,0],
  [1,2,1,0,1,1,1,0,0,0,2,0,2,1,2,0,2,2,0]
]

def cert0551n : CertifiedBoard :=
  ⟨seed0551, by apply FastValid.valid; decide +kernel⟩

def cert0551r : CertifiedBoard :=
  ⟨seed0551.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0552 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,1,2,2,0,1,1,0,2,2,1],
  [1,0,1,1,1,1,2,0,1,2,0,0,1,1,0],
  [0,2,1,2,1,0,0,0,0,2,0,2,2,0,1,0,0],
  [2,1,0,0,2,0,0,1,0,2,1,1,0,1,2,0,2,0,2]
]

def cert0552n : CertifiedBoard :=
  ⟨seed0552, by apply FastValid.valid; decide +kernel⟩

def cert0552r : CertifiedBoard :=
  ⟨seed0552.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0553 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,1,2,2,0,2,0,1,1,2,0],
  [2,0,2,1,1,1,1,0,0,0,1,1,0,1,1],
  [0,2,0,1,2,0,1,2,1,2,0,0,2,1,0,0,0],
  [1,1,0,2,0,2,2,0,0,1,0,0,2,2,1,0,1,0,2]
]

def cert0553n : CertifiedBoard :=
  ⟨seed0553, by apply FastValid.valid; decide +kernel⟩

def cert0553r : CertifiedBoard :=
  ⟨seed0553.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0554 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,1,2,2,0,2,1,1,0,1,1],
  [0,0,2,2,1,0,2,2,0,1,2,1,2,0,0],
  [1,0,1,0,0,0,0,1,2,0,1,1,1,1,2,0,0],
  [1,1,0,0,2,1,0,2,0,2,0,2,0,1,0,0,1,1,0]
]

def cert0554n : CertifiedBoard :=
  ⟨seed0554, by apply FastValid.valid; decide +kernel⟩

def cert0554r : CertifiedBoard :=
  ⟨seed0554.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0555 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,1,2,2,0,2,1,1,0,1,2],
  [0,2,1,0,0,0,0,1,1,2,1,0,1,2,0],
  [1,2,0,1,0,2,2,0,1,1,1,1,0,0,2,0,0],
  [2,0,1,1,0,0,2,2,1,2,0,2,0,0,1,0,2,0,2]
]

def cert0555n : CertifiedBoard :=
  ⟨seed0555, by apply FastValid.valid; decide +kernel⟩

def cert0555r : CertifiedBoard :=
  ⟨seed0555.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0556 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,1,2,2,0,2,1,1,0,2,2],
  [1,0,2,2,1,0,0,0,1,2,0,0,2,0,1],
  [0,1,0,1,1,2,1,2,0,1,1,1,0,0,1,0,0],
  [2,2,0,1,1,1,0,1,2,0,0,0,2,0,2,0,2,1,0]
]

def cert0556n : CertifiedBoard :=
  ⟨seed0556, by apply FastValid.valid; decide +kernel⟩

def cert0556r : CertifiedBoard :=
  ⟨seed0556.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0557 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,1,2,2,0,2,1,1,1,0,1],
  [0,1,0,1,1,1,2,0,0,0,0,2,0,1,2],
  [1,2,0,2,0,1,1,0,0,2,1,0,2,2,0,0,1],
  [0,1,0,2,2,1,2,1,0,0,1,2,0,2,0,1,1,0,0]
]

def cert0557n : CertifiedBoard :=
  ⟨seed0557, by apply FastValid.valid; decide +kernel⟩

def cert0557r : CertifiedBoard :=
  ⟨seed0557.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0558 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,1,2,2,0,2,1,1,1,2,0],
  [0,1,0,1,1,1,0,2,2,1,0,0,0,0,1],
  [1,2,0,0,2,0,1,0,0,1,2,1,0,2,0,1,2],
  [2,0,2,2,0,2,0,0,2,1,2,0,1,1,0,1,1,0,0]
]

def cert0558n : CertifiedBoard :=
  ⟨seed0558, by apply FastValid.valid; decide +kernel⟩

def cert0558r : CertifiedBoard :=
  ⟨seed0558.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0559 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,1,2,2,0,2,1,1,1,2,0],
  [2,0,1,0,1,1,0,2,2,1,0,0,0,0,2],
  [2,0,1,1,0,1,2,0,0,1,1,1,0,2,1,0,0],
  [0,2,2,0,1,0,0,2,0,2,0,2,0,0,1,2,1,2,0]
]

def cert0559n : CertifiedBoard :=
  ⟨seed0559, by apply FastValid.valid; decide +kernel⟩

def cert0559r : CertifiedBoard :=
  ⟨seed0559.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0560 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,1,2,2,0,2,1,1,2,0,1],
  [1,1,0,1,1,1,1,0,0,0,0,2,2,0,0],
  [0,1,2,1,2,0,2,0,1,0,2,0,0,1,2,0,1],
  [0,1,1,0,1,0,2,2,1,0,0,2,0,2,1,0,0,1,1]
]

def cert0560n : CertifiedBoard :=
  ⟨seed0560, by apply FastValid.valid; decide +kernel⟩

def cert0560r : CertifiedBoard :=
  ⟨seed0560.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0561 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,2,0,0,0,0,2,1,1,0,0],
  [1,1,0,2,0,2,2,0,1,1,1,0,0,2,1],
  [2,1,2,1,2,0,0,1,2,0,2,1,0,0,1,1,1],
  [2,0,1,1,2,2,1,0,1,0,1,0,2,0,2,0,1,2,0]
]

def cert0561n : CertifiedBoard :=
  ⟨seed0561, by apply FastValid.valid; decide +kernel⟩

def cert0561r : CertifiedBoard :=
  ⟨seed0561.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0562 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,2,0,0,0,0,2,1,1,1,0],
  [2,0,1,1,2,0,2,2,0,0,1,1,1,0,0],
  [1,0,0,1,2,2,1,0,1,1,0,2,1,2,1,2,0],
  [1,0,0,2,1,0,2,0,2,0,1,0,1,2,0,2,0,1,0]
]

def cert0562n : CertifiedBoard :=
  ⟨seed0562, by apply FastValid.valid; decide +kernel⟩

def cert0562r : CertifiedBoard :=
  ⟨seed0562.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0563 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,2,0,0,0,1,1,0,1,1,1],
  [0,2,0,1,2,0,0,1,1,1,0,2,1,2,0],
  [2,0,2,1,2,1,1,0,1,0,0,2,2,1,0,0,2],
  [1,1,2,0,2,0,1,2,2,0,2,1,0,2,0,1,0,0,0]
]

def cert0563n : CertifiedBoard :=
  ⟨seed0563, by apply FastValid.valid; decide +kernel⟩

def cert0563r : CertifiedBoard :=
  ⟨seed0563.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0564 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,2,0,0,0,1,1,1,0,0,0],
  [2,1,0,1,1,2,0,0,1,2,0,2,2,0,2],
  [1,2,0,1,1,1,0,1,0,2,1,1,0,2,0,1,2],
  [0,2,0,2,1,2,1,0,0,2,0,1,0,0,2,1,2,2,1]
]

def cert0564n : CertifiedBoard :=
  ⟨seed0564, by apply FastValid.valid; decide +kernel⟩

def cert0564r : CertifiedBoard :=
  ⟨seed0564.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0565 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,2,0,0,0,1,1,1,0,2,1],
  [2,2,0,2,0,2,1,2,0,2,1,0,1,1,1],
  [1,1,2,0,0,0,1,2,1,1,0,0,2,0,1,0,0],
  [2,1,2,2,1,0,0,2,0,1,2,0,1,0,1,1,0,2,2]
]

def cert0565n : CertifiedBoard :=
  ⟨seed0565, by apply FastValid.valid; decide +kernel⟩

def cert0565r : CertifiedBoard :=
  ⟨seed0565.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0566 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,2,0,0,0,1,2,0,2,0,1],
  [0,2,0,1,1,2,0,2,1,0,2,2,1,2,2],
  [0,1,1,0,1,1,1,1,0,1,0,2,1,1,0,0,0],
  [2,2,0,2,0,0,2,1,2,1,0,0,1,2,0,1,0,0,2]
]

def cert0566n : CertifiedBoard :=
  ⟨seed0566, by apply FastValid.valid; decide +kernel⟩

def cert0566r : CertifiedBoard :=
  ⟨seed0566.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0567 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,2,0,0,2,0,1,1,1,0,0],
  [1,0,2,2,1,1,0,0,1,1,1,0,0,1,0],
  [0,2,1,0,1,2,0,2,1,2,1,2,2,0,1,2,0],
  [2,0,2,1,0,1,0,2,0,2,0,1,1,2,0,0,0,0,2]
]

def cert0567n : CertifiedBoard :=
  ⟨seed0567, by apply FastValid.valid; decide +kernel⟩

def cert0567r : CertifiedBoard :=
  ⟨seed0567.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0568 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,2,0,0,2,0,1,1,1,0,0],
  [2,0,2,1,1,2,0,0,0,1,1,1,0,1,0],
  [2,2,1,0,1,0,0,1,1,0,2,1,2,1,2,2,0],
  [1,0,2,1,0,0,0,2,0,2,0,1,2,0,1,2,0,2,2]
]

def cert0568n : CertifiedBoard :=
  ⟨seed0568, by apply FastValid.valid; decide +kernel⟩

def cert0568r : CertifiedBoard :=
  ⟨seed0568.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0569 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,2,0,0,2,1,0,0,0,1,1],
  [1,1,0,2,0,1,0,1,2,2,0,1,1,0,0],
  [2,1,2,1,2,0,0,0,1,1,1,2,0,2,0,2,1],
  [1,0,2,1,1,1,0,0,2,0,1,2,0,2,2,1,0,1,0]
]

def cert0569n : CertifiedBoard :=
  ⟨seed0569, by apply FastValid.valid; decide +kernel⟩

def cert0569r : CertifiedBoard :=
  ⟨seed0569.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0570 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,2,0,0,2,1,0,1,2,0,1],
  [1,2,0,1,1,1,0,0,0,0,2,0,2,1,2],
  [0,1,0,0,1,1,1,0,2,2,0,0,1,1,2,2,1],
  [2,1,2,1,0,1,2,0,1,0,2,0,2,0,2,1,1,0,0]
]

def cert0570n : CertifiedBoard :=
  ⟨seed0570, by apply FastValid.valid; decide +kernel⟩

def cert0570r : CertifiedBoard :=
  ⟨seed0570.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0571 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,2,0,1,0,0,2,1,1,0,1],
  [1,2,0,2,0,1,1,0,2,0,2,1,0,1,2],
  [0,1,1,1,0,2,1,2,1,2,0,1,2,0,0,0,0],
  [2,2,0,2,0,0,1,1,1,2,2,1,0,0,1,0,0,2,2]
]

def cert0571n : CertifiedBoard :=
  ⟨seed0571, by apply FastValid.valid; decide +kernel⟩

def cert0571r : CertifiedBoard :=
  ⟨seed0571.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0572 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,2,0,1,0,1,1,0,0,1,1],
  [1,0,2,0,2,1,2,2,0,2,0,2,1,0,0],
  [1,1,0,0,0,1,2,1,1,1,0,2,2,1,2,0,0],
  [0,0,2,1,0,1,1,1,2,0,0,0,2,0,1,2,0,1,0]
]

def cert0572n : CertifiedBoard :=
  ⟨seed0572, by apply FastValid.valid; decide +kernel⟩

def cert0572r : CertifiedBoard :=
  ⟨seed0572.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0573 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,2,0,1,0,2,0,1,1,2,0],
  [2,0,1,1,1,0,0,2,1,1,0,0,0,1,0],
  [1,0,0,1,1,1,0,2,2,1,2,2,0,0,2,1,2],
  [1,2,1,0,1,2,0,2,0,2,1,0,1,2,0,2,0,0,0]
]

def cert0573n : CertifiedBoard :=
  ⟨seed0573, by apply FastValid.valid; decide +kernel⟩

def cert0573r : CertifiedBoard :=
  ⟨seed0573.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0574 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,2,0,1,0,2,1,1,1,0,0],
  [1,1,0,2,0,2,1,0,0,0,2,0,0,1,1],
  [1,1,0,0,2,1,2,0,2,0,2,2,1,0,1,2,1],
  [2,1,2,2,0,1,1,1,2,0,1,0,1,2,0,0,0,1,1]
]

def cert0574n : CertifiedBoard :=
  ⟨seed0574, by apply FastValid.valid; decide +kernel⟩

def cert0574r : CertifiedBoard :=
  ⟨seed0574.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0575 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,2,0,1,0,2,1,1,1,2,0],
  [1,1,0,0,0,1,0,0,1,2,1,2,0,1,1],
  [0,1,1,0,2,2,0,2,1,2,2,1,0,0,2,0,0],
  [2,0,0,0,2,0,2,0,1,1,1,0,1,2,0,2,1,0,1]
]

def cert0575n : CertifiedBoard :=
  ⟨seed0575, by apply FastValid.valid; decide +kernel⟩

def cert0575r : CertifiedBoard :=
  ⟨seed0575.map List.reverse, by apply FastValid.valid; decide +kernel⟩

end TBoards.Extended
