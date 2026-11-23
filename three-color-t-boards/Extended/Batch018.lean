import Extended.Batch014

/- Generated from extended_seeds.json. Published seeds 0–4:
   Qiyuan Ma, DOI 10.5281/zenodo.23631079, CC-BY-4.0. -/

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.Extended

def seed0576 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,2,0,1,1,1,0,0,0,1,1],
  [0,1,0,2,1,1,0,0,2,1,2,0,1,2,2],
  [2,2,0,0,2,0,2,0,0,1,2,0,1,1,1,0,1],
  [1,1,2,0,2,0,2,2,1,0,1,0,2,1,2,1,0,0,0]
]

def cert0576n : CertifiedBoard :=
  ⟨seed0576, by apply FastValid.valid; decide +kernel⟩

def cert0576r : CertifiedBoard :=
  ⟨seed0576.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0577 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,2,0,1,1,1,0,1,2,0,2],
  [0,2,1,0,2,0,1,2,1,0,0,0,0,1,1],
  [1,1,0,0,2,2,1,2,0,1,0,1,0,2,0,2,1],
  [2,1,2,2,0,2,1,1,1,2,0,0,2,0,0,1,1,0,0]
]

def cert0577n : CertifiedBoard :=
  ⟨seed0577, by apply FastValid.valid; decide +kernel⟩

def cert0577r : CertifiedBoard :=
  ⟨seed0577.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0578 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,2,0,1,1,1,1,0,0,1,2],
  [2,1,0,2,1,1,0,0,2,1,2,0,0,0,0],
  [1,2,0,2,0,1,2,2,0,1,1,0,1,0,0,2,1],
  [2,1,0,2,2,1,2,0,2,0,2,0,0,1,0,1,1,2,1]
]

def cert0578n : CertifiedBoard :=
  ⟨seed0578, by apply FastValid.valid; decide +kernel⟩

def cert0578r : CertifiedBoard :=
  ⟨seed0578.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0579 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,2,0,1,1,1,1,0,2,1,1],
  [2,1,0,0,0,1,1,0,0,2,1,2,0,0,0],
  [1,1,2,2,0,0,1,2,0,2,0,2,0,1,0,2,1],
  [1,2,1,0,1,1,0,1,0,0,2,0,1,2,0,2,2,1,2]
]

def cert0579n : CertifiedBoard :=
  ⟨seed0579, by apply FastValid.valid; decide +kernel⟩

def cert0579r : CertifiedBoard :=
  ⟨seed0579.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0580 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,2,0,1,1,1,1,2,0,1,1],
  [1,1,0,2,0,2,0,2,1,2,2,1,2,1,0],
  [0,0,2,0,2,1,0,2,1,1,0,0,0,0,1,0,0],
  [1,0,1,0,1,1,0,0,1,2,0,0,2,2,0,1,2,0,0]
]

def cert0580n : CertifiedBoard :=
  ⟨seed0580, by apply FastValid.valid; decide +kernel⟩

def cert0580r : CertifiedBoard :=
  ⟨seed0580.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0581 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,2,0,1,1,1,1,2,0,1,2],
  [2,1,0,1,1,0,0,2,0,2,1,1,0,0,0],
  [1,0,1,2,0,0,0,1,0,0,2,1,2,2,0,2,1],
  [1,2,1,2,0,2,0,1,1,0,2,2,1,0,2,0,0,1,0]
]

def cert0581n : CertifiedBoard :=
  ⟨seed0581, by apply FastValid.valid; decide +kernel⟩

def cert0581r : CertifiedBoard :=
  ⟨seed0581.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0582 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,2,0,1,1,2,0,2,1,1,1],
  [1,2,0,2,0,1,1,0,0,1,0,2,0,2,1],
  [1,1,1,0,0,0,1,2,2,0,0,2,2,1,0,0,0],
  [2,1,2,1,0,2,0,1,0,1,1,0,1,2,0,0,2,1,2]
]

def cert0582n : CertifiedBoard :=
  ⟨seed0582, by apply FastValid.valid; decide +kernel⟩

def cert0582r : CertifiedBoard :=
  ⟨seed0582.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0583 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,2,0,1,1,2,1,1,1,0,1],
  [2,2,0,0,1,1,0,0,2,0,2,1,0,0,0],
  [0,1,2,0,1,1,1,0,1,0,2,0,1,2,0,2,2],
  [0,0,2,0,2,1,2,0,0,1,0,2,1,2,2,1,0,0,0]
]

def cert0583n : CertifiedBoard :=
  ⟨seed0583, by apply FastValid.valid; decide +kernel⟩

def cert0583r : CertifiedBoard :=
  ⟨seed0583.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0584 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,2,0,1,1,2,2,1,1,0,2],
  [1,2,0,2,0,2,0,2,0,1,1,1,0,1,2],
  [0,0,2,1,0,1,1,1,0,0,1,2,1,0,0,0,0],
  [0,2,1,2,0,0,2,1,2,0,1,0,0,1,0,2,2,0,0]
]

def cert0584n : CertifiedBoard :=
  ⟨seed0584, by apply FastValid.valid; decide +kernel⟩

def cert0584r : CertifiedBoard :=
  ⟨seed0584.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0585 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,2,0,1,1,2,2,1,1,1,0],
  [0,2,0,0,0,1,1,1,0,2,1,2,1,0,2],
  [1,0,1,1,0,0,2,0,0,0,1,2,0,1,2,0,2],
  [0,2,1,0,0,2,1,2,0,2,2,0,2,0,1,0,1,0,0]
]

def cert0585n : CertifiedBoard :=
  ⟨seed0585, by apply FastValid.valid; decide +kernel⟩

def cert0585r : CertifiedBoard :=
  ⟨seed0585.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0586 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,2,0,1,1,2,2,1,1,1,0],
  [0,2,1,0,0,0,2,1,0,1,1,1,0,0,1],
  [1,0,1,2,0,2,2,0,2,0,1,2,1,2,0,0,0],
  [0,1,0,0,2,1,2,0,1,0,2,0,2,0,0,1,1,0,2]
]

def cert0586n : CertifiedBoard :=
  ⟨seed0586, by apply FastValid.valid; decide +kernel⟩

def cert0586r : CertifiedBoard :=
  ⟨seed0586.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0587 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,2,0,1,1,2,2,1,1,1,0],
  [0,2,1,2,0,1,0,0,0,1,2,1,2,0,0],
  [1,0,2,1,0,0,2,1,0,1,1,0,1,0,2,2,0],
  [2,0,0,1,1,1,0,0,0,2,0,2,0,1,2,0,2,0,2]
]

def cert0587n : CertifiedBoard :=
  ⟨seed0587, by apply FastValid.valid; decide +kernel⟩

def cert0587r : CertifiedBoard :=
  ⟨seed0587.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0588 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,2,0,1,1,2,2,1,1,1,0],
  [1,2,0,2,0,1,1,1,0,1,2,0,2,1,2],
  [0,1,2,0,1,1,0,0,0,2,0,0,0,2,1,0,0],
  [1,0,2,0,2,1,2,1,0,1,0,2,2,0,0,1,0,0,1]
]

def cert0588n : CertifiedBoard :=
  ⟨seed0588, by apply FastValid.valid; decide +kernel⟩

def cert0588r : CertifiedBoard :=
  ⟨seed0588.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0589 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,2,0,1,2,0,0,0,1,1,2],
  [2,0,2,1,1,0,0,2,1,0,1,1,1,0,0],
  [1,0,2,2,1,0,0,1,0,1,0,2,1,2,1,2,0],
  [1,2,2,0,2,0,2,0,0,0,2,0,1,2,0,1,1,1,0]
]

def cert0589n : CertifiedBoard :=
  ⟨seed0589, by apply FastValid.valid; decide +kernel⟩

def cert0589r : CertifiedBoard :=
  ⟨seed0589.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0590 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,2,0,1,2,0,2,1,1,0,1],
  [0,1,0,0,0,1,1,1,2,0,2,1,0,1,1],
  [2,0,1,0,2,1,2,1,2,2,1,0,0,2,0,0,0],
  [1,1,1,0,0,1,1,0,2,0,1,2,0,0,2,0,2,2,0]
]

def cert0590n : CertifiedBoard :=
  ⟨seed0590, by apply FastValid.valid; decide +kernel⟩

def cert0590r : CertifiedBoard :=
  ⟨seed0590.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0591 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,2,0,2,0,1,0,0,1,2,0],
  [2,0,2,1,1,2,0,2,0,1,0,1,1,0,2],
  [0,2,0,1,1,1,0,1,1,1,0,0,1,2,1,0,2],
  [0,2,2,1,2,0,0,0,2,1,2,2,0,0,2,1,0,0,0]
]

def cert0591n : CertifiedBoard :=
  ⟨seed0591, by apply FastValid.valid; decide +kernel⟩

def cert0591r : CertifiedBoard :=
  ⟨seed0591.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0592 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,2,0,2,0,1,1,0,1,2,0],
  [1,0,1,1,1,2,0,2,1,2,1,2,2,1,0],
  [2,0,0,2,1,0,0,1,0,0,0,0,2,1,1,1,0],
  [1,0,2,0,1,1,0,0,1,0,2,2,0,2,0,1,2,0,0]
]

def cert0592n : CertifiedBoard :=
  ⟨seed0592, by apply FastValid.valid; decide +kernel⟩

def cert0592r : CertifiedBoard :=
  ⟨seed0592.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0593 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,2,0,2,0,1,1,1,0,1,1],
  [1,0,2,0,2,1,2,0,2,1,2,2,0,1,0],
  [1,1,1,0,2,2,1,0,0,2,0,0,0,1,1,0,0],
  [1,0,0,0,2,1,1,2,1,0,1,2,0,0,1,2,0,1,0]
]

def cert0593n : CertifiedBoard :=
  ⟨seed0593, by apply FastValid.valid; decide +kernel⟩

def cert0593r : CertifiedBoard :=
  ⟨seed0593.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0594 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,2,0,2,0,2,1,1,0,0,0],
  [0,0,1,0,2,0,2,1,0,1,1,1,0,2,2],
  [2,2,0,1,0,0,1,1,1,0,1,2,1,2,0,1,1],
  [1,1,2,0,0,0,2,1,0,0,2,0,1,2,2,1,2,0,0]
]

def cert0594n : CertifiedBoard :=
  ⟨seed0594, by apply FastValid.valid; decide +kernel⟩

def cert0594r : CertifiedBoard :=
  ⟨seed0594.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0595 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,2,0,2,1,1,0,1,1,1,0],
  [2,2,0,1,2,0,0,1,1,1,0,0,0,2,2],
  [1,0,2,1,2,2,1,0,1,2,1,0,0,1,0,0,0],
  [2,0,1,1,2,0,2,0,0,2,0,1,0,2,1,2,0,2,0]
]

def cert0595n : CertifiedBoard :=
  ⟨seed0595, by apply FastValid.valid; decide +kernel⟩

def cert0595r : CertifiedBoard :=
  ⟨seed0595.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0596 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,2,0,2,1,1,0,2,0,2,1],
  [1,1,0,1,1,0,0,0,2,0,0,1,1,1,1],
  [2,1,2,1,0,0,0,2,1,2,0,2,0,1,2,0,0],
  [0,1,2,2,1,0,2,2,0,1,0,1,0,0,1,1,2,0,1]
]

def cert0596n : CertifiedBoard :=
  ⟨seed0596, by apply FastValid.valid; decide +kernel⟩

def cert0596r : CertifiedBoard :=
  ⟨seed0596.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0597 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,2,0,2,1,1,1,0,1,1,1],
  [1,0,2,0,2,1,2,0,1,0,0,1,2,1,2],
  [1,2,0,2,0,0,1,1,2,0,0,2,1,0,0,0,0],
  [1,1,0,2,2,1,0,0,2,0,1,0,1,2,2,0,1,1,0]
]

def cert0597n : CertifiedBoard :=
  ⟨seed0597, by apply FastValid.valid; decide +kernel⟩

def cert0597r : CertifiedBoard :=
  ⟨seed0597.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0598 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,2,0,2,1,1,1,0,1,1,1],
  [2,1,0,2,0,2,2,1,0,0,2,0,1,2,1],
  [1,1,2,2,0,1,0,0,1,0,0,1,2,0,0,0,0],
  [0,1,1,0,2,1,2,0,0,2,0,2,1,2,0,1,1,0,1]
]

def cert0598n : CertifiedBoard :=
  ⟨seed0598, by apply FastValid.valid; decide +kernel⟩

def cert0598r : CertifiedBoard :=
  ⟨seed0598.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0599 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,2,0,2,1,1,1,0,1,1,2],
  [1,1,0,2,0,2,2,1,2,1,0,1,0,0,0],
  [2,0,0,0,2,1,0,0,1,1,1,0,0,2,1,2,0],
  [1,2,0,0,1,0,2,0,2,0,1,2,2,0,1,2,0,1,1]
]

def cert0599n : CertifiedBoard :=
  ⟨seed0599, by apply FastValid.valid; decide +kernel⟩

def cert0599r : CertifiedBoard :=
  ⟨seed0599.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0600 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,2,0,2,1,1,1,0,1,1,2],
  [2,1,0,1,2,0,2,0,0,0,2,1,0,0,0],
  [1,1,1,0,2,0,2,0,1,0,0,2,1,2,0,1,1],
  [1,2,0,1,1,0,2,2,1,2,2,0,0,1,0,0,1,2,1]
]

def cert0600n : CertifiedBoard :=
  ⟨seed0600, by apply FastValid.valid; decide +kernel⟩

def cert0600r : CertifiedBoard :=
  ⟨seed0600.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0601 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,2,0,2,1,1,1,0,1,1,2],
  [2,1,0,1,2,0,2,1,0,0,2,0,0,0,0],
  [1,1,1,0,2,0,2,2,1,2,0,0,1,0,0,1,1],
  [1,2,0,1,1,0,0,2,0,1,0,2,1,2,2,0,1,2,1]
]

def cert0601n : CertifiedBoard :=
  ⟨seed0601, by apply FastValid.valid; decide +kernel⟩

def cert0601r : CertifiedBoard :=
  ⟨seed0601.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0602 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,2,0,2,1,1,1,1,0,1,1],
  [1,1,0,1,2,0,2,0,0,2,0,1,0,0,0],
  [2,1,2,0,1,1,2,0,2,2,0,1,1,0,2,0,0],
  [0,0,1,0,0,1,2,2,1,0,2,1,2,1,0,0,0,2,1]
]

def cert0602n : CertifiedBoard :=
  ⟨seed0602, by apply FastValid.valid; decide +kernel⟩

def cert0602r : CertifiedBoard :=
  ⟨seed0602.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0603 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,2,0,2,1,1,1,1,0,1,1],
  [2,0,1,1,2,0,2,0,1,2,1,2,0,0,0],
  [0,0,0,1,1,0,0,2,1,2,2,1,0,2,1,0,0],
  [1,1,0,1,0,0,2,2,0,2,0,1,2,0,0,1,0,2,0]
]

def cert0603n : CertifiedBoard :=
  ⟨seed0603, by apply FastValid.valid; decide +kernel⟩

def cert0603r : CertifiedBoard :=
  ⟨seed0603.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0604 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,0,0,0,2,0,2,2,1,1,1],
  [2,0,2,1,0,2,2,0,1,0,1,2,2,0,1],
  [1,0,2,0,2,0,0,0,1,1,0,1,1,2,0,1,0],
  [1,1,1,0,0,2,1,0,0,1,2,1,2,0,0,2,1,2,0]
]

def cert0604n : CertifiedBoard :=
  ⟨seed0604, by apply FastValid.valid; decide +kernel⟩

def cert0604r : CertifiedBoard :=
  ⟨seed0604.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0605 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,0,0,0,2,1,0,0,2,0,2],
  [0,2,0,2,1,0,0,1,2,2,0,0,1,0,1],
  [1,2,0,1,1,1,1,0,1,1,2,0,2,2,0,1,2],
  [1,1,0,2,1,2,0,1,0,2,0,0,0,2,2,1,2,1,1]
]

def cert0605n : CertifiedBoard :=
  ⟨seed0605, by apply FastValid.valid; decide +kernel⟩

def cert0605r : CertifiedBoard :=
  ⟨seed0605.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0606 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,0,0,0,2,1,0,1,2,0,1],
  [1,0,1,2,1,2,0,2,0,0,1,0,0,2,0],
  [2,0,1,1,1,2,2,1,0,2,0,1,1,0,2,2,0],
  [2,0,2,2,0,2,1,1,1,0,0,2,1,2,0,0,0,1,0]
]

def cert0606n : CertifiedBoard :=
  ⟨seed0606, by apply FastValid.valid; decide +kernel⟩

def cert0606r : CertifiedBoard :=
  ⟨seed0606.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0607 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,0,0,2,0,1,0,0,2,2,1],
  [0,0,1,1,0,2,0,2,2,0,2,1,1,1,1],
  [2,1,0,1,2,1,2,0,0,0,1,0,2,1,2,0,0],
  [1,1,2,2,0,2,1,0,1,1,0,0,0,2,0,1,2,0,1]
]

def cert0607n : CertifiedBoard :=
  ⟨seed0607, by apply FastValid.valid; decide +kernel⟩

def cert0607r : CertifiedBoard :=
  ⟨seed0607.map List.reverse, by apply FastValid.valid; decide +kernel⟩

end TBoards.Extended
