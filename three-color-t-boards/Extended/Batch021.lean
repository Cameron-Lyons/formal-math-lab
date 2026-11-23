import Extended.Batch017

/- Generated from extended_seeds.json. Published seeds 0–4:
   Qiyuan Ma, DOI 10.5281/zenodo.23631079, CC-BY-4.0. -/

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.Extended

def seed0672 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,0,0,0,0,2,1,1,0,2],
  [0,2,1,2,2,1,0,2,0,0,1,1,1,0,1],
  [0,1,1,1,0,0,2,1,2,0,2,2,0,2,0,1,0],
  [1,0,1,2,1,0,0,2,0,1,2,0,2,2,0,1,0,0,1]
]

def cert0672n : CertifiedBoard :=
  ⟨seed0672, by apply FastValid.valid; decide +kernel⟩

def cert0672r : CertifiedBoard :=
  ⟨seed0672.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0673 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,0,0,0,0,2,2,1,1,0],
  [0,0,1,1,0,0,2,2,0,2,0,2,1,0,2],
  [0,2,1,2,1,2,0,1,2,0,0,1,1,1,1,0,1],
  [1,0,0,2,0,1,0,2,0,2,1,0,1,2,2,0,1,0,0]
]

def cert0673n : CertifiedBoard :=
  ⟨seed0673, by apply FastValid.valid; decide +kernel⟩

def cert0673r : CertifiedBoard :=
  ⟨seed0673.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0674 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,0,0,0,0,2,2,1,1,0],
  [1,0,1,1,1,1,0,0,1,0,1,2,1,2,0],
  [2,0,2,2,0,1,2,2,0,2,1,0,0,1,0,0,2],
  [0,2,1,2,0,2,1,0,2,0,0,2,0,1,1,0,2,0,1]
]

def cert0674n : CertifiedBoard :=
  ⟨seed0674, by apply FastValid.valid; decide +kernel⟩

def cert0674r : CertifiedBoard :=
  ⟨seed0674.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0675 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,0,0,0,1,0,1,2,0,1],
  [0,0,1,1,1,0,1,0,2,0,0,2,0,1,2],
  [1,2,0,2,1,2,2,0,1,1,1,0,0,2,0,2,2],
  [2,2,0,2,1,1,0,2,1,2,1,0,0,2,2,1,0,0,0]
]

def cert0675n : CertifiedBoard :=
  ⟨seed0675, by apply FastValid.valid; decide +kernel⟩

def cert0675r : CertifiedBoard :=
  ⟨seed0675.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0676 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,0,0,0,1,1,1,0,0,2],
  [0,2,1,2,2,1,0,1,1,1,0,0,1,0,1],
  [2,2,0,1,0,2,1,0,2,0,1,2,0,0,2,0,2],
  [0,2,0,2,2,0,1,2,1,2,0,2,1,1,0,0,0,2,2]
]

def cert0676n : CertifiedBoard :=
  ⟨seed0676, by apply FastValid.valid; decide +kernel⟩

def cert0676r : CertifiedBoard :=
  ⟨seed0676.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0677 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,0,0,0,1,1,1,0,2,0],
  [0,1,1,0,0,2,2,0,1,2,2,0,0,0,1],
  [2,1,2,1,0,1,0,1,2,0,2,2,1,0,2,0,1],
  [2,0,2,0,1,0,0,2,1,2,0,2,1,1,1,0,0,2,1]
]

def cert0677n : CertifiedBoard :=
  ⟨seed0677, by apply FastValid.valid; decide +kernel⟩

def cert0677r : CertifiedBoard :=
  ⟨seed0677.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0678 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,0,0,0,1,2,0,2,1,1],
  [1,2,0,1,0,0,1,0,1,1,0,0,2,1,0],
  [1,0,0,0,2,0,2,0,2,1,2,2,0,1,2,1,2],
  [1,1,1,0,2,2,1,0,1,1,1,0,2,0,0,2,2,0,1]
]

def cert0678n : CertifiedBoard :=
  ⟨seed0678, by apply FastValid.valid; decide +kernel⟩

def cert0678r : CertifiedBoard :=
  ⟨seed0678.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0679 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,0,0,2,0,2,1,1,0,2],
  [1,1,0,0,0,2,1,0,1,1,1,1,0,0,0],
  [0,2,1,2,0,2,2,1,0,2,0,1,2,2,0,0,1],
  [0,0,2,2,0,2,0,1,2,1,2,0,1,0,0,1,0,1,1]
]

def cert0679n : CertifiedBoard :=
  ⟨seed0679, by apply FastValid.valid; decide +kernel⟩

def cert0679r : CertifiedBoard :=
  ⟨seed0679.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0680 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,0,0,2,1,2,0,2,0,1],
  [0,0,2,1,0,0,1,0,1,0,2,1,1,0,0],
  [2,1,0,1,2,1,2,0,1,1,0,0,1,2,2,0,2],
  [0,2,2,0,1,1,1,1,0,2,0,2,0,0,0,0,2,2,1]
]

def cert0680n : CertifiedBoard :=
  ⟨seed0680, by apply FastValid.valid; decide +kernel⟩

def cert0680r : CertifiedBoard :=
  ⟨seed0680.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0681 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,0,0,2,1,2,0,2,2,1],
  [2,1,2,1,0,1,0,0,2,1,1,0,0,0,0],
  [0,0,1,1,1,0,2,0,0,1,2,2,0,2,1,0,1],
  [0,2,2,0,1,0,0,2,0,1,1,1,0,2,0,1,2,0,2]
]

def cert0681n : CertifiedBoard :=
  ⟨seed0681, by apply FastValid.valid; decide +kernel⟩

def cert0681r : CertifiedBoard :=
  ⟨seed0681.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0682 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,0,1,0,1,1,0,0,2,2],
  [2,2,0,2,1,1,0,0,1,2,1,0,1,2,0],
  [0,2,0,1,1,1,1,0,2,1,0,2,0,0,0,0,2],
  [2,0,2,1,2,2,0,0,2,2,1,2,0,2,0,1,0,0,1]
]

def cert0682n : CertifiedBoard :=
  ⟨seed0682, by apply FastValid.valid; decide +kernel⟩

def cert0682r : CertifiedBoard :=
  ⟨seed0682.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0683 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,0,1,0,2,0,2,1,1,0],
  [0,2,2,0,2,0,1,1,0,1,1,1,1,0,2],
  [1,0,1,2,0,2,2,0,0,0,2,1,0,0,2,0,1],
  [1,2,1,2,2,1,0,0,0,1,0,0,1,2,0,0,2,1,2]
]

def cert0683n : CertifiedBoard :=
  ⟨seed0683, by apply FastValid.valid; decide +kernel⟩

def cert0683r : CertifiedBoard :=
  ⟨seed0683.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0684 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,0,1,1,0,0,0,1,2,0],
  [1,0,0,0,2,0,1,2,1,0,1,1,1,1,0],
  [2,0,0,2,0,2,1,2,2,1,0,2,0,2,1,2,0],
  [2,0,2,2,0,1,0,1,0,2,2,0,0,2,1,1,0,0,1]
]

def cert0684n : CertifiedBoard :=
  ⟨seed0684, by apply FastValid.valid; decide +kernel⟩

def cert0684r : CertifiedBoard :=
  ⟨seed0684.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0685 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,0,1,1,0,0,0,2,2,1],
  [1,0,2,1,2,0,1,2,1,2,0,2,0,1,0],
  [0,0,0,2,1,0,1,1,1,1,0,2,0,2,2,0,0],
  [2,1,0,0,1,2,2,0,0,2,0,2,1,1,0,0,1,0,1]
]

def cert0685n : CertifiedBoard :=
  ⟨seed0685, by apply FastValid.valid; decide +kernel⟩

def cert0685r : CertifiedBoard :=
  ⟨seed0685.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0686 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,0,1,1,0,0,0,2,2,1],
  [1,0,2,1,2,0,1,2,1,2,0,2,0,1,0],
  [0,0,0,2,1,0,1,1,1,1,0,2,0,2,2,0,0],
  [2,1,0,0,1,2,2,0,2,0,0,2,1,1,0,0,1,0,1]
]

def cert0686n : CertifiedBoard :=
  ⟨seed0686, by apply FastValid.valid; decide +kernel⟩

def cert0686r : CertifiedBoard :=
  ⟨seed0686.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0687 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,0,1,1,1,0,0,2,0,2],
  [0,2,0,0,0,0,1,2,1,2,0,2,1,2,0],
  [2,0,0,1,1,0,0,2,1,1,1,0,1,2,2,1,0],
  [1,0,1,0,2,0,2,2,0,1,0,0,2,1,0,2,2,0,1]
]

def cert0687n : CertifiedBoard :=
  ⟨seed0687, by apply FastValid.valid; decide +kernel⟩

def cert0687r : CertifiedBoard :=
  ⟨seed0687.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0688 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,0,1,1,1,1,0,0,0,1],
  [2,1,2,1,0,1,1,0,0,0,2,1,0,1,0],
  [0,2,0,2,2,0,2,1,2,0,0,1,2,2,0,0,2],
  [1,0,0,2,2,1,1,0,2,0,2,0,1,2,0,1,0,2,1]
]

def cert0688n : CertifiedBoard :=
  ⟨seed0688, by apply FastValid.valid; decide +kernel⟩

def cert0688r : CertifiedBoard :=
  ⟨seed0688.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0689 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,0,1,1,1,1,0,0,0,2],
  [2,1,2,1,0,2,0,0,0,2,0,0,2,2,1],
  [0,2,2,0,2,1,0,1,1,0,0,1,0,2,1,1,0],
  [1,0,1,2,0,2,0,2,1,2,2,0,1,2,0,1,0,0,1]
]

def cert0689n : CertifiedBoard :=
  ⟨seed0689, by apply FastValid.valid; decide +kernel⟩

def cert0689r : CertifiedBoard :=
  ⟨seed0689.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0690 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,0,1,1,1,1,0,0,2,0],
  [2,0,1,0,0,0,1,2,2,0,2,2,0,1,0],
  [1,0,1,1,0,2,0,0,2,2,1,2,0,2,1,0,1],
  [2,1,2,0,0,0,2,1,0,0,1,2,1,1,0,2,0,2,1]
]

def cert0690n : CertifiedBoard :=
  ⟨seed0690, by apply FastValid.valid; decide +kernel⟩

def cert0690r : CertifiedBoard :=
  ⟨seed0690.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0691 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,0,1,2,0,2,1,1,0,2],
  [0,2,0,0,0,1,1,1,1,0,1,1,0,0,2],
  [0,2,2,1,0,2,1,0,0,2,1,2,1,2,0,0,0],
  [0,0,2,0,2,0,1,2,2,0,2,2,0,1,0,0,1,0,1]
]

def cert0691n : CertifiedBoard :=
  ⟨seed0691, by apply FastValid.valid; decide +kernel⟩

def cert0691r : CertifiedBoard :=
  ⟨seed0691.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0692 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,0,1,2,0,2,1,1,1,0],
  [1,2,0,0,2,0,0,0,2,0,2,1,2,1,2],
  [1,0,0,1,0,0,0,2,1,0,0,1,2,2,1,0,1],
  [1,1,1,0,2,0,2,2,0,1,0,1,1,0,2,2,0,1,1]
]

def cert0692n : CertifiedBoard :=
  ⟨seed0692, by apply FastValid.valid; decide +kernel⟩

def cert0692r : CertifiedBoard :=
  ⟨seed0692.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0693 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,0,1,2,0,2,2,1,1,0],
  [1,0,2,0,0,2,1,0,1,0,0,1,1,0,0],
  [0,0,0,2,1,0,1,2,1,2,2,0,2,1,2,0,1],
  [2,0,0,1,1,1,1,0,0,0,2,0,2,0,1,0,2,2,0]
]

def cert0693n : CertifiedBoard :=
  ⟨seed0693, by apply FastValid.valid; decide +kernel⟩

def cert0693r : CertifiedBoard :=
  ⟨seed0693.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0694 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,0,2,0,1,0,2,0,2,2],
  [2,2,0,1,2,0,2,1,2,1,0,1,1,0,0],
  [0,0,0,1,0,0,2,1,1,1,1,0,2,1,0,0,1],
  [0,0,2,0,1,1,0,1,2,2,0,0,2,2,1,2,0,0,0]
]

def cert0694n : CertifiedBoard :=
  ⟨seed0694, by apply FastValid.valid; decide +kernel⟩

def cert0694r : CertifiedBoard :=
  ⟨seed0694.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0695 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,0,2,0,1,1,0,1,2,0],
  [2,0,2,1,0,0,2,1,0,0,2,0,0,1,0],
  [2,0,2,1,1,0,1,1,1,1,0,2,2,0,1,2,0],
  [1,0,2,2,1,2,1,2,2,0,1,0,0,2,0,0,0,0,1]
]

def cert0695n : CertifiedBoard :=
  ⟨seed0695, by apply FastValid.valid; decide +kernel⟩

def cert0695r : CertifiedBoard :=
  ⟨seed0695.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0696 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,0,2,0,1,1,0,2,1,1],
  [2,0,2,1,2,0,0,1,1,1,0,1,2,2,0],
  [1,1,1,0,0,0,0,2,1,0,0,2,0,0,2,2,0],
  [2,0,1,2,1,0,0,1,0,1,0,2,2,1,2,0,2,0,1]
]

def cert0696n : CertifiedBoard :=
  ⟨seed0696, by apply FastValid.valid; decide +kernel⟩

def cert0696r : CertifiedBoard :=
  ⟨seed0696.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0697 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,0,2,0,1,1,1,0,1,2],
  [1,0,0,0,2,0,0,2,0,1,2,2,0,0,1],
  [1,2,1,0,2,2,1,2,0,2,1,0,0,0,1,1,0],
  [0,2,1,1,1,0,2,1,2,0,2,2,0,1,0,1,0,0,2]
]

def cert0697n : CertifiedBoard :=
  ⟨seed0697, by apply FastValid.valid; decide +kernel⟩

def cert0697r : CertifiedBoard :=
  ⟨seed0697.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0698 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,0,2,0,1,2,0,2,2,1],
  [1,1,0,0,0,1,0,2,0,0,2,1,1,1,0],
  [2,1,2,2,0,0,1,0,2,1,0,0,0,2,1,0,1],
  [1,0,1,1,0,0,2,2,0,1,2,1,2,0,2,0,1,1,1]
]

def cert0698n : CertifiedBoard :=
  ⟨seed0698, by apply FastValid.valid; decide +kernel⟩

def cert0698r : CertifiedBoard :=
  ⟨seed0698.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0699 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,0,2,0,2,1,1,1,0,0],
  [0,2,1,2,2,1,2,0,2,0,1,2,1,0,2],
  [1,0,0,0,0,2,1,0,2,0,1,0,0,1,1,0,1],
  [0,0,2,2,0,0,2,2,0,1,2,0,0,1,1,1,0,1,0]
]

def cert0699n : CertifiedBoard :=
  ⟨seed0699, by apply FastValid.valid; decide +kernel⟩

def cert0699r : CertifiedBoard :=
  ⟨seed0699.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0700 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,0,2,0,2,1,1,1,0,1],
  [1,2,0,0,2,0,2,1,2,0,1,1,0,1,2],
  [0,0,0,1,0,2,2,0,1,0,2,1,2,1,0,0,0],
  [2,0,0,1,1,1,0,0,2,2,0,1,2,2,1,0,0,2,0]
]

def cert0700n : CertifiedBoard :=
  ⟨seed0700, by apply FastValid.valid; decide +kernel⟩

def cert0700r : CertifiedBoard :=
  ⟨seed0700.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0701 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,0,2,0,2,1,1,1,0,1],
  [2,1,2,1,2,0,1,2,0,1,1,1,0,0,0],
  [0,0,1,0,0,2,2,0,0,0,1,2,2,0,0,2,1],
  [1,0,2,0,1,1,0,2,1,0,1,0,0,2,0,2,2,1,0]
]

def cert0701n : CertifiedBoard :=
  ⟨seed0701, by apply FastValid.valid; decide +kernel⟩

def cert0701r : CertifiedBoard :=
  ⟨seed0701.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0702 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,0,2,1,1,0,0,2,0,2],
  [0,2,0,1,0,2,2,1,2,1,2,0,1,0,1],
  [1,0,2,1,0,0,1,2,0,0,1,1,0,0,2,1,0],
  [0,2,0,2,2,0,1,1,1,1,0,1,2,2,0,0,0,0,2]
]

def cert0702n : CertifiedBoard :=
  ⟨seed0702, by apply FastValid.valid; decide +kernel⟩

def cert0702r : CertifiedBoard :=
  ⟨seed0702.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0703 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,0,2,1,1,0,2,0,1,2],
  [1,0,0,2,0,2,2,1,2,1,0,0,1,2,0],
  [1,2,2,0,0,1,1,1,0,0,0,0,2,1,0,1,0],
  [2,0,0,2,1,2,0,1,1,1,0,2,0,2,2,0,1,0,1]
]

def cert0703n : CertifiedBoard :=
  ⟨seed0703, by apply FastValid.valid; decide +kernel⟩

def cert0703r : CertifiedBoard :=
  ⟨seed0703.map List.reverse, by apply FastValid.valid; decide +kernel⟩

end TBoards.Extended
