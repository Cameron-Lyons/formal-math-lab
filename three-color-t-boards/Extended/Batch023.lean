import Extended.Batch019

/- Generated from extended_seeds.json. Published seeds 0–4:
   Qiyuan Ma, DOI 10.5281/zenodo.23631079, CC-BY-4.0. -/

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.Extended

def seed0736 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,1,2,0,1,0,2,1,1,0],
  [2,1,0,0,0,0,2,2,0,0,1,2,2,0,1],
  [1,0,1,2,0,0,2,0,2,0,2,1,0,0,1,1,1],
  [1,1,0,1,1,1,0,0,2,2,1,2,0,1,0,2,0,2,1]
]

def cert0736n : CertifiedBoard :=
  ⟨seed0736, by apply FastValid.valid; decide +kernel⟩

def cert0736r : CertifiedBoard :=
  ⟨seed0736.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0737 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,1,2,0,1,1,0,0,1,2],
  [0,0,1,2,2,1,0,2,0,2,1,0,1,0,1],
  [0,1,0,2,0,2,2,0,2,1,2,0,1,1,0,0,0],
  [1,2,0,0,2,0,0,0,2,1,1,1,1,0,0,2,2,0,1]
]

def cert0737n : CertifiedBoard :=
  ⟨seed0737, by apply FastValid.valid; decide +kernel⟩

def cert0737r : CertifiedBoard :=
  ⟨seed0737.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0738 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,1,2,0,2,1,1,0,0,0],
  [2,0,0,2,0,1,2,0,2,2,0,1,0,0,1],
  [0,0,2,1,0,1,1,1,1,0,2,1,2,2,0,1,0],
  [1,0,2,2,1,0,1,1,0,0,0,2,0,0,1,2,0,2,0]
]

def cert0738n : CertifiedBoard :=
  ⟨seed0738, by apply FastValid.valid; decide +kernel⟩

def cert0738r : CertifiedBoard :=
  ⟨seed0738.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0739 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,1,2,0,2,1,1,0,0,1],
  [1,0,1,1,0,1,2,0,1,2,2,0,2,1,0],
  [1,1,1,0,0,2,0,2,2,0,0,2,0,0,0,0,2],
  [0,2,0,1,0,2,2,1,0,2,1,2,0,1,0,0,1,1,1]
]

def cert0739n : CertifiedBoard :=
  ⟨seed0739, by apply FastValid.valid; decide +kernel⟩

def cert0739r : CertifiedBoard :=
  ⟨seed0739.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0740 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,1,2,0,2,1,1,0,0,2],
  [1,2,0,0,0,1,2,0,2,2,0,2,0,1,2],
  [0,2,0,1,0,1,1,1,1,0,2,0,0,0,1,0,1],
  [0,2,2,1,2,2,0,1,1,0,0,2,1,0,2,1,0,0,2]
]

def cert0740n : CertifiedBoard :=
  ⟨seed0740, by apply FastValid.valid; decide +kernel⟩

def cert0740r : CertifiedBoard :=
  ⟨seed0740.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0741 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,1,2,0,2,1,1,1,0,1],
  [0,0,2,0,0,0,2,2,0,1,0,0,0,1,2],
  [1,2,0,2,1,0,1,0,2,0,1,1,0,2,0,1,2],
  [1,2,2,1,2,0,2,2,0,0,1,1,1,0,0,2,1,0,0]
]

def cert0741n : CertifiedBoard :=
  ⟨seed0741, by apply FastValid.valid; decide +kernel⟩

def cert0741r : CertifiedBoard :=
  ⟨seed0741.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0742 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,1,2,0,2,1,1,1,0,2],
  [0,2,0,0,0,1,0,0,2,0,1,1,0,0,0],
  [1,2,0,1,0,1,1,1,0,2,2,0,2,0,2,1,2],
  [0,0,2,1,0,0,1,2,2,0,1,2,0,0,2,2,1,0,1]
]

def cert0742n : CertifiedBoard :=
  ⟨seed0742, by apply FastValid.valid; decide +kernel⟩

def cert0742r : CertifiedBoard :=
  ⟨seed0742.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0743 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,1,2,2,1,0,0,0,2,0],
  [0,2,2,0,0,1,1,0,2,0,2,1,0,1,0],
  [1,0,2,1,1,0,1,0,0,1,2,0,2,1,2,0,1],
  [2,0,1,1,1,1,0,0,0,2,0,2,2,0,1,2,0,0,2]
]

def cert0743n : CertifiedBoard :=
  ⟨seed0743, by apply FastValid.valid; decide +kernel⟩

def cert0743r : CertifiedBoard :=
  ⟨seed0743.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0744 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,1,2,2,1,0,0,1,2,0],
  [0,0,2,0,0,2,1,1,1,0,1,1,1,0,0],
  [2,0,1,0,2,1,0,1,0,0,2,2,0,1,2,0,2],
  [0,2,1,2,0,0,0,0,1,1,0,2,0,2,0,2,2,0,1]
]

def cert0744n : CertifiedBoard :=
  ⟨seed0744, by apply FastValid.valid; decide +kernel⟩

def cert0744r : CertifiedBoard :=
  ⟨seed0744.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0745 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,1,2,2,1,0,0,1,2,0],
  [0,1,1,0,0,2,1,1,1,1,0,0,0,0,1],
  [2,0,1,2,0,0,2,2,0,0,2,0,2,1,2,0,1],
  [1,0,2,0,2,1,0,2,0,2,2,0,1,0,1,1,0,1,0]
]

def cert0745n : CertifiedBoard :=
  ⟨seed0745, by apply FastValid.valid; decide +kernel⟩

def cert0745r : CertifiedBoard :=
  ⟨seed0745.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0746 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,1,2,2,1,0,0,1,2,0],
  [2,0,1,1,1,1,0,2,0,2,0,0,0,0,1],
  [2,0,2,2,0,1,2,0,2,1,0,1,1,0,1,0,0],
  [0,0,2,1,1,0,0,2,2,0,1,0,2,0,0,2,1,2,0]
]

def cert0746n : CertifiedBoard :=
  ⟨seed0746, by apply FastValid.valid; decide +kernel⟩

def cert0746r : CertifiedBoard :=
  ⟨seed0746.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0747 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,1,2,2,1,0,0,2,0,1],
  [2,0,1,1,0,2,1,1,1,1,0,1,2,0,2],
  [0,2,2,0,1,0,0,0,2,0,0,0,1,2,0,0,1],
  [0,1,1,0,1,0,0,2,0,2,1,0,2,2,0,2,1,2,0]
]

def cert0747n : CertifiedBoard :=
  ⟨seed0747, by apply FastValid.valid; decide +kernel⟩

def cert0747r : CertifiedBoard :=
  ⟨seed0747.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0748 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,1,2,2,1,0,0,2,1,1],
  [0,2,2,0,0,1,2,0,1,1,0,0,0,0,2],
  [2,1,0,2,0,1,1,1,0,2,0,2,0,0,1,0,1],
  [1,1,1,0,1,2,0,1,0,0,2,2,0,2,1,2,0,2,1]
]

def cert0748n : CertifiedBoard :=
  ⟨seed0748, by apply FastValid.valid; decide +kernel⟩

def cert0748r : CertifiedBoard :=
  ⟨seed0748.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0749 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,1,2,2,1,0,1,2,0,1],
  [1,1,0,0,0,1,0,0,0,2,0,2,2,0,1],
  [0,1,1,0,0,2,2,0,1,0,2,1,0,2,0,2,1],
  [2,1,2,0,0,1,1,1,0,1,2,0,2,0,0,2,1,1,1]
]

def cert0749n : CertifiedBoard :=
  ⟨seed0749, by apply FastValid.valid; decide +kernel⟩

def cert0749r : CertifiedBoard :=
  ⟨seed0749.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0750 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,1,2,2,1,0,1,2,0,2],
  [1,2,0,2,1,1,0,0,0,0,1,1,0,0,1],
  [2,0,0,2,0,1,0,0,2,1,0,2,0,1,0,1,2],
  [0,2,2,0,2,1,2,0,1,1,1,1,0,2,2,0,0,2,0]
]

def cert0750n : CertifiedBoard :=
  ⟨seed0750, by apply FastValid.valid; decide +kernel⟩

def cert0750r : CertifiedBoard :=
  ⟨seed0750.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0751 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,1,2,2,1,0,2,0,1,2],
  [0,0,1,0,0,0,0,2,2,0,0,1,1,1,0],
  [1,0,0,2,1,0,2,2,0,2,1,2,0,1,1,0,1],
  [1,2,0,1,0,0,2,1,1,1,0,1,2,0,2,0,2,0,0]
]

def cert0751n : CertifiedBoard :=
  ⟨seed0751, by apply FastValid.valid; decide +kernel⟩

def cert0751r : CertifiedBoard :=
  ⟨seed0751.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0752 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,1,2,2,1,0,2,1,1,0],
  [2,1,0,0,2,2,0,2,0,1,0,1,1,0,1],
  [0,0,1,0,0,1,2,0,0,0,2,0,1,2,0,2,1],
  [1,0,2,0,2,2,0,0,2,1,2,0,1,1,1,1,0,0,0]
]

def cert0752n : CertifiedBoard :=
  ⟨seed0752, by apply FastValid.valid; decide +kernel⟩

def cert0752r : CertifiedBoard :=
  ⟨seed0752.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0753 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,1,2,2,1,0,2,1,1,1],
  [0,2,0,2,0,1,0,0,1,1,0,1,2,0,1],
  [2,0,0,0,2,2,0,0,1,1,1,0,0,0,2,2,0],
  [1,1,0,1,0,2,0,2,1,0,0,2,1,2,0,1,2,0,2]
]

def cert0753n : CertifiedBoard :=
  ⟨seed0753, by apply FastValid.valid; decide +kernel⟩

def cert0753r : CertifiedBoard :=
  ⟨seed0753.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0754 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,2,0,0,0,0,1,2,0,1],
  [1,0,1,0,0,2,1,2,0,2,0,2,0,1,2],
  [1,2,0,0,2,2,0,2,1,1,0,1,0,0,1,1,1],
  [1,1,1,0,0,2,2,1,0,2,0,1,1,0,2,1,2,1,0]
]

def cert0754n : CertifiedBoard :=
  ⟨seed0754, by apply FastValid.valid; decide +kernel⟩

def cert0754r : CertifiedBoard :=
  ⟨seed0754.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0755 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,2,0,0,0,0,2,0,2,1],
  [2,0,1,2,1,1,1,0,2,1,0,2,2,1,0],
  [1,0,1,1,1,0,0,2,0,0,1,0,1,2,0,2,0],
  [2,1,2,0,1,1,0,0,2,2,0,2,1,2,0,1,0,0,1]
]

def cert0755n : CertifiedBoard :=
  ⟨seed0755, by apply FastValid.valid; decide +kernel⟩

def cert0755r : CertifiedBoard :=
  ⟨seed0755.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0756 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,2,0,0,0,0,2,0,2,2],
  [2,2,0,2,1,1,1,0,0,2,0,1,0,0,1],
  [1,0,2,1,0,1,1,1,0,1,1,0,2,0,2,1,0],
  [0,0,2,2,1,2,0,1,0,0,1,2,1,2,0,1,2,0,0]
]

def cert0756n : CertifiedBoard :=
  ⟨seed0756, by apply FastValid.valid; decide +kernel⟩

def cert0756r : CertifiedBoard :=
  ⟨seed0756.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0757 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,2,0,0,0,0,2,2,1,1],
  [1,0,2,1,0,2,1,2,0,0,2,0,2,0,1],
  [1,1,0,1,2,1,0,1,2,0,2,0,1,0,0,1,0],
  [2,1,2,0,1,1,1,1,0,0,1,1,0,0,2,2,0,2,1]
]

def cert0757n : CertifiedBoard :=
  ⟨seed0757, by apply FastValid.valid; decide +kernel⟩

def cert0757r : CertifiedBoard :=
  ⟨seed0757.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0758 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,2,0,0,0,0,2,2,1,1],
  [2,0,1,1,0,1,2,0,0,1,0,0,1,2,0],
  [1,1,0,2,1,0,1,0,2,1,2,1,0,0,2,0,2],
  [0,2,0,1,1,1,1,0,0,2,1,2,0,2,2,0,2,0,1]
]

def cert0758n : CertifiedBoard :=
  ⟨seed0758, by apply FastValid.valid; decide +kernel⟩

def cert0758r : CertifiedBoard :=
  ⟨seed0758.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0759 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,2,0,0,0,2,1,1,1,0],
  [0,2,1,0,0,2,0,0,1,0,2,0,1,0,2],
  [1,0,1,2,1,2,0,2,2,0,2,0,1,1,1,0,1],
  [1,1,0,0,0,1,2,0,2,2,1,0,0,2,1,2,0,1,1]
]

def cert0759n : CertifiedBoard :=
  ⟨seed0759, by apply FastValid.valid; decide +kernel⟩

def cert0759r : CertifiedBoard :=
  ⟨seed0759.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0760 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,2,0,0,1,0,0,0,2,2],
  [0,2,1,2,1,1,1,0,0,0,1,0,1,2,0],
  [2,0,2,1,0,1,1,0,0,2,2,0,1,1,1,0,2],
  [2,2,1,0,2,0,0,2,1,2,0,2,0,1,2,0,2,0,1]
]

def cert0760n : CertifiedBoard :=
  ⟨seed0760, by apply FastValid.valid; decide +kernel⟩

def cert0760r : CertifiedBoard :=
  ⟨seed0760.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0761 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,2,0,0,1,0,0,2,1,1],
  [1,0,0,2,0,2,2,0,0,0,2,0,1,1,0],
  [1,2,0,2,2,1,0,1,2,0,1,1,0,2,1,0,1],
  [1,1,1,1,0,2,0,1,0,0,0,1,2,1,2,0,2,1,2]
]

def cert0761n : CertifiedBoard :=
  ⟨seed0761, by apply FastValid.valid; decide +kernel⟩

def cert0761r : CertifiedBoard :=
  ⟨seed0761.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0762 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,2,0,0,1,0,1,2,0,1],
  [1,1,0,0,0,2,0,1,1,0,0,2,2,0,1],
  [1,2,1,2,0,0,2,1,2,0,2,1,0,0,0,1,2],
  [0,1,1,1,1,0,1,0,2,0,2,2,1,0,2,0,2,1,1]
]

def cert0762n : CertifiedBoard :=
  ⟨seed0762, by apply FastValid.valid; decide +kernel⟩

def cert0762r : CertifiedBoard :=
  ⟨seed0762.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0763 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,2,0,0,1,0,1,2,0,1],
  [2,0,2,0,2,2,1,2,0,1,1,0,0,1,1],
  [0,2,0,0,2,1,1,1,1,0,0,0,2,0,1,2,0],
  [1,1,0,2,2,0,2,1,2,1,0,1,0,2,1,0,0,0,2]
]

def cert0763n : CertifiedBoard :=
  ⟨seed0763, by apply FastValid.valid; decide +kernel⟩

def cert0763r : CertifiedBoard :=
  ⟨seed0763.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0764 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,2,0,0,1,0,1,2,0,2],
  [2,1,0,0,0,0,2,1,2,0,0,2,2,0,1],
  [1,1,1,1,0,0,2,2,1,0,0,1,0,2,0,1,1],
  [0,2,0,2,1,2,0,2,1,1,0,2,0,1,1,0,1,2,1]
]

def cert0764n : CertifiedBoard :=
  ⟨seed0764, by apply FastValid.valid; decide +kernel⟩

def cert0764r : CertifiedBoard :=
  ⟨seed0764.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0765 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,2,0,0,1,0,2,2,1,1],
  [0,2,1,2,0,2,0,0,2,1,0,1,2,1,0],
  [1,0,0,0,2,1,2,0,1,0,0,0,1,1,1,0,2],
  [1,1,1,0,1,1,0,0,2,0,2,2,0,2,0,1,2,0,1]
]

def cert0765n : CertifiedBoard :=
  ⟨seed0765, by apply FastValid.valid; decide +kernel⟩

def cert0765r : CertifiedBoard :=
  ⟨seed0765.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0766 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,2,0,0,1,0,2,2,1,1],
  [1,0,0,0,2,0,2,2,0,1,1,0,1,1,0],
  [2,1,0,1,0,2,1,0,0,0,2,0,2,1,2,0,1],
  [1,1,1,1,0,0,1,2,1,2,0,0,2,0,1,2,0,2,1]
]

def cert0766n : CertifiedBoard :=
  ⟨seed0766, by apply FastValid.valid; decide +kernel⟩

def cert0766r : CertifiedBoard :=
  ⟨seed0766.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0767 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,2,0,0,1,2,0,2,0,1],
  [0,2,0,1,1,1,0,2,1,0,0,2,2,0,2],
  [1,1,0,1,1,0,0,0,1,2,1,0,0,0,2,2,1],
  [2,1,2,0,0,2,0,1,0,1,0,2,1,2,0,2,1,1,1]
]

def cert0767n : CertifiedBoard :=
  ⟨seed0767, by apply FastValid.valid; decide +kernel⟩

def cert0767r : CertifiedBoard :=
  ⟨seed0767.map List.reverse, by apply FastValid.valid; decide +kernel⟩

end TBoards.Extended
