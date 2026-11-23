import Extended.Batch020

/- Generated from extended_seeds.json. Published seeds 0–4:
   Qiyuan Ma, DOI 10.5281/zenodo.23631079, CC-BY-4.0. -/

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.Extended

def seed0768 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,2,0,0,2,0,2,2,1,1],
  [0,0,2,1,0,2,1,0,0,1,1,1,0,0,0],
  [1,1,0,2,0,1,0,0,2,1,2,1,2,0,2,0,1],
  [1,1,1,0,1,2,0,2,2,0,1,0,1,2,0,0,0,1,1]
]

def cert0768n : CertifiedBoard :=
  ⟨seed0768, by apply FastValid.valid; decide +kernel⟩

def cert0768r : CertifiedBoard :=
  ⟨seed0768.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0769 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,2,0,0,2,1,1,1,0,1],
  [0,2,1,2,0,2,2,0,0,1,1,1,0,1,2],
  [2,1,0,0,0,0,2,0,1,1,0,0,2,0,1,0,2],
  [1,2,0,1,0,2,0,2,1,2,1,0,0,1,2,0,2,2,1]
]

def cert0769n : CertifiedBoard :=
  ⟨seed0769, by apply FastValid.valid; decide +kernel⟩

def cert0769r : CertifiedBoard :=
  ⟨seed0769.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0770 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,2,0,1,2,1,1,0,0,0],
  [1,0,0,0,2,2,1,2,0,1,1,1,0,1,0],
  [2,0,0,2,1,0,2,1,2,0,2,1,0,0,1,2,0],
  [0,0,2,2,0,2,0,0,1,0,1,1,1,0,2,0,2,0,1]
]

def cert0770n : CertifiedBoard :=
  ⟨seed0770, by apply FastValid.valid; decide +kernel⟩

def cert0770r : CertifiedBoard :=
  ⟨seed0770.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0771 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,2,0,1,2,1,1,0,2,0],
  [1,0,2,1,2,0,2,0,0,1,0,0,2,1,0],
  [2,0,2,2,1,0,1,1,1,0,1,2,0,0,0,0,1],
  [2,0,1,0,0,2,0,1,1,1,0,0,2,2,0,2,1,2,0]
]

def cert0771n : CertifiedBoard :=
  ⟨seed0771, by apply FastValid.valid; decide +kernel⟩

def cert0771r : CertifiedBoard :=
  ⟨seed0771.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0772 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,2,0,1,2,1,1,1,0,1],
  [0,0,2,0,2,0,1,0,0,2,1,2,0,1,2],
  [1,2,0,2,1,0,0,1,1,0,0,0,2,2,0,0,1],
  [0,1,0,2,2,1,0,1,1,1,0,2,1,2,0,2,0,0,0]
]

def cert0772n : CertifiedBoard :=
  ⟨seed0772, by apply FastValid.valid; decide +kernel⟩

def cert0772r : CertifiedBoard :=
  ⟨seed0772.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0773 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,2,0,1,2,1,1,1,0,1],
  [0,1,0,0,0,2,0,0,2,1,2,0,2,1,0],
  [0,0,1,1,0,2,2,1,2,0,1,0,2,0,2,0,1],
  [1,0,1,1,1,0,0,0,1,2,0,2,1,0,0,2,2,0,0]
]

def cert0773n : CertifiedBoard :=
  ⟨seed0773, by apply FastValid.valid; decide +kernel⟩

def cert0773r : CertifiedBoard :=
  ⟨seed0773.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0774 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,2,0,1,2,1,1,1,0,1],
  [0,2,0,2,0,2,2,0,0,1,1,1,0,1,0],
  [2,0,2,1,0,0,2,0,1,1,0,0,0,2,1,0,2],
  [1,0,2,2,1,2,0,0,0,1,2,0,1,0,0,2,1,2,0]
]

def cert0774n : CertifiedBoard :=
  ⟨seed0774, by apply FastValid.valid; decide +kernel⟩

def cert0774r : CertifiedBoard :=
  ⟨seed0774.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0775 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,2,0,1,2,1,1,1,0,2],
  [0,0,1,2,0,2,2,0,0,1,1,1,0,0,0],
  [2,0,2,0,2,1,2,0,1,1,0,0,0,2,1,0,1],
  [0,2,0,0,2,2,1,0,0,2,1,2,0,1,0,1,0,2,0]
]

def cert0775n : CertifiedBoard :=
  ⟨seed0775, by apply FastValid.valid; decide +kernel⟩

def cert0775r : CertifiedBoard :=
  ⟨seed0775.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0776 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,2,0,2,0,0,1,2,0,1],
  [0,2,1,2,1,1,1,0,2,0,0,0,0,1,2],
  [1,0,0,2,0,2,1,0,0,2,1,2,0,1,1,1,0],
  [1,2,0,2,2,1,0,1,0,1,0,0,2,2,0,1,1,0,2]
]

def cert0776n : CertifiedBoard :=
  ⟨seed0776, by apply FastValid.valid; decide +kernel⟩

def cert0776r : CertifiedBoard :=
  ⟨seed0776.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0777 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,2,0,2,1,0,0,0,2,0],
  [1,0,2,1,2,0,2,0,1,2,0,2,2,1,0],
  [0,1,0,1,2,1,1,0,1,0,0,1,1,0,2,0,1],
  [2,0,0,0,1,1,1,1,0,0,2,1,2,0,0,2,2,0,1]
]

def cert0777n : CertifiedBoard :=
  ⟨seed0777, by apply FastValid.valid; decide +kernel⟩

def cert0777r : CertifiedBoard :=
  ⟨seed0777.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0778 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,2,0,2,1,0,0,2,0,1],
  [1,0,1,1,1,1,0,0,0,2,1,0,1,1,0],
  [2,0,0,1,2,0,1,0,2,2,0,2,0,2,1,2,0],
  [1,0,2,0,0,0,1,0,0,2,2,1,2,0,1,2,1,1,0]
]

def cert0778n : CertifiedBoard :=
  ⟨seed0778, by apply FastValid.valid; decide +kernel⟩

def cert0778r : CertifiedBoard :=
  ⟨seed0778.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0779 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,2,0,2,1,0,1,2,0,2],
  [0,2,0,0,0,0,1,1,1,0,0,2,2,0,1],
  [1,1,0,0,2,1,0,1,2,1,2,0,0,2,0,1,1],
  [0,1,0,0,1,0,2,0,2,1,1,1,0,2,2,1,2,0,1]
]

def cert0779n : CertifiedBoard :=
  ⟨seed0779, by apply FastValid.valid; decide +kernel⟩

def cert0779r : CertifiedBoard :=
  ⟨seed0779.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0780 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,2,0,2,1,2,0,2,0,1],
  [1,0,1,0,0,0,1,1,1,0,1,0,2,1,0],
  [1,2,1,2,0,2,2,0,0,2,0,1,1,0,0,0,2],
  [0,2,1,1,1,0,2,2,1,0,0,2,0,1,2,0,0,1,2]
]

def cert0780n : CertifiedBoard :=
  ⟨seed0780, by apply FastValid.valid; decide +kernel⟩

def cert0780r : CertifiedBoard :=
  ⟨seed0780.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0781 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,2,0,2,1,2,0,2,0,1],
  [1,2,0,0,0,0,2,1,1,1,1,0,0,2,1],
  [2,1,0,2,0,0,1,1,0,0,2,0,1,0,0,1,2],
  [0,1,2,0,2,2,0,1,1,0,2,2,1,2,1,0,1,0,1]
]

def cert0781n : CertifiedBoard :=
  ⟨seed0781, by apply FastValid.valid; decide +kernel⟩

def cert0781r : CertifiedBoard :=
  ⟨seed0781.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0782 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,2,0,2,1,2,0,2,2,1],
  [0,0,1,1,1,1,0,1,2,1,1,0,0,0,2],
  [0,2,2,0,1,0,0,0,2,0,1,2,0,1,0,0,1],
  [2,1,0,2,0,2,1,2,0,0,2,1,0,1,1,0,2,0,0]
]

def cert0782n : CertifiedBoard :=
  ⟨seed0782, by apply FastValid.valid; decide +kernel⟩

def cert0782r : CertifiedBoard :=
  ⟨seed0782.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0783 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,2,0,2,1,2,0,2,2,1],
  [2,0,1,1,0,0,2,1,1,1,1,0,1,2,0],
  [0,0,1,0,0,2,0,2,0,1,2,1,0,0,0,0,1],
  [2,1,0,2,1,2,0,1,1,0,1,0,2,0,0,2,2,0,0]
]

def cert0783n : CertifiedBoard :=
  ⟨seed0783, by apply FastValid.valid; decide +kernel⟩

def cert0783r : CertifiedBoard :=
  ⟨seed0783.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0784 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,2,0,2,1,2,0,2,2,1],
  [2,1,2,1,0,0,1,0,1,0,2,0,1,2,0],
  [0,0,2,1,1,1,0,0,0,2,0,0,0,1,1,0,1],
  [2,0,1,1,1,0,0,2,1,0,2,0,2,2,0,1,2,0,0]
]

def cert0784n : CertifiedBoard :=
  ⟨seed0784, by apply FastValid.valid; decide +kernel⟩

def cert0784r : CertifiedBoard :=
  ⟨seed0784.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0785 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,0,0,2,0,2,1,1,1,0],
  [1,0,2,0,2,0,2,2,1,0,1,2,2,0,1],
  [0,1,0,0,1,1,2,0,1,1,1,0,0,2,2,0,1],
  [2,1,2,0,0,1,1,0,2,1,2,1,0,1,0,0,0,2,1]
]

def cert0785n : CertifiedBoard :=
  ⟨seed0785, by apply FastValid.valid; decide +kernel⟩

def cert0785r : CertifiedBoard :=
  ⟨seed0785.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0786 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,0,0,2,0,2,2,1,1,0],
  [1,1,0,0,2,2,0,0,0,1,1,2,2,0,1],
  [0,1,2,1,2,0,2,1,0,0,2,1,0,0,1,1,1],
  [1,0,1,1,1,0,1,0,2,0,2,0,1,0,2,1,2,0,1]
]

def cert0786n : CertifiedBoard :=
  ⟨seed0786, by apply FastValid.valid; decide +kernel⟩

def cert0786r : CertifiedBoard :=
  ⟨seed0786.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0787 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,0,0,2,0,2,2,1,1,2],
  [0,2,1,0,0,2,0,0,0,1,1,1,1,0,2],
  [1,0,0,1,1,0,2,1,2,0,2,1,2,0,1,0,1],
  [1,2,1,0,1,2,2,0,2,0,1,1,0,0,2,2,0,1,0]
]

def cert0787n : CertifiedBoard :=
  ⟨seed0787, by apply FastValid.valid; decide +kernel⟩

def cert0787r : CertifiedBoard :=
  ⟨seed0787.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0788 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,0,0,2,1,0,0,1,1,2],
  [0,0,1,1,0,0,2,0,1,0,1,1,1,0,1],
  [1,2,0,2,0,1,0,2,2,0,2,1,2,2,0,1,2],
  [1,2,0,2,2,1,2,1,0,2,0,0,2,1,1,1,0,0,0]
]

def cert0788n : CertifiedBoard :=
  ⟨seed0788, by apply FastValid.valid; decide +kernel⟩

def cert0788r : CertifiedBoard :=
  ⟨seed0788.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0789 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,0,0,2,1,0,2,0,1,1],
  [1,2,0,2,2,0,2,0,2,0,0,0,2,1,2],
  [1,1,1,1,0,0,2,2,1,0,1,0,1,1,0,0,1],
  [1,2,2,0,1,0,2,1,1,2,1,2,0,1,1,0,0,1,2]
]

def cert0789n : CertifiedBoard :=
  ⟨seed0789, by apply FastValid.valid; decide +kernel⟩

def cert0789r : CertifiedBoard :=
  ⟨seed0789.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0790 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,0,0,2,2,0,2,1,1,0],
  [2,0,1,1,1,0,0,2,0,1,0,1,2,2,0],
  [1,0,2,1,2,1,0,2,2,1,0,0,1,0,0,1,1],
  [1,1,0,1,1,1,2,0,0,0,2,1,2,0,2,0,2,0,1]
]

def cert0790n : CertifiedBoard :=
  ⟨seed0790, by apply FastValid.valid; decide +kernel⟩

def cert0790r : CertifiedBoard :=
  ⟨seed0790.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0791 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,0,0,2,2,0,2,1,1,1],
  [1,1,0,0,2,0,1,1,0,0,2,0,1,1,0],
  [0,2,1,2,0,0,0,1,2,0,2,2,1,2,1,0,1],
  [1,0,0,1,0,2,1,0,2,0,1,0,1,1,1,2,2,0,2]
]

def cert0791n : CertifiedBoard :=
  ⟨seed0791, by apply FastValid.valid; decide +kernel⟩

def cert0791r : CertifiedBoard :=
  ⟨seed0791.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0792 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,0,0,2,2,0,2,1,1,1],
  [1,2,0,2,0,0,1,0,0,2,0,1,2,1,2],
  [1,1,1,0,0,0,2,1,0,2,2,1,0,0,1,0,1],
  [2,0,1,1,0,1,1,0,2,0,1,1,2,2,0,2,1,2,0]
]

def cert0792n : CertifiedBoard :=
  ⟨seed0792, by apply FastValid.valid; decide +kernel⟩

def cert0792r : CertifiedBoard :=
  ⟨seed0792.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0793 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,0,2,0,1,0,2,0,2,1],
  [2,1,2,2,1,0,2,2,0,1,0,1,1,2,0],
  [1,0,0,0,1,1,0,0,0,2,2,0,1,1,1,1,0],
  [2,0,2,0,0,2,1,2,0,2,1,1,0,1,2,1,0,0,1]
]

def cert0793n : CertifiedBoard :=
  ⟨seed0793, by apply FastValid.valid; decide +kernel⟩

def cert0793r : CertifiedBoard :=
  ⟨seed0793.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0794 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,0,2,0,1,1,0,2,0,2],
  [1,2,0,2,2,0,2,1,2,1,0,0,1,1,2],
  [0,2,1,1,0,0,0,1,1,1,1,0,1,0,0,0,2],
  [0,2,2,1,2,0,0,2,0,1,2,2,0,1,0,2,1,0,1]
]

def cert0794n : CertifiedBoard :=
  ⟨seed0794, by apply FastValid.valid; decide +kernel⟩

def cert0794r : CertifiedBoard :=
  ⟨seed0794.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0795 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,0,2,0,1,1,1,0,0,1],
  [0,1,1,1,2,0,0,2,0,1,2,1,0,2,1],
  [2,1,2,2,0,2,0,2,1,1,0,0,0,0,2,1,0],
  [1,0,1,0,2,2,0,2,2,1,2,0,1,0,0,1,1,0,1]
]

def cert0795n : CertifiedBoard :=
  ⟨seed0795, by apply FastValid.valid; decide +kernel⟩

def cert0795r : CertifiedBoard :=
  ⟨seed0795.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0796 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,0,2,0,2,1,1,0,0,1],
  [0,2,1,0,2,0,0,2,2,1,2,1,0,0,0],
  [0,1,1,2,0,2,1,2,0,1,1,1,1,0,1,0,2],
  [0,0,1,0,0,0,2,0,2,2,0,1,2,2,0,1,1,0,1]
]

def cert0796n : CertifiedBoard :=
  ⟨seed0796, by apply FastValid.valid; decide +kernel⟩

def cert0796r : CertifiedBoard :=
  ⟨seed0796.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0797 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,0,2,1,1,1,0,0,0,1],
  [1,0,0,0,2,0,2,1,2,1,0,2,1,2,2],
  [2,2,0,0,1,0,1,1,2,0,1,0,1,1,0,2,0],
  [2,0,2,2,0,1,2,0,1,1,1,0,0,2,0,2,2,1,0]
]

def cert0797n : CertifiedBoard :=
  ⟨seed0797, by apply FastValid.valid; decide +kernel⟩

def cert0797r : CertifiedBoard :=
  ⟨seed0797.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0798 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,0,2,1,1,1,1,0,0,0],
  [0,2,0,2,2,0,0,2,0,1,2,1,0,0,1],
  [1,2,0,1,0,1,1,0,2,0,1,1,2,0,2,1,2],
  [0,0,0,1,1,0,1,0,0,2,1,2,2,0,2,2,1,0,2]
]

def cert0798n : CertifiedBoard :=
  ⟨seed0798, by apply FastValid.valid; decide +kernel⟩

def cert0798r : CertifiedBoard :=
  ⟨seed0798.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0799 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,1,0,0,0,0,2,1,1,0],
  [0,2,1,0,0,1,1,0,0,2,2,1,2,0,2],
  [1,0,2,0,2,0,1,2,1,0,1,1,1,1,2,0,2],
  [0,2,0,0,1,0,1,1,0,2,1,2,2,0,0,2,2,0,1]
]

def cert0799n : CertifiedBoard :=
  ⟨seed0799, by apply FastValid.valid; decide +kernel⟩

def cert0799r : CertifiedBoard :=
  ⟨seed0799.map List.reverse, by apply FastValid.valid; decide +kernel⟩

end TBoards.Extended
