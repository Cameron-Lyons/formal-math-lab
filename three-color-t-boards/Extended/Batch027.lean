import Extended.Batch023

/- Generated from extended_seeds.json. Published seeds 0–4:
   Qiyuan Ma, DOI 10.5281/zenodo.23631079, CC-BY-4.0. -/

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.Extended

def seed0864 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,1,2,1,1,1,0,0,0,2],
  [0,2,2,0,2,0,2,1,0,0,0,1,0,0,1],
  [0,0,2,2,1,0,1,1,1,0,2,1,2,2,0,1,1],
  [1,1,0,1,1,2,0,0,2,1,2,0,1,0,2,0,2,0,0]
]

def cert0864n : CertifiedBoard :=
  ⟨seed0864, by apply FastValid.valid; decide +kernel⟩

def cert0864r : CertifiedBoard :=
  ⟨seed0864.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0865 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,1,2,1,1,1,0,0,2,1],
  [2,1,0,0,0,1,1,2,2,0,0,2,2,1,2],
  [1,0,2,0,1,0,0,0,2,0,2,0,0,1,1,0,1],
  [1,2,0,2,2,0,2,1,2,0,1,1,1,0,2,1,0,1,0]
]

def cert0865n : CertifiedBoard :=
  ⟨seed0865, by apply FastValid.valid; decide +kernel⟩

def cert0865r : CertifiedBoard :=
  ⟨seed0865.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0866 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,1,2,1,1,1,0,1,1,2],
  [0,0,1,1,1,0,0,2,0,2,1,2,0,0,0],
  [0,0,2,1,2,2,0,2,2,1,0,0,2,0,1,0,1],
  [1,2,0,0,1,0,2,2,0,2,1,0,2,0,1,1,0,0,0]
]

def cert0866n : CertifiedBoard :=
  ⟨seed0866, by apply FastValid.valid; decide +kernel⟩

def cert0866r : CertifiedBoard :=
  ⟨seed0866.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0867 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,1,2,1,1,1,1,0,0,2],
  [0,1,1,0,2,2,0,1,0,0,0,2,0,0,1],
  [0,2,1,2,2,0,2,1,2,0,1,0,1,1,0,2,0],
  [2,0,2,0,2,2,1,0,1,1,2,0,0,2,1,0,0,0,1]
]

def cert0867n : CertifiedBoard :=
  ⟨seed0867, by apply FastValid.valid; decide +kernel⟩

def cert0867r : CertifiedBoard :=
  ⟨seed0867.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0868 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,1,2,1,1,1,1,0,1,1],
  [1,0,0,2,1,0,0,2,1,2,2,0,1,1,0],
  [2,0,2,0,0,0,0,2,2,1,0,2,0,2,0,0,1],
  [1,1,2,0,1,0,1,1,0,0,1,0,2,2,0,2,1,2,0]
]

def cert0868n : CertifiedBoard :=
  ⟨seed0868, by apply FastValid.valid; decide +kernel⟩

def cert0868r : CertifiedBoard :=
  ⟨seed0868.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0869 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,1,2,1,1,1,1,0,1,1],
  [1,0,0,2,1,0,0,2,1,2,2,0,1,1,0],
  [2,0,2,0,0,0,0,2,2,1,0,2,0,2,0,0,1],
  [1,1,2,0,1,1,0,1,0,0,1,0,2,2,0,2,1,2,0]
]

def cert0869n : CertifiedBoard :=
  ⟨seed0869, by apply FastValid.valid; decide +kernel⟩

def cert0869r : CertifiedBoard :=
  ⟨seed0869.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0870 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,1,2,1,1,1,1,0,2,0],
  [1,0,0,0,0,1,1,2,2,0,0,2,0,1,0],
  [2,0,2,1,0,1,1,0,0,2,2,0,2,1,2,0,1],
  [2,0,2,2,1,0,2,1,2,0,0,1,1,0,1,0,0,2,0]
]

def cert0870n : CertifiedBoard :=
  ⟨seed0870, by apply FastValid.valid; decide +kernel⟩

def cert0870r : CertifiedBoard :=
  ⟨seed0870.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0871 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,1,2,1,1,1,1,0,2,0],
  [1,0,0,0,2,1,0,0,2,1,2,0,2,1,0],
  [2,0,2,2,0,1,1,0,2,0,2,0,1,0,1,0,1],
  [0,0,0,2,2,1,2,2,0,0,1,1,2,0,0,1,1,0,0]
]

def cert0871n : CertifiedBoard :=
  ⟨seed0871, by apply FastValid.valid; decide +kernel⟩

def cert0871r : CertifiedBoard :=
  ⟨seed0871.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0872 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,1,2,2,1,0,0,0,2,1],
  [0,0,2,1,1,0,0,1,1,0,0,1,1,1,1],
  [2,1,0,2,2,0,2,1,2,1,2,0,0,2,0,0,0],
  [1,1,2,0,2,0,2,0,1,0,1,1,0,1,0,2,2,0,1]
]

def cert0872n : CertifiedBoard :=
  ⟨seed0872, by apply FastValid.valid; decide +kernel⟩

def cert0872r : CertifiedBoard :=
  ⟨seed0872.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0873 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,1,2,2,1,0,0,1,1,2],
  [1,2,0,0,0,1,1,0,1,0,1,0,0,2,2],
  [2,2,0,2,0,1,1,1,0,0,0,2,1,0,2,0,1],
  [2,1,1,1,0,2,1,2,0,2,2,0,0,2,0,2,1,2,1]
]

def cert0873n : CertifiedBoard :=
  ⟨seed0873, by apply FastValid.valid; decide +kernel⟩

def cert0873r : CertifiedBoard :=
  ⟨seed0873.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0874 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,1,2,2,1,0,0,2,1,1],
  [1,0,1,1,1,0,0,0,1,0,0,2,0,2,0],
  [1,1,0,2,1,2,1,2,0,0,2,0,2,2,0,1,0],
  [2,0,0,0,1,1,1,2,0,2,1,0,1,1,0,2,2,0,1]
]

def cert0874n : CertifiedBoard :=
  ⟨seed0874, by apply FastValid.valid; decide +kernel⟩

def cert0874r : CertifiedBoard :=
  ⟨seed0874.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0875 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,1,2,2,1,0,1,1,1,0],
  [0,2,2,0,2,0,0,0,2,0,2,1,2,0,0],
  [1,0,2,0,1,0,0,1,1,0,2,1,1,1,2,0,1],
  [0,0,0,2,1,2,1,0,1,1,0,0,1,0,0,2,2,0,2]
]

def cert0875n : CertifiedBoard :=
  ⟨seed0875, by apply FastValid.valid; decide +kernel⟩

def cert0875r : CertifiedBoard :=
  ⟨seed0875.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0876 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,1,2,2,1,0,1,1,1,0],
  [1,0,0,0,0,1,0,2,2,0,1,1,1,0,1],
  [2,0,0,2,0,2,1,2,0,2,1,2,0,2,1,0,0],
  [0,0,1,0,2,0,0,2,0,1,1,2,1,1,0,0,2,2,0]
]

def cert0876n : CertifiedBoard :=
  ⟨seed0876, by apply FastValid.valid; decide +kernel⟩

def cert0876r : CertifiedBoard :=
  ⟨seed0876.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0877 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,1,2,2,1,0,2,1,1,0],
  [2,0,1,1,2,0,0,1,1,1,0,1,0,0,1],
  [0,0,2,0,2,0,2,1,2,1,2,0,2,1,0,0,0],
  [1,0,1,0,0,2,0,0,0,2,2,0,1,1,1,0,2,2,0]
]

def cert0877n : CertifiedBoard :=
  ⟨seed0877, by apply FastValid.valid; decide +kernel⟩

def cert0877r : CertifiedBoard :=
  ⟨seed0877.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0878 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,2,0,0,0,0,2,0,2,2],
  [0,2,1,0,2,2,1,2,0,2,0,1,1,1,0],
  [1,0,0,1,0,1,1,2,1,1,0,0,1,1,1,0,2],
  [2,2,0,0,2,1,0,0,2,1,2,2,0,1,2,0,1,0,1]
]

def cert0878n : CertifiedBoard :=
  ⟨seed0878, by apply FastValid.valid; decide +kernel⟩

def cert0878r : CertifiedBoard :=
  ⟨seed0878.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0879 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,2,0,0,0,0,2,1,1,1],
  [2,1,2,0,1,1,2,0,2,0,0,1,2,1,0],
  [1,0,1,0,0,1,1,0,2,2,1,0,0,2,2,0,1],
  [1,1,1,0,0,2,1,2,2,0,2,0,1,0,1,1,0,2,1]
]

def cert0879n : CertifiedBoard :=
  ⟨seed0879, by apply FastValid.valid; decide +kernel⟩

def cert0879r : CertifiedBoard :=
  ⟨seed0879.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0880 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,2,0,0,0,2,1,1,1,0],
  [2,1,2,0,2,2,1,0,1,0,1,2,2,0,1],
  [1,0,0,0,2,0,1,1,1,0,0,1,0,2,0,2,1],
  [2,1,2,0,0,2,2,0,1,1,0,2,1,0,0,1,1,2,1]
]

def cert0880n : CertifiedBoard :=
  ⟨seed0880, by apply FastValid.valid; decide +kernel⟩

def cert0880r : CertifiedBoard :=
  ⟨seed0880.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0881 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,2,0,0,1,0,1,1,1,0],
  [0,2,1,0,0,2,0,1,0,0,1,1,1,0,2],
  [0,1,1,2,0,2,2,1,2,2,0,0,2,1,2,0,1],
  [1,0,1,2,1,1,0,2,2,0,2,1,0,0,0,0,2,0,1]
]

def cert0881n : CertifiedBoard :=
  ⟨seed0881, by apply FastValid.valid; decide +kernel⟩

def cert0881r : CertifiedBoard :=
  ⟨seed0881.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0882 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,2,0,0,1,1,0,2,2,1],
  [2,1,2,1,1,0,1,0,1,2,2,0,1,1,0],
  [1,0,0,2,0,1,0,2,1,0,0,0,2,1,2,0,0],
  [0,0,0,2,0,2,2,0,2,1,0,0,1,1,1,1,2,0,1]
]

def cert0882n : CertifiedBoard :=
  ⟨seed0882, by apply FastValid.valid; decide +kernel⟩

def cert0882r : CertifiedBoard :=
  ⟨seed0882.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0883 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,2,0,0,1,1,1,0,2,0],
  [0,1,1,1,2,0,1,0,2,1,2,0,0,0,1],
  [2,0,1,2,2,0,2,1,0,1,1,0,0,2,2,0,1],
  [2,1,1,0,0,2,1,0,1,0,0,0,2,0,2,2,1,2,1]
]

def cert0883n : CertifiedBoard :=
  ⟨seed0883, by apply FastValid.valid; decide +kernel⟩

def cert0883r : CertifiedBoard :=
  ⟨seed0883.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0884 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,2,0,0,2,1,1,1,0,1],
  [0,1,1,1,2,0,2,0,2,0,1,2,0,1,0],
  [0,2,1,2,1,0,0,2,1,0,2,2,0,1,0,0,1],
  [1,0,0,0,0,1,1,0,1,1,0,2,2,1,2,2,0,0,2]
]

def cert0884n : CertifiedBoard :=
  ⟨seed0884, by apply FastValid.valid; decide +kernel⟩

def cert0884r : CertifiedBoard :=
  ⟨seed0884.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0885 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,2,0,1,1,1,1,0,0,0],
  [0,2,0,0,2,2,1,2,1,2,2,0,1,0,1],
  [0,0,2,0,2,1,1,2,0,1,0,2,1,0,0,1,1],
  [1,1,0,2,2,0,2,1,0,1,1,0,0,1,2,0,0,0,2]
]

def cert0885n : CertifiedBoard :=
  ⟨seed0885, by apply FastValid.valid; decide +kernel⟩

def cert0885r : CertifiedBoard :=
  ⟨seed0885.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0886 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,2,1,0,0,0,2,1,1,0],
  [0,0,1,0,1,1,2,1,0,2,0,1,1,0,1],
  [0,2,1,2,0,1,2,2,1,2,0,2,2,0,1,0,0],
  [1,0,0,0,2,2,0,0,1,1,1,1,0,2,0,2,0,0,2]
]

def cert0886n : CertifiedBoard :=
  ⟨seed0886, by apply FastValid.valid; decide +kernel⟩

def cert0886r : CertifiedBoard :=
  ⟨seed0886.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0887 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,2,1,0,0,2,2,1,1,2],
  [1,0,0,0,1,0,1,2,0,0,2,0,1,1,0],
  [1,2,0,2,0,1,0,2,0,1,1,0,2,1,2,1,0],
  [1,0,0,0,2,1,2,2,0,2,2,0,0,1,1,1,1,0,1]
]

def cert0887n : CertifiedBoard :=
  ⟨seed0887, by apply FastValid.valid; decide +kernel⟩

def cert0887r : CertifiedBoard :=
  ⟨seed0887.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0888 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,2,1,0,1,1,1,0,0,1],
  [0,2,2,0,2,1,1,0,1,2,1,2,0,1,0],
  [1,0,2,2,1,0,2,0,1,0,0,0,2,1,2,0,0],
  [0,0,0,1,1,2,2,0,1,1,1,0,0,2,0,0,2,0,2]
]

def cert0888n : CertifiedBoard :=
  ⟨seed0888, by apply FastValid.valid; decide +kernel⟩

def cert0888r : CertifiedBoard :=
  ⟨seed0888.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0889 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,2,1,0,1,1,1,0,2,0],
  [2,0,0,0,2,1,1,0,0,2,0,1,0,0,1],
  [0,0,1,1,0,2,1,2,0,2,2,1,2,1,0,1,2],
  [1,2,0,1,0,0,2,2,0,2,0,1,1,1,2,2,0,0,0]
]

def cert0889n : CertifiedBoard :=
  ⟨seed0889, by apply FastValid.valid; decide +kernel⟩

def cert0889r : CertifiedBoard :=
  ⟨seed0889.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0890 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,2,1,0,2,0,1,1,1,0],
  [0,1,0,0,1,1,2,0,2,2,0,1,1,0,1],
  [1,0,0,0,2,1,2,2,1,0,0,2,2,0,0,1,2],
  [1,2,1,2,0,0,0,2,1,1,1,0,2,0,2,0,1,0,1]
]

def cert0890n : CertifiedBoard :=
  ⟨seed0890, by apply FastValid.valid; decide +kernel⟩

def cert0890r : CertifiedBoard :=
  ⟨seed0890.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0891 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,2,1,0,2,0,2,1,1,2],
  [0,1,1,1,0,1,1,0,2,0,0,1,0,0,2],
  [0,2,1,2,0,0,1,2,1,0,0,2,2,0,1,0,1],
  [1,2,0,1,1,1,0,0,0,0,2,0,2,2,1,2,2,0,1]
]

def cert0891n : CertifiedBoard :=
  ⟨seed0891, by apply FastValid.valid; decide +kernel⟩

def cert0891r : CertifiedBoard :=
  ⟨seed0891.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0892 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,1,0,0,0,0,2,2,1,1,2],
  [0,0,2,1,2,2,0,0,1,0,1,2,1,0,2],
  [1,1,0,1,1,1,1,0,2,1,2,0,0,2,1,0,0],
  [1,2,0,2,2,0,1,1,0,0,1,2,0,2,0,2,0,1,1]
]

def cert0892n : CertifiedBoard :=
  ⟨seed0892, by apply FastValid.valid; decide +kernel⟩

def cert0892r : CertifiedBoard :=
  ⟨seed0892.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0893 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,1,0,0,0,1,1,0,0,0,2],
  [2,1,2,0,0,2,2,0,2,0,1,0,0,1,2],
  [1,1,2,2,1,0,1,1,1,0,1,1,0,2,0,2,1],
  [1,2,1,0,2,2,0,1,2,0,0,2,1,2,0,2,1,1,1]
]

def cert0893n : CertifiedBoard :=
  ⟨seed0893, by apply FastValid.valid; decide +kernel⟩

def cert0893r : CertifiedBoard :=
  ⟨seed0893.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0894 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,1,0,0,0,1,1,2,0,2,2],
  [1,0,0,0,2,1,2,0,2,0,0,2,2,1,1],
  [2,2,0,1,1,0,0,2,1,0,1,0,1,1,1,1,0],
  [1,1,0,2,1,2,0,0,1,2,2,0,2,0,1,2,1,0,2]
]

def cert0894n : CertifiedBoard :=
  ⟨seed0894, by apply FastValid.valid; decide +kernel⟩

def cert0894r : CertifiedBoard :=
  ⟨seed0894.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0895 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,1,0,0,0,2,1,1,1,0,2],
  [0,2,0,2,1,0,0,2,2,1,2,2,0,2,1],
  [2,1,0,0,1,1,1,0,1,2,0,0,0,1,0,1,1],
  [1,1,2,1,2,0,1,2,0,0,2,2,0,1,1,0,2,0,2]
]

def cert0895n : CertifiedBoard :=
  ⟨seed0895, by apply FastValid.valid; decide +kernel⟩

def cert0895r : CertifiedBoard :=
  ⟨seed0895.map List.reverse, by apply FastValid.valid; decide +kernel⟩

end TBoards.Extended
