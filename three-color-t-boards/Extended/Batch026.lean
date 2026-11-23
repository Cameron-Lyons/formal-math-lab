import Extended.Batch022

/- Generated from extended_seeds.json. Published seeds 0–4:
   Qiyuan Ma, DOI 10.5281/zenodo.23631079, CC-BY-4.0. -/

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.Extended

def seed0832 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,1,1,1,2,1,1,0,1,1],
  [1,0,2,0,1,1,0,0,0,0,2,1,2,2,0],
  [2,0,2,0,2,1,2,0,1,0,0,2,0,0,2,1,0],
  [1,1,1,0,2,2,1,0,0,1,2,0,2,2,0,0,1,0,1]
]

def cert0832n : CertifiedBoard :=
  ⟨seed0832, by apply FastValid.valid; decide +kernel⟩

def cert0832r : CertifiedBoard :=
  ⟨seed0832.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0833 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,1,1,1,2,1,1,1,0,1],
  [2,1,0,0,2,1,2,2,0,2,0,0,0,2,1],
  [1,0,0,2,2,0,1,0,2,0,0,0,1,0,2,1,0],
  [2,0,2,0,2,2,1,2,0,1,1,0,1,1,0,0,1,2,0]
]

def cert0833n : CertifiedBoard :=
  ⟨seed0833, by apply FastValid.valid; decide +kernel⟩

def cert0833r : CertifiedBoard :=
  ⟨seed0833.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0834 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,1,1,1,2,1,1,1,0,1],
  [2,1,2,0,1,1,0,0,0,1,2,2,0,0,2],
  [0,2,0,0,2,0,2,1,0,0,1,0,0,0,2,2,1],
  [1,0,1,1,0,2,2,0,2,0,2,1,2,0,1,0,2,1,0]
]

def cert0834n : CertifiedBoard :=
  ⟨seed0834, by apply FastValid.valid; decide +kernel⟩

def cert0834r : CertifiedBoard :=
  ⟨seed0834.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0835 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,1,1,1,2,1,1,1,0,2],
  [0,2,0,0,0,1,2,0,2,1,2,2,0,0,1],
  [0,2,2,1,0,1,1,0,1,0,0,0,2,2,0,1,0],
  [1,0,2,0,2,0,2,1,0,0,2,1,2,0,1,1,0,0,2]
]

def cert0835n : CertifiedBoard :=
  ⟨seed0835, by apply FastValid.valid; decide +kernel⟩

def cert0835r : CertifiedBoard :=
  ⟨seed0835.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0836 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,1,1,1,2,1,1,1,0,2],
  [0,2,0,0,0,1,2,2,0,2,1,2,0,0,2],
  [1,0,2,0,1,0,0,0,1,1,0,0,2,1,2,0,1],
  [0,2,0,2,2,0,2,1,0,1,0,0,2,2,1,0,1,1,0]
]

def cert0836n : CertifiedBoard :=
  ⟨seed0836, by apply FastValid.valid; decide +kernel⟩

def cert0836r : CertifiedBoard :=
  ⟨seed0836.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0837 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,1,1,1,2,1,1,1,0,2],
  [0,2,1,0,1,1,0,0,0,2,1,2,2,0,1],
  [2,0,0,1,0,2,0,0,1,0,0,0,2,2,1,2,0],
  [1,0,0,2,2,0,1,1,0,1,2,0,2,0,2,0,2,1,0]
]

def cert0837n : CertifiedBoard :=
  ⟨seed0837, by apply FastValid.valid; decide +kernel⟩

def cert0837r : CertifiedBoard :=
  ⟨seed0837.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0838 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,1,1,1,2,1,1,1,0,2],
  [1,0,0,0,0,1,0,0,2,1,2,2,0,0,1],
  [2,0,2,1,0,1,1,0,2,2,1,0,0,2,0,2,0],
  [0,2,2,0,2,1,2,0,0,2,0,1,2,0,1,1,0,1,0]
]

def cert0838n : CertifiedBoard :=
  ⟨seed0838, by apply FastValid.valid; decide +kernel⟩

def cert0838r : CertifiedBoard :=
  ⟨seed0838.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0839 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,1,1,1,2,2,1,1,0,1],
  [0,2,0,0,1,1,0,0,2,0,2,1,2,0,2],
  [2,0,0,2,1,2,1,0,0,2,1,0,0,0,0,1,1],
  [1,1,1,0,2,2,0,1,0,1,0,2,0,2,2,0,1,2,0]
]

def cert0839n : CertifiedBoard :=
  ⟨seed0839, by apply FastValid.valid; decide +kernel⟩

def cert0839r : CertifiedBoard :=
  ⟨seed0839.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0840 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,1,1,1,2,2,1,1,0,1],
  [1,0,0,2,1,2,0,0,0,2,0,2,1,0,0],
  [0,1,2,0,2,2,0,2,2,0,0,1,1,1,0,1,0],
  [0,0,1,0,2,0,1,1,0,0,0,2,1,2,1,0,2,0,1]
]

def cert0840n : CertifiedBoard :=
  ⟨seed0840, by apply FastValid.valid; decide +kernel⟩

def cert0840r : CertifiedBoard :=
  ⟨seed0840.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0841 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,1,1,1,2,2,1,1,1,0],
  [0,0,1,0,2,2,0,0,2,0,2,1,2,1,2],
  [1,0,1,1,0,0,2,2,0,0,0,2,1,0,0,0,1],
  [1,2,0,2,0,2,1,0,1,1,0,2,0,1,2,0,1,0,0]
]

def cert0841n : CertifiedBoard :=
  ⟨seed0841, by apply FastValid.valid; decide +kernel⟩

def cert0841r : CertifiedBoard :=
  ⟨seed0841.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0842 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,1,1,1,2,2,1,1,1,0],
  [0,0,2,0,1,1,0,0,0,2,1,2,1,0,1],
  [1,0,2,0,2,2,0,2,1,0,0,0,2,0,0,1,2],
  [1,2,0,0,1,0,1,1,0,2,1,2,0,2,2,0,1,0,0]
]

def cert0842n : CertifiedBoard :=
  ⟨seed0842, by apply FastValid.valid; decide +kernel⟩

def cert0842r : CertifiedBoard :=
  ⟨seed0842.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0843 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,1,1,1,2,2,1,1,1,0],
  [1,0,0,2,2,0,2,0,0,0,1,0,0,0,2],
  [2,1,2,0,2,0,2,0,1,0,1,1,0,2,1,0,1],
  [0,2,1,0,0,1,1,0,2,2,0,1,2,0,0,2,1,2,1]
]

def cert0843n : CertifiedBoard :=
  ⟨seed0843, by apply FastValid.valid; decide +kernel⟩

def cert0843r : CertifiedBoard :=
  ⟨seed0843.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0844 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,1,1,1,2,2,1,1,1,0],
  [1,0,0,2,2,0,2,0,0,0,2,1,2,1,2],
  [1,0,0,1,0,2,0,2,1,0,2,0,1,0,0,0,1],
  [1,2,0,1,1,0,1,1,0,1,2,0,2,2,0,0,2,1,0]
]

def cert0844n : CertifiedBoard :=
  ⟨seed0844, by apply FastValid.valid; decide +kernel⟩

def cert0844r : CertifiedBoard :=
  ⟨seed0844.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0845 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,1,1,1,2,2,1,1,1,0],
  [1,0,1,0,1,1,0,0,0,0,1,2,1,2,0],
  [2,0,2,0,0,2,1,0,2,2,0,0,2,2,0,1,0],
  [1,0,0,1,1,0,0,2,0,2,0,2,1,0,2,1,2,0,1]
]

def cert0845n : CertifiedBoard :=
  ⟨seed0845, by apply FastValid.valid; decide +kernel⟩

def cert0845r : CertifiedBoard :=
  ⟨seed0845.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0846 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,1,1,1,2,2,1,1,1,0],
  [2,0,1,0,0,2,0,0,0,2,1,2,1,0,1],
  [1,0,1,1,0,2,0,2,1,0,0,0,2,0,2,2,0],
  [1,0,0,1,2,0,0,1,0,2,1,2,0,2,2,0,1,1,0]
]

def cert0846n : CertifiedBoard :=
  ⟨seed0846, by apply FastValid.valid; decide +kernel⟩

def cert0846r : CertifiedBoard :=
  ⟨seed0846.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0847 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,1,1,1,2,2,1,1,1,0],
  [2,0,1,0,1,1,0,0,0,0,1,2,1,0,1],
  [0,0,2,0,2,2,0,0,2,1,0,2,0,2,1,2,0],
  [1,0,0,1,1,0,2,2,0,2,1,2,0,1,0,0,2,0,0]
]

def cert0847n : CertifiedBoard :=
  ⟨seed0847, by apply FastValid.valid; decide +kernel⟩

def cert0847r : CertifiedBoard :=
  ⟨seed0847.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0848 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,1,1,1,2,2,1,1,1,0],
  [2,0,1,0,1,1,0,0,0,2,2,0,2,1,2],
  [1,0,2,1,0,2,0,0,2,0,0,1,1,0,0,2,0],
  [1,2,0,2,1,2,0,2,2,0,1,0,1,2,1,0,0,0,1]
]

def cert0848n : CertifiedBoard :=
  ⟨seed0848, by apply FastValid.valid; decide +kernel⟩

def cert0848r : CertifiedBoard :=
  ⟨seed0848.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0849 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,1,1,1,2,2,1,1,1,0],
  [2,1,2,0,2,1,2,1,0,2,2,0,2,0,0],
  [0,0,0,2,1,0,0,0,1,0,0,2,0,1,1,0,1],
  [1,0,2,2,0,1,2,0,2,0,0,1,0,1,1,0,0,2,1]
]

def cert0849n : CertifiedBoard :=
  ⟨seed0849, by apply FastValid.valid; decide +kernel⟩

def cert0849r : CertifiedBoard :=
  ⟨seed0849.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0850 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,1,1,1,2,2,1,1,1,0],
  [2,2,0,2,0,0,2,0,0,0,1,2,1,0,1],
  [2,0,1,1,0,2,1,0,0,1,0,0,0,2,1,2,0],
  [1,0,1,1,0,0,2,1,2,0,1,0,2,0,2,2,0,2,2]
]

def cert0850n : CertifiedBoard :=
  ⟨seed0850, by apply FastValid.valid; decide +kernel⟩

def cert0850r : CertifiedBoard :=
  ⟨seed0850.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0851 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,1,2,0,1,0,0,0,2,2],
  [0,0,1,1,2,0,0,1,1,1,0,2,2,1,1],
  [2,2,0,0,0,2,0,2,1,2,1,0,1,1,1,0,0],
  [1,1,0,1,0,0,2,1,0,2,0,2,1,2,2,0,2,0,1]
]

def cert0851n : CertifiedBoard :=
  ⟨seed0851, by apply FastValid.valid; decide +kernel⟩

def cert0851r : CertifiedBoard :=
  ⟨seed0851.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0852 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,1,2,0,1,0,1,1,1,2],
  [1,2,0,2,0,2,0,2,0,0,1,1,1,0,0],
  [0,0,0,1,1,0,0,2,2,1,0,2,1,2,2,0,1],
  [0,0,2,1,2,1,0,1,0,2,2,0,0,0,2,1,1,0,0]
]

def cert0852n : CertifiedBoard :=
  ⟨seed0852, by apply FastValid.valid; decide +kernel⟩

def cert0852r : CertifiedBoard :=
  ⟨seed0852.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0853 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,1,2,0,1,0,2,1,1,0],
  [1,0,0,0,1,1,1,1,0,0,2,2,0,0,1],
  [2,1,0,2,0,2,0,2,1,2,0,0,0,2,1,2,1],
  [1,1,2,2,0,2,2,1,0,0,2,0,1,0,1,1,0,1,1]
]

def cert0853n : CertifiedBoard :=
  ⟨seed0853, by apply FastValid.valid; decide +kernel⟩

def cert0853r : CertifiedBoard :=
  ⟨seed0853.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0854 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,1,2,0,1,0,2,2,1,1],
  [2,0,0,0,1,1,1,1,0,0,1,1,2,2,0],
  [1,1,0,2,2,0,2,0,0,2,0,1,1,0,0,0,2],
  [0,2,1,0,0,2,0,2,1,2,0,2,1,2,1,0,1,0,1]
]

def cert0854n : CertifiedBoard :=
  ⟨seed0854, by apply FastValid.valid; decide +kernel⟩

def cert0854r : CertifiedBoard :=
  ⟨seed0854.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0855 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,1,2,0,1,1,0,2,1,1],
  [2,0,0,0,1,1,1,2,0,0,2,2,1,0,0],
  [0,0,0,2,1,2,2,0,2,2,0,1,1,1,0,0,1],
  [1,1,0,1,0,1,0,0,2,0,2,0,2,1,2,1,0,2,0]
]

def cert0855n : CertifiedBoard :=
  ⟨seed0855, by apply FastValid.valid; decide +kernel⟩

def cert0855r : CertifiedBoard :=
  ⟨seed0855.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0856 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,1,2,0,2,0,1,1,0,1],
  [0,0,1,1,2,0,0,2,2,1,2,1,0,1,0],
  [0,2,1,0,0,2,2,0,2,1,1,1,1,0,0,0,2],
  [1,0,2,0,2,0,0,0,1,0,2,1,2,2,0,1,1,0,0]
]

def cert0856n : CertifiedBoard :=
  ⟨seed0856, by apply FastValid.valid; decide +kernel⟩

def cert0856r : CertifiedBoard :=
  ⟨seed0856.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0857 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,1,2,0,2,1,1,0,0,0],
  [1,0,1,1,2,0,2,0,2,1,0,0,1,1,0],
  [1,2,2,0,0,0,1,0,2,0,1,0,2,1,2,1,2],
  [0,0,2,2,1,0,0,2,0,0,2,2,0,1,1,1,1,0,1]
]

def cert0857n : CertifiedBoard :=
  ⟨seed0857, by apply FastValid.valid; decide +kernel⟩

def cert0857r : CertifiedBoard :=
  ⟨seed0857.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0858 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,1,2,0,2,1,1,1,0,1],
  [0,1,1,1,2,0,2,0,2,1,2,2,0,0,2],
  [0,0,1,1,0,0,2,2,1,0,2,0,1,1,0,0,0],
  [0,2,1,2,1,0,1,0,0,1,0,2,2,0,0,0,2,0,1]
]

def cert0858n : CertifiedBoard :=
  ⟨seed0858, by apply FastValid.valid; decide +kernel⟩

def cert0858r : CertifiedBoard :=
  ⟨seed0858.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0859 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,1,2,1,1,0,0,0,2,0],
  [1,0,1,0,1,1,1,0,0,0,2,0,1,1,0],
  [2,0,2,1,0,2,1,2,2,0,2,2,1,2,0,0,1],
  [0,2,1,0,2,0,0,1,1,1,2,0,2,2,0,1,0,0,2]
]

def cert0859n : CertifiedBoard :=
  ⟨seed0859, by apply FastValid.valid; decide +kernel⟩

def cert0859r : CertifiedBoard :=
  ⟨seed0859.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0860 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,1,2,1,1,0,0,1,1,1],
  [0,0,1,0,2,0,2,1,0,0,2,2,0,0,0],
  [1,0,2,1,2,0,1,1,2,2,0,2,2,1,0,1,0],
  [1,1,1,0,1,1,0,0,2,0,2,0,0,0,2,1,2,0,1]
]

def cert0860n : CertifiedBoard :=
  ⟨seed0860, by apply FastValid.valid; decide +kernel⟩

def cert0860r : CertifiedBoard :=
  ⟨seed0860.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0861 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,1,2,1,1,0,1,1,0,2],
  [0,0,1,1,2,0,2,1,2,0,2,1,0,0,0],
  [0,2,1,0,0,2,2,0,2,0,1,1,1,1,0,2,0],
  [2,0,0,1,0,1,0,0,2,2,1,2,2,0,0,0,2,0,1]
]

def cert0861n : CertifiedBoard :=
  ⟨seed0861, by apply FastValid.valid; decide +kernel⟩

def cert0861r : CertifiedBoard :=
  ⟨seed0861.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0862 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,1,2,1,1,0,1,1,1,0],
  [1,0,2,0,2,1,0,0,0,2,2,0,2,1,0],
  [1,0,0,2,0,2,1,2,0,1,0,2,2,0,1,0,1],
  [1,1,1,0,0,1,1,2,2,1,2,0,0,0,2,0,0,1,1]
]

def cert0862n : CertifiedBoard :=
  ⟨seed0862, by apply FastValid.valid; decide +kernel⟩

def cert0862r : CertifiedBoard :=
  ⟨seed0862.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0863 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,1,2,1,1,0,1,1,1,0],
  [2,2,0,0,1,1,1,2,2,0,2,1,2,0,1],
  [1,0,2,0,0,1,0,0,2,2,1,0,0,0,0,2,0],
  [2,0,2,0,1,0,1,1,0,0,2,1,0,2,1,2,0,2,2]
]

def cert0863n : CertifiedBoard :=
  ⟨seed0863, by apply FastValid.valid; decide +kernel⟩

def cert0863r : CertifiedBoard :=
  ⟨seed0863.map List.reverse, by apply FastValid.valid; decide +kernel⟩

end TBoards.Extended
