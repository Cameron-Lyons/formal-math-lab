import Extended.Batch024

/- Generated from extended_seeds.json. Published seeds 0–4:
   Qiyuan Ma, DOI 10.5281/zenodo.23631079, CC-BY-4.0. -/

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.Extended

def seed0896 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,1,0,0,0,2,1,1,1,2,0],
  [2,0,2,1,2,1,0,1,0,0,2,0,1,1,0],
  [1,0,2,2,1,0,1,2,0,2,0,0,1,1,1,0,2],
  [1,2,2,0,2,2,0,1,1,0,0,0,2,1,2,0,0,1,2]
]

def cert0896n : CertifiedBoard :=
  ⟨seed0896, by apply FastValid.valid; decide +kernel⟩

def cert0896r : CertifiedBoard :=
  ⟨seed0896.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0897 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,1,0,0,2,1,0,0,0,1,1],
  [2,0,0,2,2,0,2,0,2,1,2,0,1,2,0],
  [1,0,1,0,2,2,1,0,2,1,1,1,0,1,1,1,0],
  [1,1,0,0,0,1,2,0,1,1,2,1,2,2,0,2,0,0,2]
]

def cert0897n : CertifiedBoard :=
  ⟨seed0897, by apply FastValid.valid; decide +kernel⟩

def cert0897r : CertifiedBoard :=
  ⟨seed0897.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0898 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,1,0,0,2,1,0,0,1,1,1],
  [2,0,0,2,0,0,1,0,1,1,0,1,2,2,0],
  [2,0,2,1,0,2,2,0,1,1,1,0,2,1,1,2,0],
  [1,1,0,0,0,0,2,2,1,2,0,2,0,1,2,1,2,0,2]
]

def cert0898n : CertifiedBoard :=
  ⟨seed0898, by apply FastValid.valid; decide +kernel⟩

def cert0898r : CertifiedBoard :=
  ⟨seed0898.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0899 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,1,0,0,2,1,0,0,2,2,1],
  [2,1,2,0,2,1,0,0,0,0,2,1,1,2,2],
  [1,0,1,1,1,0,2,0,0,1,0,1,2,0,1,1,0],
  [2,2,0,1,2,1,2,0,2,2,0,2,0,0,1,1,1,0,2]
]

def cert0899n : CertifiedBoard :=
  ⟨seed0899, by apply FastValid.valid; decide +kernel⟩

def cert0899r : CertifiedBoard :=
  ⟨seed0899.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0900 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,1,0,0,2,1,0,1,1,2,0],
  [2,0,0,2,0,1,0,0,0,0,1,2,2,1,2],
  [1,1,1,0,1,2,0,0,2,2,0,1,1,0,2,1,1],
  [1,2,1,2,0,2,0,2,1,0,0,1,1,1,0,2,2,0,2]
]

def cert0900n : CertifiedBoard :=
  ⟨seed0900, by apply FastValid.valid; decide +kernel⟩

def cert0900r : CertifiedBoard :=
  ⟨seed0900.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0901 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,1,0,0,2,1,2,0,2,2,1],
  [1,0,1,2,0,0,1,0,2,1,1,0,1,1,0],
  [2,1,0,0,0,0,2,2,0,0,1,2,1,2,0,1,1],
  [1,1,2,2,0,2,1,0,0,2,0,1,1,1,1,0,2,0,2]
]

def cert0901n : CertifiedBoard :=
  ⟨seed0901, by apply FastValid.valid; decide +kernel⟩

def cert0901r : CertifiedBoard :=
  ⟨seed0901.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0902 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,1,1,0,0,0,0,2,1,1,0],
  [0,2,2,1,2,2,0,0,1,1,0,2,1,0,0],
  [1,0,1,1,1,1,2,0,2,0,2,0,1,2,1,0,2],
  [0,0,2,1,2,0,1,0,1,0,0,2,2,0,0,1,2,0,2]
]

def cert0902n : CertifiedBoard :=
  ⟨seed0902, by apply FastValid.valid; decide +kernel⟩

def cert0902r : CertifiedBoard :=
  ⟨seed0902.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0903 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,1,1,0,0,0,2,1,1,0,2],
  [2,2,0,2,0,0,0,1,0,0,1,2,0,2,2],
  [1,1,2,0,0,2,1,0,2,0,1,1,1,1,0,1,1],
  [2,0,1,0,0,2,2,1,0,1,2,0,2,1,2,1,2,2,0]
]

def cert0903n : CertifiedBoard :=
  ⟨seed0903, by apply FastValid.valid; decide +kernel⟩

def cert0903r : CertifiedBoard :=
  ⟨seed0903.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0904 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,1,1,0,0,0,2,1,1,1,0],
  [1,0,2,2,0,2,0,1,0,0,1,2,2,0,2],
  [0,2,1,0,1,1,0,2,1,0,1,1,1,2,0,0,2],
  [0,2,2,1,2,0,0,0,1,2,1,2,0,1,0,0,2,0,2]
]

def cert0904n : CertifiedBoard :=
  ⟨seed0904, by apply FastValid.valid; decide +kernel⟩

def cert0904r : CertifiedBoard :=
  ⟨seed0904.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0905 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,1,1,0,0,0,2,2,1,1,2],
  [1,2,0,2,0,0,0,1,0,0,1,2,1,2,0],
  [1,1,1,0,1,1,0,2,2,0,2,1,0,1,0,0,2],
  [2,0,1,2,2,0,2,0,0,2,1,0,2,1,2,0,1,1,1]
]

def cert0905n : CertifiedBoard :=
  ⟨seed0905, by apply FastValid.valid; decide +kernel⟩

def cert0905r : CertifiedBoard :=
  ⟨seed0905.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0906 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,1,1,0,0,1,0,1,2,0,2],
  [2,1,0,2,1,2,2,0,2,1,2,1,1,0,0],
  [0,2,1,0,1,1,1,1,0,0,0,0,2,0,1,0,2],
  [0,0,2,2,0,1,2,0,0,2,0,0,1,1,2,0,2,2,1]
]

def cert0906n : CertifiedBoard :=
  ⟨seed0906, by apply FastValid.valid; decide +kernel⟩

def cert0906r : CertifiedBoard :=
  ⟨seed0906.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0907 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,1,1,0,0,2,1,1,0,1,2],
  [2,0,2,2,0,0,0,2,2,1,2,0,1,0,2],
  [1,2,0,0,0,1,1,0,1,1,1,1,2,0,1,0,0],
  [0,0,2,1,0,0,1,2,1,2,2,0,2,0,2,1,0,2,0]
]

def cert0907n : CertifiedBoard :=
  ⟨seed0907, by apply FastValid.valid; decide +kernel⟩

def cert0907r : CertifiedBoard :=
  ⟨seed0907.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0908 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,1,1,0,0,2,1,1,1,2,0],
  [1,2,0,2,1,2,1,0,0,1,2,0,2,1,2],
  [0,0,0,0,1,2,2,1,0,2,0,1,1,0,1,0,0],
  [2,0,1,0,1,1,1,0,2,0,2,2,0,0,2,2,0,0,2]
]

def cert0908n : CertifiedBoard :=
  ⟨seed0908, by apply FastValid.valid; decide +kernel⟩

def cert0908r : CertifiedBoard :=
  ⟨seed0908.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0909 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,1,1,1,0,0,2,1,1,1,0],
  [1,0,0,2,1,2,0,1,0,2,2,0,2,0,0],
  [0,0,0,1,1,2,2,1,2,1,0,1,1,0,2,0,2],
  [0,2,2,0,1,0,0,0,1,2,0,0,2,1,0,1,2,0,2]
]

def cert0909n : CertifiedBoard :=
  ⟨seed0909, by apply FastValid.valid; decide +kernel⟩

def cert0909r : CertifiedBoard :=
  ⟨seed0909.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0910 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,1,1,1,0,0,2,1,1,1,0],
  [1,0,0,2,2,0,0,0,1,1,2,1,2,0,2],
  [0,1,0,1,0,2,2,0,0,2,0,1,2,2,1,0,1],
  [0,2,1,0,2,1,2,0,2,0,1,1,0,0,0,1,2,0,2]
]

def cert0910n : CertifiedBoard :=
  ⟨seed0910, by apply FastValid.valid; decide +kernel⟩

def cert0910r : CertifiedBoard :=
  ⟨seed0910.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0911 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,1,1,1,0,0,2,1,1,1,0],
  [2,0,0,0,2,1,2,1,0,2,2,0,1,0,0],
  [1,0,1,1,0,1,2,0,2,0,1,1,2,0,2,0,2],
  [0,0,0,1,2,2,0,0,1,0,2,1,0,0,2,2,1,2,0]
]

def cert0911n : CertifiedBoard :=
  ⟨seed0911, by apply FastValid.valid; decide +kernel⟩

def cert0911r : CertifiedBoard :=
  ⟨seed0911.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0912 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,1,1,1,0,0,2,2,1,1,0],
  [1,0,0,2,2,0,0,0,1,1,1,2,0,2,1],
  [1,2,2,0,0,1,1,0,2,0,1,0,0,0,2,1,2],
  [2,1,0,1,2,0,1,2,1,2,0,2,1,0,1,0,2,0,2]
]

def cert0912n : CertifiedBoard :=
  ⟨seed0912, by apply FastValid.valid; decide +kernel⟩

def cert0912r : CertifiedBoard :=
  ⟨seed0912.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0913 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,1,1,1,0,2,1,1,2,0,2],
  [1,0,0,2,2,0,0,0,2,1,0,0,1,1,0],
  [2,0,2,0,1,1,1,0,1,0,1,0,2,1,2,2,0],
  [1,0,0,1,2,0,1,2,1,2,0,2,0,0,0,2,2,1,0]
]

def cert0913n : CertifiedBoard :=
  ⟨seed0913, by apply FastValid.valid; decide +kernel⟩

def cert0913r : CertifiedBoard :=
  ⟨seed0913.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0914 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,1,2,0,0,0,2,1,1,1,2],
  [0,1,0,1,1,0,2,2,0,1,2,1,0,0,2],
  [1,2,0,2,0,1,0,1,1,0,2,0,2,1,0,0,1],
  [1,2,2,1,2,0,0,0,1,1,1,0,0,2,2,0,2,1,2]
]

def cert0914n : CertifiedBoard :=
  ⟨seed0914, by apply FastValid.valid; decide +kernel⟩

def cert0914r : CertifiedBoard :=
  ⟨seed0914.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0915 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,1,2,0,0,1,0,1,1,1,0],
  [0,2,1,1,0,0,0,2,2,0,1,1,1,0,1],
  [0,1,1,2,1,2,0,2,0,2,2,0,2,1,0,0,2],
  [1,0,2,0,1,2,2,1,2,0,0,2,1,0,0,0,1,0,2]
]

def cert0915n : CertifiedBoard :=
  ⟨seed0915, by apply FastValid.valid; decide +kernel⟩

def cert0915r : CertifiedBoard :=
  ⟨seed0915.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0916 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,1,2,0,0,1,0,1,1,2,0],
  [1,0,1,2,0,2,1,0,0,0,1,1,1,1,0],
  [2,0,1,0,0,2,2,1,0,2,1,2,1,2,2,0,0],
  [0,0,0,2,0,1,1,0,0,2,0,2,1,1,0,2,2,0,2]
]

def cert0916n : CertifiedBoard :=
  ⟨seed0916, by apply FastValid.valid; decide +kernel⟩

def cert0916r : CertifiedBoard :=
  ⟨seed0916.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0917 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,1,2,0,0,1,0,2,1,1,1],
  [1,1,0,1,1,1,2,0,0,0,1,2,2,0,1],
  [0,2,1,0,1,1,0,0,0,2,0,2,0,2,2,0,2],
  [0,1,0,0,2,1,2,1,0,2,2,1,2,0,1,1,0,0,2]
]

def cert0917n : CertifiedBoard :=
  ⟨seed0917, by apply FastValid.valid; decide +kernel⟩

def cert0917r : CertifiedBoard :=
  ⟨seed0917.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0918 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,1,2,0,0,1,1,1,0,0,0],
  [0,2,2,1,2,1,1,0,0,2,1,0,2,0,1],
  [0,1,1,2,0,1,1,1,0,1,0,2,0,2,2,0,2],
  [0,0,1,0,0,2,1,2,2,0,0,0,2,1,0,1,2,0,2]
]

def cert0918n : CertifiedBoard :=
  ⟨seed0918, by apply FastValid.valid; decide +kernel⟩

def cert0918r : CertifiedBoard :=
  ⟨seed0918.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0919 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,1,2,0,0,1,1,1,0,0,0],
  [0,2,2,1,2,1,1,0,0,2,1,0,2,0,2],
  [0,1,1,2,0,1,1,1,0,1,0,2,0,1,2,0,2],
  [0,0,1,0,0,2,1,2,2,0,0,0,2,2,0,2,1,0,1]
]

def cert0919n : CertifiedBoard :=
  ⟨seed0919, by apply FastValid.valid; decide +kernel⟩

def cert0919r : CertifiedBoard :=
  ⟨seed0919.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0920 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,1,2,0,1,1,0,0,2,2,1],
  [1,2,0,2,1,0,1,0,0,0,1,1,1,2,1],
  [2,1,2,0,0,1,0,1,1,0,2,0,2,0,0,0,2],
  [2,1,1,1,0,0,2,1,2,2,0,2,1,0,2,2,0,1,2]
]

def cert0920n : CertifiedBoard :=
  ⟨seed0920, by apply FastValid.valid; decide +kernel⟩

def cert0920r : CertifiedBoard :=
  ⟨seed0920.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0921 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,1,2,0,1,1,1,0,2,1,1],
  [1,0,2,2,0,0,2,2,0,2,0,0,1,1,0],
  [0,0,0,1,2,0,1,1,1,2,0,2,1,2,1,0,0],
  [1,1,0,1,0,0,0,2,1,2,2,1,0,1,0,0,2,0,2]
]

def cert0921n : CertifiedBoard :=
  ⟨seed0921, by apply FastValid.valid; decide +kernel⟩

def cert0921r : CertifiedBoard :=
  ⟨seed0921.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0922 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,1,2,0,1,2,1,1,0,0,2],
  [2,1,0,2,1,2,0,2,0,2,1,0,0,2,1],
  [0,0,1,0,1,1,1,1,0,1,1,2,2,0,0,0,0],
  [1,0,2,0,0,1,1,0,0,2,2,0,2,2,1,2,0,1,0]
]

def cert0922n : CertifiedBoard :=
  ⟨seed0922, by apply FastValid.valid; decide +kernel⟩

def cert0922r : CertifiedBoard :=
  ⟨seed0922.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0923 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,1,2,0,1,2,1,1,2,0,2],
  [0,1,1,0,0,2,2,0,0,1,1,1,1,0,1],
  [2,0,1,0,0,1,0,2,1,0,2,1,2,2,0,0,0],
  [0,0,0,2,0,2,0,2,2,1,0,1,1,0,0,2,1,2,0]
]

def cert0923n : CertifiedBoard :=
  ⟨seed0923, by apply FastValid.valid; decide +kernel⟩

def cert0923r : CertifiedBoard :=
  ⟨seed0923.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0924 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,1,2,0,1,2,2,1,1,2,0],
  [2,0,0,0,1,1,1,0,0,1,1,1,0,1,0],
  [1,0,0,2,0,2,1,2,1,2,0,0,0,2,2,0,1],
  [0,1,0,1,1,0,2,1,0,2,0,2,1,0,0,2,2,0,2]
]

def cert0924n : CertifiedBoard :=
  ⟨seed0924, by apply FastValid.valid; decide +kernel⟩

def cert0924r : CertifiedBoard :=
  ⟨seed0924.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0925 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,1,2,1,0,0,0,1,1,2,0],
  [1,1,0,1,1,0,2,1,2,0,1,0,0,0,2],
  [1,2,2,0,2,0,2,1,1,1,0,0,2,0,0,1,2],
  [2,0,0,2,2,0,2,2,1,2,0,1,0,2,1,0,1,1,1]
]

def cert0925n : CertifiedBoard :=
  ⟨seed0925, by apply FastValid.valid; decide +kernel⟩

def cert0925r : CertifiedBoard :=
  ⟨seed0925.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0926 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,1,2,1,0,0,2,1,1,0,2],
  [0,1,1,2,0,2,2,0,2,2,1,2,0,0,1],
  [1,0,2,0,0,0,1,2,0,1,1,1,0,1,0,1,0],
  [1,2,2,0,2,1,0,0,0,2,0,1,1,1,0,0,2,1,2]
]

def cert0926n : CertifiedBoard :=
  ⟨seed0926, by apply FastValid.valid; decide +kernel⟩

def cert0926r : CertifiedBoard :=
  ⟨seed0926.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0927 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,1,2,1,0,0,2,1,1,2,0],
  [1,0,1,2,0,0,0,0,1,1,1,1,0,1,0],
  [0,2,1,2,2,1,0,2,2,0,2,0,1,1,0,0,2],
  [2,0,0,1,0,2,2,0,1,1,0,0,2,1,2,0,2,0,2]
]

def cert0927n : CertifiedBoard :=
  ⟨seed0927, by apply FastValid.valid; decide +kernel⟩

def cert0927r : CertifiedBoard :=
  ⟨seed0927.map List.reverse, by apply FastValid.valid; decide +kernel⟩

end TBoards.Extended
