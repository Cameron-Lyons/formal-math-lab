import CertifiedFamily

/- Generated from extended_seeds.json. Published seeds 0–4:
   Qiyuan Ma, DOI 10.5281/zenodo.23631079, CC-BY-4.0. -/

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.Extended

def seed0000 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [0,1,2,1,2,2,2,0,2,2,0,0,1],
  [1,2,2,1,0,1,0,2,0,2,2,2,0,0,1],
  [2,2,2,1,1,1,2,1,2,1,0,1,2,2,1,1,2],
  [1,2,0,1,1,0,0,0,2,1,2,0,1,0,0,0,2,0,0]
]

def cert0000n : CertifiedBoard :=
  ⟨seed0000, by apply FastValid.valid; decide +kernel⟩

def cert0000r : CertifiedBoard :=
  ⟨seed0000.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0001 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,1,2,0,1,1,1,1,2,0,2],
  [1,0,1,2,0,2,1,2,2,0,0,0,1,0,1],
  [0,1,1,0,0,2,1,1,0,2,2,0,0,2,0,1,0],
  [2,0,2,1,0,2,2,1,2,1,0,0,0,1,1,0,0,2,0]
]

def cert0001n : CertifiedBoard :=
  ⟨seed0001, by apply FastValid.valid; decide +kernel⟩

def cert0001r : CertifiedBoard :=
  ⟨seed0001.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0002 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,1,2,0,1,1,1,1,2,0,2],
  [2,1,0,1,1,0,2,1,2,2,0,0,2,2,1],
  [0,0,1,0,0,2,0,1,2,1,1,0,1,0,0,0,0],
  [2,0,0,1,1,0,2,2,0,2,1,0,0,2,1,2,0,2,0]
]

def cert0002n : CertifiedBoard :=
  ⟨seed0002, by apply FastValid.valid; decide +kernel⟩

def cert0002r : CertifiedBoard :=
  ⟨seed0002.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0003 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,1,1,2,1,0,1],
  [2,0,1,1,2,1,2,2,0],
  [0,0,1,2,2,2,2,1,2,0,2],
  [2,1,2,1,1,2,2,1,1,1,1,1,0],
  [0,2,0,1,1,0,1,0,0,1,2,0,2,2,2],
  [2,2,0,2,1,0,0,2,1,1,0,2,2,1,0,2,1],
  [1,0,1,2,0,1,0,2,2,0,0,2,0,0,2,0,0,0,0]
]

def cert0003n : CertifiedBoard :=
  ⟨seed0003, by apply FastValid.valid; decide +kernel⟩

def cert0003r : CertifiedBoard :=
  ⟨seed0003.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0004 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,1,1,2,1,0,1],
  [2,0,1,1,2,1,2,2,0],
  [0,0,1,2,2,2,2,1,2,0,2],
  [2,1,2,1,1,2,2,1,1,1,1,1,0],
  [1,0,1,0,2,0,0,2,1,0,1,2,0,2,1],
  [0,2,1,1,0,2,2,2,1,0,2,0,1,2,0,2,2],
  [2,2,0,0,0,2,2,0,1,0,0,2,0,0,1,1,0,0,0]
]

def cert0004n : CertifiedBoard :=
  ⟨seed0004, by apply FastValid.valid; decide +kernel⟩

def cert0004r : CertifiedBoard :=
  ⟨seed0004.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0005 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [0,2,0,1,2,1,2,1,2,2,2,1,0],
  [2,2,1,1,2,0,0,1,1,0,0,2,2,0,2],
  [1,2,2,0,2,1,2,1,1,1,2,2,2,2,1,0,1],
  [1,0,1,2,0,0,0,0,1,0,0,2,0,1,0,2,2,0,0]
]

def cert0005n : CertifiedBoard :=
  ⟨seed0005, by apply FastValid.valid; decide +kernel⟩

def cert0005r : CertifiedBoard :=
  ⟨seed0005.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0006 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [0,2,0,2,1,2,1,1,2,2,2,0,0],
  [2,2,2,0,1,2,1,0,0,1,0,2,2,1,1],
  [1,2,2,2,1,0,1,1,1,2,2,1,2,1,2,0,2],
  [1,1,0,0,0,2,2,0,0,0,2,0,1,0,1,2,0,0,1]
]

def cert0006n : CertifiedBoard :=
  ⟨seed0006, by apply FastValid.valid; decide +kernel⟩

def cert0006r : CertifiedBoard :=
  ⟨seed0006.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0007 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [0,2,0,2,2,2,1,1,1,2,2,0,0],
  [1,2,2,2,2,1,0,1,2,0,0,2,2,0,1],
  [2,1,2,0,1,2,2,1,0,1,1,2,1,2,1,2,1],
  [2,2,0,2,0,0,1,0,2,1,1,0,0,0,0,1,0,0,2]
]

def cert0007n : CertifiedBoard :=
  ⟨seed0007, by apply FastValid.valid; decide +kernel⟩

def cert0007r : CertifiedBoard :=
  ⟨seed0007.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0008 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [0,2,0,2,2,2,1,1,1,2,2,0,0],
  [1,2,2,2,2,1,0,1,2,0,0,2,2,0,1],
  [2,1,2,0,1,2,2,1,0,1,1,2,1,2,1,2,1],
  [2,2,0,2,0,0,1,0,2,1,1,0,0,1,0,0,0,0,2]
]

def cert0008n : CertifiedBoard :=
  ⟨seed0008, by apply FastValid.valid; decide +kernel⟩

def cert0008r : CertifiedBoard :=
  ⟨seed0008.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0009 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [0,2,1,0,1,2,2,2,2,0,2,0,1],
  [1,2,1,2,0,1,0,1,0,2,0,2,2,1,2],
  [2,2,1,1,2,1,1,1,2,1,2,2,2,1,0,0,2],
  [1,2,0,0,2,2,0,0,0,1,1,0,0,1,2,2,0,0,0]
]

def cert0009n : CertifiedBoard :=
  ⟨seed0009, by apply FastValid.valid; decide +kernel⟩

def cert0009r : CertifiedBoard :=
  ⟨seed0009.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0010 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [0,2,1,1,2,1,0,1,2,0,2,0,1],
  [1,2,1,1,0,1,1,1,2,2,0,2,0,0,2],
  [2,2,2,2,1,2,2,0,0,1,2,1,2,2,2,1,2],
  [1,2,0,0,1,0,0,2,2,0,1,0,2,2,1,0,0,0,0]
]

def cert0010n : CertifiedBoard :=
  ⟨seed0010, by apply FastValid.valid; decide +kernel⟩

def cert0010r : CertifiedBoard :=
  ⟨seed0010.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0011 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [0,2,1,1,2,2,1,1,1,0,1,0,1],
  [2,2,0,1,2,1,0,2,0,2,2,2,1,0,0],
  [1,2,1,2,2,2,2,0,2,0,1,2,2,1,2,1,2],
  [1,2,0,0,1,0,0,1,1,2,0,0,2,2,0,0,0,0,2]
]

def cert0011n : CertifiedBoard :=
  ⟨seed0011, by apply FastValid.valid; decide +kernel⟩

def cert0011r : CertifiedBoard :=
  ⟨seed0011.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0012 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [0,2,2,1,2,0,1,1,1,0,1,0,2],
  [2,2,0,1,2,2,0,0,0,2,0,2,1,0,1],
  [1,2,1,2,2,2,1,1,2,1,2,2,2,2,1,1,2],
  [1,2,1,0,0,1,0,0,1,2,0,2,0,0,2,2,0,0,0]
]

def cert0012n : CertifiedBoard :=
  ⟨seed0012, by apply FastValid.valid; decide +kernel⟩

def cert0012r : CertifiedBoard :=
  ⟨seed0012.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0013 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [0,2,2,1,2,1,0,1,2,0,2,0,1],
  [2,1,2,1,0,0,2,1,1,2,0,2,0,0,2],
  [1,2,2,1,1,1,2,1,2,2,2,0,1,2,2,2,1],
  [2,2,0,0,0,1,0,1,1,0,2,2,2,0,0,1,0,0,0]
]

def cert0013n : CertifiedBoard :=
  ⟨seed0013, by apply FastValid.valid; decide +kernel⟩

def cert0013r : CertifiedBoard :=
  ⟨seed0013.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0014 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [0,2,2,1,2,2,2,0,0,1,0,0,2],
  [2,1,2,1,0,1,0,2,2,0,1,2,1,0,1],
  [1,2,2,2,2,1,1,2,2,1,1,2,1,2,0,2,1],
  [2,2,0,0,1,2,0,2,0,1,1,1,0,0,2,0,0,0,0]
]

def cert0014n : CertifiedBoard :=
  ⟨seed0014, by apply FastValid.valid; decide +kernel⟩

def cert0014r : CertifiedBoard :=
  ⟨seed0014.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0015 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [0,2,2,2,2,0,1,1,1,0,1,2,2],
  [1,2,1,0,1,2,0,2,1,2,0,0,0,0,1],
  [2,2,1,2,1,2,2,2,1,1,2,1,1,2,2,0,2],
  [2,2,0,1,0,2,0,0,2,0,0,1,0,0,2,2,1,0,0]
]

def cert0015n : CertifiedBoard :=
  ⟨seed0015, by apply FastValid.valid; decide +kernel⟩

def cert0015r : CertifiedBoard :=
  ⟨seed0015.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0016 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [0,2,2,2,2,0,1,1,1,0,1,2,2],
  [1,2,1,0,1,2,0,2,1,2,0,0,0,0,2],
  [2,2,1,2,1,2,2,2,1,1,2,1,1,2,2,0,1],
  [2,2,0,0,2,0,0,1,0,0,1,0,2,0,2,2,1,0,0]
]

def cert0016n : CertifiedBoard :=
  ⟨seed0016, by apply FastValid.valid; decide +kernel⟩

def cert0016r : CertifiedBoard :=
  ⟨seed0016.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0017 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [0,2,2,2,2,0,2,0,2,1,2,2,1],
  [2,1,0,1,0,2,2,1,2,1,1,0,0,0,2],
  [2,2,2,1,1,1,2,1,0,1,1,2,1,2,2,0,1],
  [1,2,0,0,2,0,0,1,2,0,1,0,0,1,2,2,0,0,0]
]

def cert0017n : CertifiedBoard :=
  ⟨seed0017, by apply FastValid.valid; decide +kernel⟩

def cert0017r : CertifiedBoard :=
  ⟨seed0017.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0018 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [0,2,2,2,2,1,0,1,2,1,2,0,0],
  [1,2,2,1,0,0,2,1,2,2,0,2,2,0,1],
  [2,2,0,1,1,1,2,1,1,2,2,2,1,2,1,1,0],
  [1,0,2,0,0,1,0,1,0,0,0,1,2,0,0,0,2,0,2]
]

def cert0018n : CertifiedBoard :=
  ⟨seed0018, by apply FastValid.valid; decide +kernel⟩

def cert0018r : CertifiedBoard :=
  ⟨seed0018.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0019 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [1,2,0,0,2,0,2,0,2,1,2,2,2],
  [2,2,2,1,1,2,0,1,2,1,1,0,0,0,1],
  [2,2,0,1,1,1,2,2,2,1,0,1,2,2,1,2,1],
  [2,1,2,1,0,0,1,0,1,0,2,2,0,0,2,2,0,0,0]
]

def cert0019n : CertifiedBoard :=
  ⟨seed0019, by apply FastValid.valid; decide +kernel⟩

def cert0019r : CertifiedBoard :=
  ⟨seed0019.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0020 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [1,2,0,0,2,2,0,0,0,1,0,0,1],
  [1,2,2,1,2,1,2,2,2,1,1,1,2,2,1],
  [2,2,2,2,0,2,2,0,1,0,1,2,1,2,1,1,2],
  [2,1,0,0,2,0,1,2,0,2,1,0,1,1,0,2,0,0,0]
]

def cert0020n : CertifiedBoard :=
  ⟨seed0020, by apply FastValid.valid; decide +kernel⟩

def cert0020r : CertifiedBoard :=
  ⟨seed0020.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0021 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [1,2,0,0,2,2,2,2,0,2,0,0,1],
  [1,1,2,2,0,1,0,0,2,2,1,2,1,1,1],
  [2,2,1,2,1,1,2,1,2,2,0,1,0,1,2,2,2],
  [2,2,1,0,0,0,0,1,1,0,2,0,2,1,0,1,2,0,0]
]

def cert0021n : CertifiedBoard :=
  ⟨seed0021, by apply FastValid.valid; decide +kernel⟩

def cert0021r : CertifiedBoard :=
  ⟨seed0021.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0022 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [1,2,0,1,2,1,0,1,0,0,2,2,1],
  [1,1,2,0,2,1,1,1,2,2,0,0,2,0,0],
  [2,2,1,2,1,2,2,2,0,2,2,2,2,1,2,1,1],
  [2,1,0,2,0,0,0,0,1,2,2,0,1,0,0,1,1,0,1]
]

def cert0022n : CertifiedBoard :=
  ⟨seed0022, by apply FastValid.valid; decide +kernel⟩

def cert0022r : CertifiedBoard :=
  ⟨seed0022.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0023 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [1,2,0,1,2,2,1,1,1,0,1,0,2],
  [1,1,2,0,0,2,2,2,0,2,0,2,1,0,0],
  [2,2,2,1,2,2,0,1,2,2,2,1,2,1,2,1,1],
  [0,2,0,0,0,0,1,1,2,1,0,1,0,0,2,2,0,0,1]
]

def cert0023n : CertifiedBoard :=
  ⟨seed0023, by apply FastValid.valid; decide +kernel⟩

def cert0023r : CertifiedBoard :=
  ⟨seed0023.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0024 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [1,2,0,1,2,2,2,0,2,2,2,0,1],
  [2,1,2,1,0,1,0,1,2,1,0,2,0,2,0],
  [2,0,0,2,2,1,1,1,2,1,1,2,2,1,2,2,1],
  [2,2,2,0,0,1,1,0,0,0,0,1,0,0,2,1,2,0,0]
]

def cert0024n : CertifiedBoard :=
  ⟨seed0024, by apply FastValid.valid; decide +kernel⟩

def cert0024r : CertifiedBoard :=
  ⟨seed0024.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0025 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [1,2,0,1,2,2,2,2,0,2,1,2,0],
  [2,2,1,1,2,1,0,2,2,0,0,0,1,2,2],
  [2,0,1,1,1,2,2,2,1,2,1,2,1,0,1,0,1],
  [2,2,1,1,0,0,2,0,0,1,0,0,0,2,0,2,2,0,0]
]

def cert0025n : CertifiedBoard :=
  ⟨seed0025, by apply FastValid.valid; decide +kernel⟩

def cert0025r : CertifiedBoard :=
  ⟨seed0025.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0026 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [1,2,0,2,1,2,1,1,0,0,1,2,2],
  [2,2,2,2,1,0,1,1,2,2,0,1,0,0,1],
  [2,2,0,1,0,2,2,2,0,2,2,1,1,1,2,2,1],
  [2,1,2,1,2,1,0,1,2,0,0,0,2,0,0,2,0,0,0]
]

def cert0026n : CertifiedBoard :=
  ⟨seed0026, by apply FastValid.valid; decide +kernel⟩

def cert0026r : CertifiedBoard :=
  ⟨seed0026.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0027 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [1,2,0,2,1,2,1,1,0,0,1,2,2],
  [2,2,2,2,1,0,1,1,2,2,0,1,0,0,1],
  [2,2,0,1,0,2,2,2,0,2,2,1,1,1,2,2,1],
  [2,1,2,1,2,1,0,1,2,0,0,2,0,0,2,0,0,0,0]
]

def cert0027n : CertifiedBoard :=
  ⟨seed0027, by apply FastValid.valid; decide +kernel⟩

def cert0027r : CertifiedBoard :=
  ⟨seed0027.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0028 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [1,2,0,2,1,2,1,1,1,0,1,2,2],
  [2,2,2,2,2,0,0,0,2,2,0,1,0,0,1],
  [1,2,1,0,2,2,1,2,2,0,1,1,2,2,1,1,2],
  [2,2,1,2,1,0,1,0,0,2,0,0,0,1,2,0,2,0,0]
]

def cert0028n : CertifiedBoard :=
  ⟨seed0028, by apply FastValid.valid; decide +kernel⟩

def cert0028r : CertifiedBoard :=
  ⟨seed0028.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0029 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [1,2,0,2,2,0,0,0,1,2,1,2,1],
  [1,2,2,1,0,1,1,2,1,1,0,0,2,0,0],
  [2,2,1,2,2,2,0,2,1,1,1,2,2,2,2,1,2],
  [2,1,0,2,0,1,2,0,1,0,1,0,0,2,2,0,0,0,1]
]

def cert0029n : CertifiedBoard :=
  ⟨seed0029, by apply FastValid.valid; decide +kernel⟩

def cert0029r : CertifiedBoard :=
  ⟨seed0029.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0030 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [1,2,0,2,2,1,2,1,2,2,0,0,0],
  [2,2,2,0,0,1,1,0,0,2,2,2,2,0,1],
  [2,1,0,1,2,1,1,1,2,2,1,2,2,1,1,2,1],
  [0,0,2,1,0,1,0,0,1,2,0,1,0,2,0,2,0,0,0]
]

def cert0030n : CertifiedBoard :=
  ⟨seed0030, by apply FastValid.valid; decide +kernel⟩

def cert0030r : CertifiedBoard :=
  ⟨seed0030.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0031 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [1,2,0,2,2,1,2,1,2,2,0,0,0],
  [2,2,2,0,0,1,1,0,0,2,2,2,2,0,1],
  [2,1,0,1,2,1,1,1,2,2,1,2,2,1,1,2,1],
  [1,0,2,1,0,1,0,0,1,2,0,0,0,2,0,2,0,1,0]
]

def cert0031n : CertifiedBoard :=
  ⟨seed0031, by apply FastValid.valid; decide +kernel⟩

def cert0031r : CertifiedBoard :=
  ⟨seed0031.map List.reverse, by apply FastValid.valid; decide +kernel⟩

end TBoards.Extended
