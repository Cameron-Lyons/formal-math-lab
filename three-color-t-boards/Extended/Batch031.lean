import Extended.Batch027

/- Generated from extended_seeds.json. Published seeds 0–4:
   Qiyuan Ma, DOI 10.5281/zenodo.23631079, CC-BY-4.0. -/

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.Extended

def seed0992 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,1,1,0,0,0,1,1,1,2,0,2],
  [1,0,0,2,1,0,2,0,2,0,1,0,0,2,2],
  [1,2,2,0,0,0,2,2,1,0,1,1,1,0,1,1,0],
  [2,2,0,1,2,0,1,0,2,0,0,1,2,0,2,1,2,1,2]
]

def cert0992n : CertifiedBoard :=
  ⟨seed0992, by apply FastValid.valid; decide +kernel⟩

def cert0992r : CertifiedBoard :=
  ⟨seed0992.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0993 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,1,1,0,0,0,1,1,1,2,0,2],
  [1,0,0,2,1,0,2,0,2,0,1,0,0,2,2],
  [1,2,2,0,0,0,2,2,1,0,1,1,1,0,1,1,0],
  [2,2,0,1,2,0,1,0,2,0,2,1,2,0,0,1,2,1,2]
]

def cert0993n : CertifiedBoard :=
  ⟨seed0993, by apply FastValid.valid; decide +kernel⟩

def cert0993r : CertifiedBoard :=
  ⟨seed0993.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0994 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,1,1,0,0,0,1,2,0,1,1,0],
  [1,0,2,0,0,2,0,1,1,1,2,0,2,0,2],
  [0,2,1,0,0,2,2,1,2,0,1,1,1,0,1,0,2],
  [0,0,1,2,2,0,0,2,2,0,2,1,2,1,0,1,0,0,0]
]

def cert0994n : CertifiedBoard :=
  ⟨seed0994, by apply FastValid.valid; decide +kernel⟩

def cert0994r : CertifiedBoard :=
  ⟨seed0994.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0995 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,1,1,0,0,0,2,0,1,2,0,2],
  [0,1,0,1,1,1,0,0,2,2,0,0,1,1,1],
  [2,0,0,2,0,1,2,1,0,1,1,0,2,1,2,2,0],
  [1,1,2,0,2,0,1,0,2,1,2,0,2,2,1,0,0,0,1]
]

def cert0995n : CertifiedBoard :=
  ⟨seed0995, by apply FastValid.valid; decide +kernel⟩

def cert0995r : CertifiedBoard :=
  ⟨seed0995.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0996 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,1,1,0,0,2,0,0,0,2,2,1],
  [0,1,0,2,1,0,0,1,1,0,1,1,0,1,1],
  [2,1,2,1,0,0,0,2,1,2,2,0,1,0,2,0,2],
  [1,1,1,1,2,0,2,0,0,1,2,0,2,2,0,1,2,0,1]
]

def cert0996n : CertifiedBoard :=
  ⟨seed0996, by apply FastValid.valid; decide +kernel⟩

def cert0996r : CertifiedBoard :=
  ⟨seed0996.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0997 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,1,1,0,0,2,0,0,1,1,1,2],
  [0,1,0,1,1,1,0,2,2,0,1,2,2,0,2],
  [1,0,0,0,2,0,2,1,0,0,2,1,2,0,1,1,0],
  [1,2,1,2,0,0,0,1,2,0,2,2,1,0,2,0,1,0,1]
]

def cert0997n : CertifiedBoard :=
  ⟨seed0997, by apply FastValid.valid; decide +kernel⟩

def cert0997r : CertifiedBoard :=
  ⟨seed0997.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0998 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,1,1,1,0,0,0,0,1,1,0,2],
  [0,1,1,2,1,2,0,1,0,2,0,1,0,1,2],
  [0,0,1,2,2,1,0,0,2,1,2,0,0,2,2,0,1],
  [1,2,0,2,0,2,0,2,1,0,1,1,1,0,0,2,2,0,0]
]

def cert0998n : CertifiedBoard :=
  ⟨seed0998, by apply FastValid.valid; decide +kernel⟩

def cert0998r : CertifiedBoard :=
  ⟨seed0998.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0999 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,1,1,1,0,0,0,0,1,1,1,0],
  [1,0,1,2,2,0,1,1,0,0,2,1,2,1,2],
  [1,2,0,1,0,2,0,0,2,0,2,0,1,2,0,0,2],
  [0,1,1,2,0,2,2,1,0,2,2,0,2,1,0,0,1,0,1]
]

def cert0999n : CertifiedBoard :=
  ⟨seed0999, by apply FastValid.valid; decide +kernel⟩

def cert0999r : CertifiedBoard :=
  ⟨seed0999.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1000 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,1,1,1,0,0,0,0,1,2,0,2],
  [1,1,0,0,2,0,2,0,0,2,1,0,1,1,1],
  [2,0,1,0,1,0,2,2,1,0,0,2,1,2,1,2,0],
  [0,2,0,1,2,0,0,1,1,2,2,0,2,2,0,1,1,0,2]
]

def cert1000n : CertifiedBoard :=
  ⟨seed1000, by apply FastValid.valid; decide +kernel⟩

def cert1000r : CertifiedBoard :=
  ⟨seed1000.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1001 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,1,1,1,0,0,0,0,2,0,1,1],
  [0,2,2,1,2,1,0,0,2,0,2,2,0,0,2],
  [1,1,0,0,1,2,0,2,1,0,1,1,1,0,1,0,2],
  [1,2,2,0,0,1,1,2,0,2,1,2,0,1,0,2,0,1,2]
]

def cert1001n : CertifiedBoard :=
  ⟨seed1001, by apply FastValid.valid; decide +kernel⟩

def cert1001r : CertifiedBoard :=
  ⟨seed1001.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1002 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,1,1,1,0,0,0,0,2,0,1,1],
  [1,0,1,2,1,2,0,0,2,1,2,0,2,1,0],
  [2,0,2,0,0,1,0,0,1,1,2,2,1,0,1,2,0],
  [1,1,1,0,2,2,0,1,0,0,2,0,2,2,0,1,1,0,2]
]

def cert1002n : CertifiedBoard :=
  ⟨seed1002, by apply FastValid.valid; decide +kernel⟩

def cert1002r : CertifiedBoard :=
  ⟨seed1002.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1003 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,1,1,1,0,0,0,2,0,1,1,0],
  [0,0,2,2,0,1,2,0,2,2,1,2,1,0,2],
  [0,1,0,1,2,0,1,1,1,0,0,2,0,2,1,0,1],
  [1,0,0,0,1,0,2,1,2,0,2,0,0,1,1,2,2,0,0]
]

def cert1003n : CertifiedBoard :=
  ⟨seed1003, by apply FastValid.valid; decide +kernel⟩

def cert1003r : CertifiedBoard :=
  ⟨seed1003.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1004 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,1,1,1,0,0,0,2,0,1,2,0],
  [2,0,0,2,1,2,2,0,1,0,2,2,0,2,0],
  [1,1,1,0,0,1,1,0,0,1,0,2,2,1,0,1,1],
  [2,0,1,2,1,2,0,0,0,2,1,0,1,1,2,0,2,0,2]
]

def cert1004n : CertifiedBoard :=
  ⟨seed1004, by apply FastValid.valid; decide +kernel⟩

def cert1004r : CertifiedBoard :=
  ⟨seed1004.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1005 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,1,1,1,0,0,1,0,0,2,0,2],
  [1,1,0,1,2,2,0,2,1,0,2,0,1,0,2],
  [2,0,0,0,1,1,1,0,0,0,2,2,1,2,0,1,1],
  [0,2,2,0,0,2,1,2,1,0,1,1,2,0,1,2,0,2,0]
]

def cert1005n : CertifiedBoard :=
  ⟨seed1005, by apply FastValid.valid; decide +kernel⟩

def cert1005r : CertifiedBoard :=
  ⟨seed1005.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1006 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,1,1,1,0,0,1,0,1,1,0,0],
  [0,1,1,2,2,0,1,0,2,1,2,1,2,0,1],
  [1,0,0,2,0,2,2,0,2,0,1,2,0,0,2,1,0],
  [0,0,0,2,2,1,0,2,0,0,0,1,1,1,0,1,2,0,2]
]

def cert1006n : CertifiedBoard :=
  ⟨seed1006, by apply FastValid.valid; decide +kernel⟩

def cert1006r : CertifiedBoard :=
  ⟨seed1006.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1007 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,1,1,1,0,0,1,0,1,1,1,0],
  [1,0,1,2,0,1,1,0,0,0,1,2,2,0,0],
  [0,0,2,1,2,0,2,1,0,2,2,0,2,2,1,2,0],
  [2,0,1,0,2,0,1,1,2,1,0,0,2,0,2,0,0,0,2]
]

def cert1007n : CertifiedBoard :=
  ⟨seed1007, by apply FastValid.valid; decide +kernel⟩

def cert1007r : CertifiedBoard :=
  ⟨seed1007.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1008 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,1,1,1,0,0,1,0,1,1,1,0],
  [1,0,1,2,0,2,1,0,0,0,1,2,2,0,0],
  [2,1,2,0,0,2,0,1,1,0,2,1,0,2,2,0,2],
  [0,0,0,2,0,1,0,0,2,0,1,1,2,1,2,0,2,2,1]
]

def cert1008n : CertifiedBoard :=
  ⟨seed1008, by apply FastValid.valid; decide +kernel⟩

def cert1008r : CertifiedBoard :=
  ⟨seed1008.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1009 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,1,1,1,0,0,1,0,1,2,0,2],
  [2,1,0,0,2,0,0,2,2,0,0,0,0,1,1],
  [2,2,1,0,1,1,1,0,0,2,0,1,0,2,1,2,1],
  [1,1,0,2,1,2,0,1,2,0,2,2,0,2,0,1,1,2,2]
]

def cert1009n : CertifiedBoard :=
  ⟨seed1009, by apply FastValid.valid; decide +kernel⟩

def cert1009r : CertifiedBoard :=
  ⟨seed1009.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1010 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,1,1,1,0,0,1,1,0,0,0,2],
  [0,1,0,2,1,2,1,0,1,2,0,2,1,2,0],
  [2,0,0,0,1,2,2,1,0,0,2,2,0,1,0,1,1],
  [1,1,1,0,2,2,0,2,0,2,0,1,1,2,0,0,2,0,1]
]

def cert1010n : CertifiedBoard :=
  ⟨seed1010, by apply FastValid.valid; decide +kernel⟩

def cert1010r : CertifiedBoard :=
  ⟨seed1010.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1011 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,1,1,1,0,0,1,1,0,1,1,1],
  [0,0,1,2,2,0,2,1,2,1,0,2,1,2,0],
  [1,1,0,0,0,2,2,0,1,0,2,0,2,0,0,0,2],
  [2,0,1,2,0,1,1,2,0,0,2,0,2,2,1,0,1,0,0]
]

def cert1011n : CertifiedBoard :=
  ⟨seed1011, by apply FastValid.valid; decide +kernel⟩

def cert1011r : CertifiedBoard :=
  ⟨seed1011.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1012 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,1,1,1,0,0,1,1,0,1,1,1],
  [2,0,2,2,0,1,0,0,2,1,2,0,0,0,2],
  [2,2,1,0,0,2,1,0,1,0,2,0,1,1,0,2,0],
  [1,1,2,0,2,0,1,2,1,2,0,0,0,1,2,2,0,2,2]
]

def cert1012n : CertifiedBoard :=
  ⟨seed1012, by apply FastValid.valid; decide +kernel⟩

def cert1012r : CertifiedBoard :=
  ⟨seed1012.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1013 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,1,1,1,0,0,1,1,1,0,0,0],
  [0,0,2,0,2,0,1,0,2,1,2,0,2,2,0],
  [2,0,0,1,1,0,2,1,0,1,2,2,1,2,0,1,1],
  [1,1,2,0,1,2,1,0,1,0,0,0,2,2,0,2,0,0,2]
]

def cert1013n : CertifiedBoard :=
  ⟨seed1013, by apply FastValid.valid; decide +kernel⟩

def cert1013r : CertifiedBoard :=
  ⟨seed1013.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1014 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,1,1,1,0,0,1,1,1,0,0,2],
  [1,1,0,1,2,2,0,2,0,2,0,1,0,0,0],
  [0,0,0,2,1,0,2,2,0,2,2,1,2,1,0,1,1],
  [1,2,0,0,2,0,0,1,2,0,1,1,2,0,1,0,2,1,2]
]

def cert1014n : CertifiedBoard :=
  ⟨seed1014, by apply FastValid.valid; decide +kernel⟩

def cert1014r : CertifiedBoard :=
  ⟨seed1014.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1015 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,1,1,1,0,0,1,1,1,0,1,1],
  [1,1,0,2,0,0,2,2,0,2,1,0,1,2,2],
  [2,0,1,0,0,0,1,1,2,0,2,2,0,0,0,2,0],
  [2,2,1,2,1,0,2,1,2,0,2,0,1,2,0,1,0,0,2]
]

def cert1015n : CertifiedBoard :=
  ⟨seed1015, by apply FastValid.valid; decide +kernel⟩

def cert1015r : CertifiedBoard :=
  ⟨seed1015.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1016 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,1,1,1,0,0,1,1,1,2,0,1],
  [2,2,0,2,0,0,0,2,1,2,0,2,0,0,2],
  [0,1,1,0,0,0,1,0,1,2,2,1,0,1,1,0,2],
  [0,2,0,1,2,0,2,2,0,1,0,0,2,1,2,1,0,2,2]
]

def cert1016n : CertifiedBoard :=
  ⟨seed1016, by apply FastValid.valid; decide +kernel⟩

def cert1016r : CertifiedBoard :=
  ⟨seed1016.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1017 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,1,1,1,0,0,1,1,1,2,0,2],
  [2,0,1,2,2,0,0,2,0,1,2,0,1,1,0],
  [1,0,0,1,0,1,1,0,2,2,0,2,0,0,0,2,1],
  [2,1,2,0,2,1,2,1,0,0,0,2,2,1,0,1,0,2,0]
]

def cert1017n : CertifiedBoard :=
  ⟨seed1017, by apply FastValid.valid; decide +kernel⟩

def cert1017r : CertifiedBoard :=
  ⟨seed1017.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1018 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,1,1,1,0,0,1,1,2,0,1,1],
  [1,0,1,2,1,2,0,0,2,0,0,2,0,1,0],
  [2,0,2,1,0,0,0,0,1,1,0,2,2,1,2,2,0],
  [1,1,1,0,1,2,0,1,0,0,2,1,0,2,2,0,2,0,2]
]

def cert1018n : CertifiedBoard :=
  ⟨seed1018, by apply FastValid.valid; decide +kernel⟩

def cert1018r : CertifiedBoard :=
  ⟨seed1018.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1019 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,1,1,1,0,0,1,2,0,1,1,1],
  [2,2,0,2,0,1,1,0,0,0,2,1,2,0,2],
  [1,1,0,1,0,0,2,1,0,2,0,2,0,0,0,1,2],
  [1,2,2,0,1,0,1,1,2,1,0,2,2,1,2,0,0,2,2]
]

def cert1019n : CertifiedBoard :=
  ⟨seed1019, by apply FastValid.valid; decide +kernel⟩

def cert1019r : CertifiedBoard :=
  ⟨seed1019.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1020 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,1,1,1,0,0,1,2,0,1,1,2],
  [1,0,1,2,1,2,2,0,0,0,0,2,0,2,0],
  [1,2,0,1,0,1,1,0,0,1,0,2,0,2,2,1,0],
  [2,0,0,2,1,0,0,2,1,2,0,1,1,1,0,2,2,0,2]
]

def cert1020n : CertifiedBoard :=
  ⟨seed1020, by apply FastValid.valid; decide +kernel⟩

def cert1020r : CertifiedBoard :=
  ⟨seed1020.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1021 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,1,1,1,0,0,1,2,0,2,0,1],
  [0,1,0,2,0,1,1,0,1,0,0,1,2,0,2],
  [2,1,2,0,0,2,0,0,2,2,0,2,1,0,1,1,1],
  [1,1,2,2,1,0,2,2,0,1,1,0,0,0,0,2,1,2,1]
]

def cert1021n : CertifiedBoard :=
  ⟨seed1021, by apply FastValid.valid; decide +kernel⟩

def cert1021r : CertifiedBoard :=
  ⟨seed1021.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1022 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,1,1,1,0,0,2,0,1,1,1,0],
  [0,1,0,1,2,2,0,2,2,1,2,1,2,0,1],
  [1,0,0,2,1,0,0,0,1,2,0,0,1,0,2,0,2],
  [0,2,1,0,2,0,1,1,0,1,1,2,0,0,0,2,2,0,2]
]

def cert1022n : CertifiedBoard :=
  ⟨seed1022, by apply FastValid.valid; decide +kernel⟩

def cert1022r : CertifiedBoard :=
  ⟨seed1022.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1023 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,0,0,0,0,2,0,1,2,0],
  [0,2,1,1,2,1,0,0,1,1,0,1,1,1,0],
  [2,0,1,1,1,0,1,2,0,2,0,2,2,0,1,0,2],
  [1,0,0,2,1,2,2,0,0,1,0,2,0,2,1,2,0,0,2]
]

def cert1023n : CertifiedBoard :=
  ⟨seed1023, by apply FastValid.valid; decide +kernel⟩

def cert1023r : CertifiedBoard :=
  ⟨seed1023.map List.reverse, by apply FastValid.valid; decide +kernel⟩

end TBoards.Extended
