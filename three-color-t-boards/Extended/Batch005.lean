import Extended.Batch001

/- Generated from extended_seeds.json. Published seeds 0–4:
   Qiyuan Ma, DOI 10.5281/zenodo.23631079, CC-BY-4.0. -/

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.Extended

def seed0160 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,1,1,1,0,2,1,1,1,0,0],
  [1,1,0,1,0,0,0,2,2,1,2,0,0,1,1],
  [1,2,1,0,2,0,0,2,0,2,0,2,2,0,1,2,2],
  [2,2,0,1,0,0,2,1,2,0,2,1,0,1,2,0,1,1,2]
]

def cert0160n : CertifiedBoard :=
  ⟨seed0160, by apply FastValid.valid; decide +kernel⟩

def cert0160r : CertifiedBoard :=
  ⟨seed0160.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0161 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,1,1,1,0,2,1,1,1,0,0],
  [2,0,2,1,0,0,0,2,2,1,2,1,0,1,1],
  [1,1,2,0,1,0,0,2,0,2,0,0,2,0,1,2,2],
  [2,2,0,2,1,2,0,0,1,1,0,1,0,2,2,0,1,2,0]
]

def cert0161n : CertifiedBoard :=
  ⟨seed0161, by apply FastValid.valid; decide +kernel⟩

def cert0161r : CertifiedBoard :=
  ⟨seed0161.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0162 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,1,1,1,0,2,1,1,1,0,0],
  [2,1,0,0,1,2,1,0,2,2,0,0,0,2,2],
  [2,2,1,2,0,0,2,0,1,0,1,1,0,1,1,2,0],
  [2,0,1,2,0,2,0,2,1,2,2,0,2,0,1,0,0,2,1]
]

def cert0162n : CertifiedBoard :=
  ⟨seed0162, by apply FastValid.valid; decide +kernel⟩

def cert0162r : CertifiedBoard :=
  ⟨seed0162.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0163 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,1,1,1,0,2,1,1,1,2,0],
  [1,0,2,1,2,1,2,0,2,0,1,2,2,1,0],
  [2,0,0,2,2,0,1,0,0,1,1,0,0,2,1,0,0],
  [1,1,0,1,0,1,2,0,2,0,0,0,2,2,0,2,0,1,1]
]

def cert0163n : CertifiedBoard :=
  ⟨seed0163, by apply FastValid.valid; decide +kernel⟩

def cert0163r : CertifiedBoard :=
  ⟨seed0163.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0164 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,1,1,1,0,2,1,1,1,2,0],
  [2,1,0,0,1,2,1,0,2,2,0,0,0,2,2],
  [2,2,1,2,0,0,2,0,1,0,1,1,0,1,1,0,0],
  [2,0,1,2,0,2,0,2,1,2,2,0,2,0,1,0,0,2,1]
]

def cert0164n : CertifiedBoard :=
  ⟨seed0164, by apply FastValid.valid; decide +kernel⟩

def cert0164r : CertifiedBoard :=
  ⟨seed0164.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0165 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,1,1,1,0,2,1,1,1,2,0],
  [2,1,2,0,2,0,0,2,2,1,2,0,2,0,0],
  [2,0,1,0,0,1,1,0,0,2,1,0,1,1,0,2,1],
  [2,0,2,0,1,0,1,2,2,0,1,2,1,0,0,0,2,2,0]
]

def cert0165n : CertifiedBoard :=
  ⟨seed0165, by apply FastValid.valid; decide +kernel⟩

def cert0165r : CertifiedBoard :=
  ⟨seed0165.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0166 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,1,1,1,0,2,1,1,2,0,2],
  [2,1,2,0,1,2,2,0,2,0,0,0,2,2,1],
  [0,2,1,0,0,2,0,1,1,0,1,0,1,1,1,0,0],
  [0,0,1,2,1,0,2,2,0,1,0,0,2,1,2,0,2,0,0]
]

def cert0166n : CertifiedBoard :=
  ⟨seed0166, by apply FastValid.valid; decide +kernel⟩

def cert0166r : CertifiedBoard :=
  ⟨seed0166.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0167 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,1,2,0,1,1,1,1,0,2,2],
  [2,2,0,0,1,0,1,1,0,0,0,2,1,1,2],
  [0,0,2,1,0,2,1,2,2,0,1,0,1,2,1,0,0],
  [1,2,0,2,0,2,2,1,2,0,2,0,0,2,0,1,1,0,0]
]

def cert0167n : CertifiedBoard :=
  ⟨seed0167, by apply FastValid.valid; decide +kernel⟩

def cert0167r : CertifiedBoard :=
  ⟨seed0167.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0168 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,1,2,0,1,1,1,2,0,2,0],
  [1,1,0,2,0,2,1,2,1,2,2,1,0,1,1],
  [2,0,0,0,2,2,0,1,1,1,0,0,2,0,1,0,0],
  [0,1,2,0,2,1,1,0,0,2,1,0,1,0,2,2,0,0,1]
]

def cert0168n : CertifiedBoard :=
  ⟨seed0168, by apply FastValid.valid; decide +kernel⟩

def cert0168r : CertifiedBoard :=
  ⟨seed0168.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0169 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,1,2,0,1,2,1,1,0,1,1],
  [1,1,0,1,0,0,2,0,2,0,0,0,1,1,1],
  [1,2,2,0,2,0,0,2,2,0,2,1,0,0,2,1,2],
  [1,1,0,2,1,2,0,1,1,1,2,0,1,0,2,2,1,0,0]
]

def cert0169n : CertifiedBoard :=
  ⟨seed0169, by apply FastValid.valid; decide +kernel⟩

def cert0169r : CertifiedBoard :=
  ⟨seed0169.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0170 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,1,2,0,1,2,1,1,1,0,2],
  [2,0,2,0,1,1,2,0,0,2,0,2,1,2,0],
  [0,2,2,0,1,1,1,0,1,0,1,1,0,0,2,1,0],
  [1,0,2,0,2,1,2,2,0,0,0,1,0,0,2,2,1,0,0]
]

def cert0170n : CertifiedBoard :=
  ⟨seed0170, by apply FastValid.valid; decide +kernel⟩

def cert0170r : CertifiedBoard :=
  ⟨seed0170.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0171 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,1,2,0,1,2,2,1,1,0,2],
  [0,2,1,0,1,0,1,1,1,1,2,1,2,0,2],
  [0,0,1,1,0,2,0,2,1,0,0,2,2,0,1,0,0],
  [0,2,2,0,0,0,2,1,2,0,2,0,0,2,0,1,1,0,0]
]

def cert0171n : CertifiedBoard :=
  ⟨seed0171, by apply FastValid.valid; decide +kernel⟩

def cert0171r : CertifiedBoard :=
  ⟨seed0171.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0172 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,1,2,0,1,2,2,1,1,2,0],
  [2,1,0,1,1,1,0,0,2,0,1,0,0,2,1],
  [0,1,1,0,2,1,2,1,2,0,2,2,0,1,0,0,0],
  [2,0,2,0,0,2,1,0,1,1,1,0,2,2,0,2,0,0,1]
]

def cert0172n : CertifiedBoard :=
  ⟨seed0172, by apply FastValid.valid; decide +kernel⟩

def cert0172r : CertifiedBoard :=
  ⟨seed0172.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0173 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,1,2,0,2,0,0,2,1,1,2],
  [2,1,0,1,1,1,1,0,2,0,1,2,1,0,1],
  [1,2,0,1,0,0,2,1,2,0,2,2,0,1,0,0,0],
  [0,1,1,0,2,0,0,1,1,0,0,2,2,1,2,2,0,2,1]
]

def cert0173n : CertifiedBoard :=
  ⟨seed0173, by apply FastValid.valid; decide +kernel⟩

def cert0173r : CertifiedBoard :=
  ⟨seed0173.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0174 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,1,2,0,2,0,1,1,1,0,0],
  [2,0,0,1,1,0,1,0,2,1,2,1,0,2,2],
  [2,2,1,0,1,1,1,0,0,2,2,0,1,0,0,2,1],
  [2,1,1,2,2,0,0,0,2,0,1,2,0,2,1,2,0,2,0]
]

def cert0174n : CertifiedBoard :=
  ⟨seed0174, by apply FastValid.valid; decide +kernel⟩

def cert0174r : CertifiedBoard :=
  ⟨seed0174.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0175 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,1,2,0,2,1,0,0,2,2,1],
  [2,1,0,1,1,1,2,0,2,0,0,1,1,0,0],
  [1,2,0,0,2,1,2,1,1,0,1,0,0,0,2,1,2],
  [1,1,0,2,0,2,0,1,2,2,0,1,0,2,2,0,1,1,1]
]

def cert0175n : CertifiedBoard :=
  ⟨seed0175, by apply FastValid.valid; decide +kernel⟩

def cert0175r : CertifiedBoard :=
  ⟨seed0175.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0176 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,1,2,0,2,2,0,1,1,0,0],
  [1,0,2,0,1,1,2,0,2,1,0,0,0,1,1],
  [1,1,1,0,2,1,2,2,1,2,0,0,2,2,0,1,0],
  [0,0,2,1,0,1,2,1,1,1,0,1,0,0,2,0,2,0,0]
]

def cert0176n : CertifiedBoard :=
  ⟨seed0176, by apply FastValid.valid; decide +kernel⟩

def cert0176r : CertifiedBoard :=
  ⟨seed0176.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0177 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,1,2,0,2,2,0,1,1,1,2],
  [1,2,0,1,1,0,2,1,1,0,0,0,2,0,2],
  [2,1,0,0,1,1,1,0,1,0,0,2,0,0,2,2,1],
  [0,2,0,1,0,2,1,2,1,2,2,0,2,1,0,1,2,0,0]
]

def cert0177n : CertifiedBoard :=
  ⟨seed0177, by apply FastValid.valid; decide +kernel⟩

def cert0177r : CertifiedBoard :=
  ⟨seed0177.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0178 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,1,2,0,2,2,0,2,0,1,2],
  [2,0,1,0,1,0,0,1,1,1,0,1,1,1,0],
  [1,2,0,2,0,0,2,1,2,1,2,2,0,1,1,0,0],
  [1,0,0,2,2,1,0,2,1,0,2,1,1,2,0,0,0,2,0]
]

def cert0178n : CertifiedBoard :=
  ⟨seed0178, by apply FastValid.valid; decide +kernel⟩

def cert0178r : CertifiedBoard :=
  ⟨seed0178.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0179 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,1,2,1,0,0,0,2,0,2,2],
  [2,2,0,0,1,0,1,1,0,2,0,1,0,2,1],
  [1,1,1,0,0,2,1,0,0,2,2,1,2,0,1,1,1],
  [2,1,2,2,0,2,1,1,0,1,1,2,0,1,2,0,2,0,0]
]

def cert0179n : CertifiedBoard :=
  ⟨seed0179, by apply FastValid.valid; decide +kernel⟩

def cert0179r : CertifiedBoard :=
  ⟨seed0179.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0180 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,1,2,1,0,0,0,2,1,1,0],
  [1,0,0,1,1,1,2,0,2,1,2,0,2,0,0],
  [2,0,1,0,2,1,2,2,1,0,1,1,1,0,2,2,0],
  [0,1,2,0,0,2,2,0,1,1,0,1,0,0,2,0,2,0,1]
]

def cert0180n : CertifiedBoard :=
  ⟨seed0180, by apply FastValid.valid; decide +kernel⟩

def cert0180r : CertifiedBoard :=
  ⟨seed0180.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0181 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,1,2,1,0,0,0,2,1,1,1],
  [1,1,0,1,1,0,2,1,0,0,1,2,0,1,1],
  [2,0,0,2,1,2,2,0,1,0,2,2,0,2,0,2,0],
  [1,1,2,0,1,1,1,0,1,0,0,2,2,1,2,0,2,0,0]
]

def cert0181n : CertifiedBoard :=
  ⟨seed0181, by apply FastValid.valid; decide +kernel⟩

def cert0181r : CertifiedBoard :=
  ⟨seed0181.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0182 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,1,2,1,0,0,2,0,2,1,1],
  [2,0,2,0,1,0,2,1,2,0,1,1,2,2,0],
  [1,1,1,0,1,0,0,1,1,1,0,2,0,0,2,2,0],
  [2,0,1,1,0,0,0,2,1,2,0,2,2,1,0,1,2,0,0]
]

def cert0182n : CertifiedBoard :=
  ⟨seed0182, by apply FastValid.valid; decide +kernel⟩

def cert0182r : CertifiedBoard :=
  ⟨seed0182.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0183 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,1,2,1,0,0,2,1,1,1,0],
  [1,0,2,2,0,0,2,1,2,0,1,1,1,0,0],
  [1,0,0,2,2,1,0,1,2,0,2,1,2,2,0,1,0],
  [0,0,0,1,1,2,0,2,0,1,1,0,1,0,2,0,2,0,0]
]

def cert0183n : CertifiedBoard :=
  ⟨seed0183, by apply FastValid.valid; decide +kernel⟩

def cert0183r : CertifiedBoard :=
  ⟨seed0183.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0184 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,1,2,1,0,0,2,1,1,2,0],
  [2,0,2,0,1,1,1,1,0,0,2,0,2,0,0],
  [1,0,2,2,1,2,2,0,1,0,1,0,1,1,0,2,1],
  [2,1,2,0,1,2,0,2,2,0,0,2,1,0,0,0,1,1,0]
]

def cert0184n : CertifiedBoard :=
  ⟨seed0184, by apply FastValid.valid; decide +kernel⟩

def cert0184r : CertifiedBoard :=
  ⟨seed0184.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0185 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,1,2,1,0,0,2,2,1,1,2],
  [2,0,0,1,1,1,1,0,1,0,1,2,2,0,1],
  [1,2,0,2,1,2,0,1,0,0,0,2,0,2,1,0,0],
  [0,1,1,0,2,0,0,2,0,2,2,0,1,1,0,2,1,2,0]
]

def cert0185n : CertifiedBoard :=
  ⟨seed0185, by apply FastValid.valid; decide +kernel⟩

def cert0185r : CertifiedBoard :=
  ⟨seed0185.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0186 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,1,2,1,0,0,2,2,1,1,2],
  [2,0,0,1,1,1,1,0,1,0,1,2,2,0,1],
  [1,2,0,2,1,2,0,2,0,1,0,0,0,2,1,0,0],
  [0,1,1,0,2,0,1,1,0,2,0,0,2,2,0,2,1,2,0]
]

def cert0186n : CertifiedBoard :=
  ⟨seed0186, by apply FastValid.valid; decide +kernel⟩

def cert0186r : CertifiedBoard :=
  ⟨seed0186.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0187 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,1,2,1,0,1,0,0,2,2,1],
  [2,1,0,0,1,1,1,1,0,0,2,0,2,0,0],
  [0,1,1,0,2,1,2,2,0,2,2,0,1,1,2,0,1],
  [2,0,2,0,1,0,2,1,1,0,1,2,0,0,0,2,1,2,0]
]

def cert0187n : CertifiedBoard :=
  ⟨seed0187, by apply FastValid.valid; decide +kernel⟩

def cert0187r : CertifiedBoard :=
  ⟨seed0187.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0188 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,1,2,1,0,1,0,2,2,1,1],
  [2,2,0,0,1,1,2,0,2,0,1,2,0,0,0],
  [1,0,0,2,1,2,2,0,2,0,1,1,1,1,0,1,0],
  [1,1,0,0,2,0,1,1,0,2,1,0,0,2,1,2,0,2,2]
]

def cert0188n : CertifiedBoard :=
  ⟨seed0188, by apply FastValid.valid; decide +kernel⟩

def cert0188r : CertifiedBoard :=
  ⟨seed0188.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0189 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,1,2,1,0,1,1,0,0,2,1],
  [0,1,0,2,0,2,2,0,1,0,0,2,1,1,1],
  [2,1,2,2,0,1,1,2,0,2,1,0,1,2,0,0,0],
  [1,1,1,0,2,0,0,2,0,2,2,1,2,0,1,1,0,0,1]
]

def cert0189n : CertifiedBoard :=
  ⟨seed0189, by apply FastValid.valid; decide +kernel⟩

def cert0189r : CertifiedBoard :=
  ⟨seed0189.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0190 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,1,2,1,0,1,1,2,0,2,1],
  [0,1,0,2,0,2,2,0,1,0,0,2,1,1,1],
  [2,1,2,2,0,1,1,0,0,2,1,0,1,2,0,0,0],
  [1,1,1,0,2,0,0,2,0,2,2,1,2,0,1,1,0,0,1]
]

def cert0190n : CertifiedBoard :=
  ⟨seed0190, by apply FastValid.valid; decide +kernel⟩

def cert0190r : CertifiedBoard :=
  ⟨seed0190.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0191 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,1,2,1,0,2,0,1,1,1,2],
  [2,2,0,1,1,0,0,0,2,1,0,0,2,1,1],
  [1,2,0,2,1,2,0,0,1,0,1,1,0,2,2,0,0],
  [1,1,1,0,1,2,2,1,2,0,2,0,1,0,0,2,0,2,2]
]

def cert0191n : CertifiedBoard :=
  ⟨seed0191, by apply FastValid.valid; decide +kernel⟩

def cert0191r : CertifiedBoard :=
  ⟨seed0191.map List.reverse, by apply FastValid.valid; decide +kernel⟩

end TBoards.Extended
