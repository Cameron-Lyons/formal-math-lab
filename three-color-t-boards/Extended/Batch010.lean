import Extended.Batch006

/- Generated from extended_seeds.json. Published seeds 0–4:
   Qiyuan Ma, DOI 10.5281/zenodo.23631079, CC-BY-4.0. -/

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.Extended

def seed0320 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,1,1,0,0,2,1,1,1,0,2],
  [0,2,1,2,2,0,2,0,2,1,2,1,0,0,0],
  [0,1,0,1,2,0,2,2,1,0,0,2,0,1,1,0,1],
  [1,0,2,0,1,1,2,0,1,2,0,0,2,2,0,0,0,1,0]
]

def cert0320n : CertifiedBoard :=
  ⟨seed0320, by apply FastValid.valid; decide +kernel⟩

def cert0320r : CertifiedBoard :=
  ⟨seed0320.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0321 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,1,1,0,0,2,1,1,2,0,1],
  [0,2,0,1,2,0,2,2,0,2,0,1,2,0,0],
  [0,1,1,0,1,1,1,0,0,0,2,1,2,2,1,0,2],
  [2,0,0,0,2,1,2,1,0,0,1,0,1,0,2,2,0,2,0]
]

def cert0321n : CertifiedBoard :=
  ⟨seed0321, by apply FastValid.valid; decide +kernel⟩

def cert0321r : CertifiedBoard :=
  ⟨seed0321.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0322 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,0,0,0,0,2,0,1,1,1],
  [1,1,0,1,2,0,2,2,0,0,2,0,1,1,1],
  [1,1,0,0,1,0,0,2,2,1,2,0,2,1,2,2,0],
  [2,0,2,1,0,2,0,1,0,2,1,0,1,1,2,1,1,0,0]
]

def cert0322n : CertifiedBoard :=
  ⟨seed0322, by apply FastValid.valid; decide +kernel⟩

def cert0322r : CertifiedBoard :=
  ⟨seed0322.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0323 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,0,0,0,0,2,2,1,1,1],
  [0,2,0,1,1,0,0,2,1,0,1,1,1,0,0],
  [1,1,0,0,1,2,2,0,2,1,2,0,2,1,0,2,2],
  [2,2,0,1,0,1,0,2,0,0,2,0,1,1,2,1,2,0,2]
]

def cert0323n : CertifiedBoard :=
  ⟨seed0323, by apply FastValid.valid; decide +kernel⟩

def cert0323r : CertifiedBoard :=
  ⟨seed0323.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0324 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,0,0,0,0,2,2,1,1,1],
  [1,0,0,1,0,0,2,2,0,1,1,2,1,0,0],
  [1,1,1,0,1,2,0,0,2,0,2,1,2,0,2,1,2],
  [1,2,2,0,1,1,0,1,0,2,1,0,2,0,2,0,1,1,0]
]

def cert0324n : CertifiedBoard :=
  ⟨seed0324, by apply FastValid.valid; decide +kernel⟩

def cert0324r : CertifiedBoard :=
  ⟨seed0324.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0325 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,0,0,0,0,2,2,1,1,2],
  [0,1,0,1,1,0,2,2,0,2,0,2,1,0,1],
  [1,2,0,2,1,2,1,0,0,2,0,1,1,1,1,0,0],
  [0,1,2,0,1,1,0,2,0,0,2,1,2,2,0,1,0,0,1]
]

def cert0325n : CertifiedBoard :=
  ⟨seed0325, by apply FastValid.valid; decide +kernel⟩

def cert0325r : CertifiedBoard :=
  ⟨seed0325.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0326 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,0,0,0,2,0,2,1,1,1],
  [1,0,2,1,2,0,1,0,0,0,2,0,1,1,0],
  [1,1,1,0,0,2,2,0,2,0,2,2,1,2,1,0,1],
  [0,1,2,2,0,0,1,1,2,0,1,1,0,1,0,2,1,0,0]
]

def cert0326n : CertifiedBoard :=
  ⟨seed0326, by apply FastValid.valid; decide +kernel⟩

def cert0326r : CertifiedBoard :=
  ⟨seed0326.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0327 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,0,0,0,2,1,1,2,0,1],
  [0,2,1,2,2,1,0,1,0,1,1,1,0,2,0],
  [0,1,1,1,0,2,1,2,0,2,0,1,0,0,2,0,2],
  [2,0,1,2,1,0,0,0,2,2,0,2,2,0,0,1,1,0,0]
]

def cert0327n : CertifiedBoard :=
  ⟨seed0327, by apply FastValid.valid; decide +kernel⟩

def cert0327r : CertifiedBoard :=
  ⟨seed0327.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0328 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,0,0,2,0,1,1,1,2,0],
  [2,0,0,1,0,1,0,2,1,2,1,0,0,0,2],
  [1,0,2,2,0,2,1,2,0,2,1,1,1,0,1,1,0],
  [0,2,0,2,2,1,0,0,0,2,0,1,2,2,0,1,1,0,0]
]

def cert0328n : CertifiedBoard :=
  ⟨seed0328, by apply FastValid.valid; decide +kernel⟩

def cert0328r : CertifiedBoard :=
  ⟨seed0328.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0329 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,0,0,2,0,2,1,1,0,2],
  [0,2,1,2,2,1,0,2,2,0,2,1,2,0,1],
  [0,1,1,1,1,2,0,1,0,1,1,0,0,0,0,1,0],
  [1,0,1,2,1,0,0,2,2,0,1,1,0,0,2,0,2,0,0]
]

def cert0329n : CertifiedBoard :=
  ⟨seed0329, by apply FastValid.valid; decide +kernel⟩

def cert0329r : CertifiedBoard :=
  ⟨seed0329.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0330 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,0,0,2,0,2,1,1,1,2],
  [1,2,0,0,0,0,1,0,2,2,1,2,1,0,1],
  [1,1,0,0,2,1,0,2,1,2,0,2,0,1,1,0,0],
  [0,1,2,2,0,2,2,0,1,1,1,0,0,2,0,1,0,1,1]
]

def cert0330n : CertifiedBoard :=
  ⟨seed0330, by apply FastValid.valid; decide +kernel⟩

def cert0330r : CertifiedBoard :=
  ⟨seed0330.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0331 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,0,0,2,1,0,0,2,2,1],
  [2,1,2,0,2,0,1,0,1,0,1,1,1,2,2],
  [0,1,1,1,0,0,0,2,0,0,0,1,2,1,2,0,1],
  [2,2,0,1,1,0,2,1,0,2,0,2,2,0,2,1,1,0,0]
]

def cert0331n : CertifiedBoard :=
  ⟨seed0331, by apply FastValid.valid; decide +kernel⟩

def cert0331r : CertifiedBoard :=
  ⟨seed0331.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0332 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,0,0,2,1,0,1,1,1,0],
  [1,0,1,1,1,2,0,0,0,0,2,0,2,1,2],
  [1,2,2,0,1,1,0,2,0,1,0,2,0,2,2,0,1],
  [0,1,2,0,2,1,2,1,0,0,1,0,0,2,2,1,1,0,0]
]

def cert0332n : CertifiedBoard :=
  ⟨seed0332, by apply FastValid.valid; decide +kernel⟩

def cert0332r : CertifiedBoard :=
  ⟨seed0332.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0333 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,0,0,2,1,0,1,1,2,0],
  [0,2,1,2,2,1,0,0,0,0,1,1,1,0,1],
  [0,1,1,1,0,2,2,0,0,2,0,1,2,1,2,0,2],
  [2,0,2,0,1,0,2,0,2,2,0,1,0,0,2,1,1,0,0]
]

def cert0333n : CertifiedBoard :=
  ⟨seed0333, by apply FastValid.valid; decide +kernel⟩

def cert0333r : CertifiedBoard :=
  ⟨seed0333.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0334 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,0,0,2,1,2,0,1,1,0],
  [1,0,1,1,1,2,0,2,2,0,2,0,2,1,2],
  [1,0,0,1,2,1,0,2,2,1,1,0,1,0,0,0,0],
  [1,2,2,0,1,1,1,0,0,2,0,1,0,2,0,0,2,1,0]
]

def cert0334n : CertifiedBoard :=
  ⟨seed0334, by apply FastValid.valid; decide +kernel⟩

def cert0334r : CertifiedBoard :=
  ⟨seed0334.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0335 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,0,1,0,0,0,2,0,1,1],
  [1,0,0,1,1,0,1,2,0,2,0,2,2,0,2],
  [1,1,0,2,1,2,1,2,2,1,0,1,1,2,0,0,0],
  [0,2,0,0,2,1,0,2,1,1,1,1,0,0,2,2,0,1,0]
]

def cert0335n : CertifiedBoard :=
  ⟨seed0335, by apply FastValid.valid; decide +kernel⟩

def cert0335r : CertifiedBoard :=
  ⟨seed0335.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0336 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,0,1,0,1,2,0,2,2,1],
  [2,1,0,0,2,0,2,1,2,1,1,0,0,0,0],
  [0,2,1,0,1,0,2,0,1,1,1,1,0,2,2,0,1],
  [0,1,1,0,0,2,0,0,2,1,2,2,0,0,1,1,2,0,2]
]

def cert0336n : CertifiedBoard :=
  ⟨seed0336, by apply FastValid.valid; decide +kernel⟩

def cert0336r : CertifiedBoard :=
  ⟨seed0336.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0337 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,0,1,0,2,1,1,1,0,1],
  [1,0,0,2,0,2,2,0,1,1,1,0,0,1,2],
  [0,1,1,0,2,0,2,2,1,2,1,2,2,0,0,0,0],
  [1,2,0,0,2,0,1,1,2,0,2,1,0,0,2,1,0,1,0]
]

def cert0337n : CertifiedBoard :=
  ⟨seed0337, by apply FastValid.valid; decide +kernel⟩

def cert0337r : CertifiedBoard :=
  ⟨seed0337.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0338 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,0,1,0,2,1,1,2,0,2],
  [2,0,1,0,0,2,1,0,1,1,1,0,1,1,1],
  [0,2,1,2,2,0,0,0,0,1,2,1,2,0,2,0,0],
  [1,1,0,0,2,2,1,0,0,2,2,0,1,1,0,2,0,2,0]
]

def cert0338n : CertifiedBoard :=
  ⟨seed0338, by apply FastValid.valid; decide +kernel⟩

def cert0338r : CertifiedBoard :=
  ⟨seed0338.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0339 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,0,1,1,1,0,0,0,2,1],
  [0,1,0,1,0,2,0,0,2,0,0,1,1,2,2],
  [2,1,2,1,0,0,2,2,0,1,1,0,2,1,2,0,1],
  [2,2,1,0,1,2,0,2,0,2,2,0,2,1,1,1,0,0,0]
]

def cert0339n : CertifiedBoard :=
  ⟨seed0339, by apply FastValid.valid; decide +kernel⟩

def cert0339r : CertifiedBoard :=
  ⟨seed0339.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0340 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,0,1,1,1,0,0,2,1,1],
  [2,0,1,1,1,0,0,2,1,0,1,0,1,0,0],
  [2,2,1,2,1,2,2,0,0,0,0,1,2,0,0,2,2],
  [1,1,2,0,2,2,0,1,1,0,2,0,2,0,2,1,0,2,0]
]

def cert0340n : CertifiedBoard :=
  ⟨seed0340, by apply FastValid.valid; decide +kernel⟩

def cert0340r : CertifiedBoard :=
  ⟨seed0340.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0341 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,0,1,1,1,0,2,1,1,0],
  [0,1,1,0,0,0,2,1,2,2,0,2,0,2,1],
  [1,0,1,2,1,0,2,0,1,0,0,2,2,1,2,0,0],
  [2,1,0,0,2,2,0,2,0,0,0,1,0,1,1,1,2,0,1]
]

def cert0341n : CertifiedBoard :=
  ⟨seed0341, by apply FastValid.valid; decide +kernel⟩

def cert0341r : CertifiedBoard :=
  ⟨seed0341.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0342 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,0,1,1,1,1,0,0,2,1],
  [1,0,0,1,0,2,1,0,0,2,1,0,1,1,0],
  [1,2,2,0,0,0,2,2,0,2,0,2,0,1,2,1,2],
  [2,1,2,0,1,0,2,2,1,1,0,1,1,2,0,2,0,0,0]
]

def cert0342n : CertifiedBoard :=
  ⟨seed0342, by apply FastValid.valid; decide +kernel⟩

def cert0342r : CertifiedBoard :=
  ⟨seed0342.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0343 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,0,1,1,1,1,0,0,2,2],
  [2,2,0,0,0,0,1,2,2,0,0,2,2,1,1],
  [1,1,2,0,1,1,0,0,2,0,2,1,0,1,1,0,0],
  [0,2,0,2,1,2,1,0,1,0,2,0,1,0,2,1,2,0,2]
]

def cert0343n : CertifiedBoard :=
  ⟨seed0343, by apply FastValid.valid; decide +kernel⟩

def cert0343r : CertifiedBoard :=
  ⟨seed0343.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0344 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,0,1,1,1,1,0,1,1,2],
  [0,1,0,0,2,0,2,1,2,2,0,1,2,1,1],
  [1,2,0,0,2,2,1,0,0,0,0,2,0,2,1,0,0],
  [1,1,0,2,1,2,0,1,0,1,1,0,2,2,0,2,0,0,1]
]

def cert0344n : CertifiedBoard :=
  ⟨seed0344, by apply FastValid.valid; decide +kernel⟩

def cert0344r : CertifiedBoard :=
  ⟨seed0344.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0345 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,0,1,1,1,1,0,2,2,1],
  [2,1,0,0,0,0,1,2,2,0,0,2,1,1,0],
  [1,0,0,2,2,0,2,1,0,1,1,0,2,0,2,0,1],
  [0,1,0,1,1,2,0,0,2,1,2,1,2,0,2,0,1,0,0]
]

def cert0345n : CertifiedBoard :=
  ⟨seed0345, by apply FastValid.valid; decide +kernel⟩

def cert0345r : CertifiedBoard :=
  ⟨seed0345.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0346 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,0,1,1,1,1,2,0,1,1],
  [1,1,0,2,0,2,0,2,1,2,2,1,2,1,0],
  [1,0,0,0,2,0,2,1,0,1,0,0,0,2,2,0,0],
  [2,0,0,1,0,0,2,1,1,0,1,2,0,1,1,0,2,2,0]
]

def cert0346n : CertifiedBoard :=
  ⟨seed0346, by apply FastValid.valid; decide +kernel⟩

def cert0346r : CertifiedBoard :=
  ⟨seed0346.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0347 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,0,1,1,2,1,1,0,0,0],
  [2,1,0,1,2,0,1,0,0,2,1,2,0,2,1],
  [2,2,1,0,0,2,2,0,0,1,0,2,0,1,1,1,0],
  [1,0,1,1,1,0,2,0,2,0,0,0,2,1,2,2,0,2,2]
]

def cert0347n : CertifiedBoard :=
  ⟨seed0347, by apply FastValid.valid; decide +kernel⟩

def cert0347r : CertifiedBoard :=
  ⟨seed0347.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0348 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,0,1,1,2,1,1,1,0,0],
  [2,1,0,1,0,1,1,1,0,2,1,0,0,2,1],
  [0,2,0,2,0,0,1,2,2,0,2,1,2,0,0,0,2],
  [2,1,2,0,1,1,0,0,0,2,2,0,2,0,1,0,2,2,1]
]

def cert0348n : CertifiedBoard :=
  ⟨seed0348, by apply FastValid.valid; decide +kernel⟩

def cert0348r : CertifiedBoard :=
  ⟨seed0348.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0349 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,0,1,1,2,2,1,1,0,0],
  [1,2,0,0,0,0,1,0,0,2,2,0,0,2,1],
  [2,1,0,1,1,0,2,0,2,2,0,2,1,0,1,1,1],
  [1,1,1,0,0,2,1,2,0,2,0,1,0,2,0,1,2,1,2]
]

def cert0349n : CertifiedBoard :=
  ⟨seed0349, by apply FastValid.valid; decide +kernel⟩

def cert0349r : CertifiedBoard :=
  ⟨seed0349.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0350 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,0,1,1,2,2,1,1,0,0],
  [2,1,0,1,2,0,2,0,0,2,1,2,1,2,0],
  [2,0,1,0,0,0,0,2,0,0,1,1,1,1,0,2,1],
  [2,0,2,0,2,2,0,1,0,1,1,0,0,2,1,0,2,2,0]
]

def cert0350n : CertifiedBoard :=
  ⟨seed0350, by apply FastValid.valid; decide +kernel⟩

def cert0350r : CertifiedBoard :=
  ⟨seed0350.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0351 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,0,1,1,2,2,1,1,0,2],
  [0,2,2,0,0,2,0,2,0,1,1,1,0,2,1],
  [1,2,0,2,0,1,0,1,1,1,0,0,2,1,0,0,0],
  [2,1,2,0,0,0,1,0,1,2,1,0,0,2,2,0,2,1,2]
]

def cert0351n : CertifiedBoard :=
  ⟨seed0351, by apply FastValid.valid; decide +kernel⟩

def cert0351r : CertifiedBoard :=
  ⟨seed0351.map List.reverse, by apply FastValid.valid; decide +kernel⟩

end TBoards.Extended
