import Extended.Batch004

/- Generated from extended_seeds.json. Published seeds 0–4:
   Qiyuan Ma, DOI 10.5281/zenodo.23631079, CC-BY-4.0. -/

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.Extended

def seed0256 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,2,1,2,0,2,0,1,1,0,0],
  [2,1,2,0,2,0,2,1,0,1,1,0,0,2,1],
  [2,1,1,1,1,0,2,2,1,0,0,0,2,0,0,1,1],
  [1,1,2,2,0,1,0,1,2,0,0,1,0,2,2,0,1,2,1]
]

def cert0256n : CertifiedBoard :=
  ⟨seed0256, by apply FastValid.valid; decide +kernel⟩

def cert0256r : CertifiedBoard :=
  ⟨seed0256.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0257 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,2,1,2,1,1,0,0,1,1,1],
  [2,1,0,0,2,0,1,2,2,0,0,1,2,0,0],
  [2,0,1,0,1,0,1,1,1,2,0,2,0,2,1,2,0],
  [1,1,0,2,0,1,1,0,0,0,2,2,0,2,2,1,0,2,1]
]

def cert0257n : CertifiedBoard :=
  ⟨seed0257, by apply FastValid.valid; decide +kernel⟩

def cert0257r : CertifiedBoard :=
  ⟨seed0257.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0258 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,2,1,2,1,1,0,1,1,1,0],
  [1,0,0,1,0,2,0,1,1,1,0,0,0,2,1],
  [2,1,0,2,0,0,2,1,2,2,0,2,2,0,0,1,2],
  [1,2,0,1,1,2,0,1,2,0,2,0,2,2,1,0,1,0,0]
]

def cert0258n : CertifiedBoard :=
  ⟨seed0258, by apply FastValid.valid; decide +kernel⟩

def cert0258r : CertifiedBoard :=
  ⟨seed0258.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0259 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,2,1,2,1,1,0,1,1,1,2],
  [1,2,0,0,1,2,0,2,0,2,0,1,2,2,1],
  [1,0,0,1,0,0,2,0,2,1,2,0,1,1,0,0,0],
  [2,1,0,1,1,1,0,2,2,0,1,0,2,2,0,0,2,1,0]
]

def cert0259n : CertifiedBoard :=
  ⟨seed0259, by apply FastValid.valid; decide +kernel⟩

def cert0259r : CertifiedBoard :=
  ⟨seed0259.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0260 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,2,1,2,1,1,0,2,0,1,1],
  [2,1,0,1,0,1,1,2,0,0,2,2,0,1,2],
  [1,1,0,0,1,0,0,2,0,2,0,0,1,2,0,2,1],
  [1,2,2,0,2,1,0,2,2,1,2,0,1,1,1,1,0,0,0]
]

def cert0260n : CertifiedBoard :=
  ⟨seed0260, by apply FastValid.valid; decide +kernel⟩

def cert0260r : CertifiedBoard :=
  ⟨seed0260.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0261 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,2,1,2,1,1,0,2,0,2,1],
  [2,1,0,2,2,1,0,0,2,0,1,1,0,1,1],
  [1,2,0,1,1,1,2,0,0,2,2,0,0,0,1,0,0],
  [1,1,1,0,1,2,2,0,1,0,0,1,2,0,2,0,2,1,2]
]

def cert0261n : CertifiedBoard :=
  ⟨seed0261, by apply FastValid.valid; decide +kernel⟩

def cert0261r : CertifiedBoard :=
  ⟨seed0261.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0262 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,2,1,2,1,1,1,0,0,1,1],
  [1,1,0,0,2,0,2,1,0,0,2,0,2,0,0],
  [1,2,0,1,0,2,2,0,1,0,1,1,2,0,2,1,2],
  [1,1,0,2,2,0,1,2,0,0,0,1,2,2,1,0,1,1,1]
]

def cert0262n : CertifiedBoard :=
  ⟨seed0262, by apply FastValid.valid; decide +kernel⟩

def cert0262r : CertifiedBoard :=
  ⟨seed0262.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0263 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,2,1,2,1,1,1,0,0,1,1],
  [2,0,0,2,2,1,0,1,2,2,0,1,0,0,0],
  [1,1,1,0,1,2,0,0,1,0,2,2,0,2,1,2,0],
  [2,0,1,1,0,0,2,1,0,2,0,2,0,1,1,2,0,2,0]
]

def cert0263n : CertifiedBoard :=
  ⟨seed0263, by apply FastValid.valid; decide +kernel⟩

def cert0263r : CertifiedBoard :=
  ⟨seed0263.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0264 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,2,1,2,1,1,1,0,1,1,1],
  [2,0,2,1,2,0,1,2,2,0,0,1,0,0,0],
  [1,0,2,2,1,0,0,2,0,2,1,0,1,2,0,1,0],
  [1,1,0,2,0,1,1,0,0,1,1,2,0,0,2,2,0,2,0]
]

def cert0264n : CertifiedBoard :=
  ⟨seed0264, by apply FastValid.valid; decide +kernel⟩

def cert0264r : CertifiedBoard :=
  ⟨seed0264.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0265 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,2,1,2,1,1,1,0,1,1,2],
  [0,1,1,0,2,2,0,1,0,0,2,0,1,1,1],
  [1,2,0,2,0,2,0,2,1,0,0,2,1,2,0,0,0],
  [1,1,0,2,2,1,0,0,1,2,2,0,0,1,2,0,1,0,1]
]

def cert0265n : CertifiedBoard :=
  ⟨seed0265, by apply FastValid.valid; decide +kernel⟩

def cert0265r : CertifiedBoard :=
  ⟨seed0265.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0266 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,2,1,2,1,1,1,0,1,2,0],
  [0,1,1,0,1,1,0,0,2,0,0,1,0,2,1],
  [2,1,2,2,0,1,2,0,2,2,1,0,0,0,2,0,1],
  [2,0,1,1,1,2,0,2,2,0,2,1,0,2,0,0,1,0,0]
]

def cert0266n : CertifiedBoard :=
  ⟨seed0266, by apply FastValid.valid; decide +kernel⟩

def cert0266r : CertifiedBoard :=
  ⟨seed0266.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0267 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,2,1,2,1,1,1,0,1,2,0],
  [1,1,0,0,2,0,2,2,0,0,0,1,0,2,2],
  [2,0,1,2,0,2,1,0,0,1,0,2,1,0,1,1,1],
  [2,2,1,2,0,1,1,2,2,0,0,2,0,2,0,1,1,0,0]
]

def cert0267n : CertifiedBoard :=
  ⟨seed0267, by apply FastValid.valid; decide +kernel⟩

def cert0267r : CertifiedBoard :=
  ⟨seed0267.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0268 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,2,1,2,1,1,1,0,2,2,1],
  [2,0,0,2,0,1,2,0,2,0,1,0,1,2,0],
  [0,1,1,0,2,0,1,1,2,0,2,1,0,1,0,0,1],
  [2,1,2,2,0,2,1,0,0,0,1,1,1,0,0,2,2,0,0]
]

def cert0268n : CertifiedBoard :=
  ⟨seed0268, by apply FastValid.valid; decide +kernel⟩

def cert0268r : CertifiedBoard :=
  ⟨seed0268.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0269 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,2,1,2,1,1,1,1,0,0,1],
  [2,1,2,0,1,1,0,1,2,0,1,1,0,0,0],
  [0,1,2,2,1,0,0,2,2,0,2,0,2,0,0,2,1],
  [0,0,1,0,2,1,0,1,1,2,0,2,2,0,1,0,2,0,0]
]

def cert0269n : CertifiedBoard :=
  ⟨seed0269, by apply FastValid.valid; decide +kernel⟩

def cert0269r : CertifiedBoard :=
  ⟨seed0269.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0270 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,2,1,2,1,1,1,1,0,0,1],
  [2,1,2,0,1,1,0,1,2,0,1,1,0,0,0],
  [0,1,2,2,1,0,0,2,2,0,2,0,2,0,0,2,1],
  [1,0,1,0,2,0,0,1,1,2,0,2,2,0,1,0,2,1,0]
]

def cert0270n : CertifiedBoard :=
  ⟨seed0270, by apply FastValid.valid; decide +kernel⟩

def cert0270r : CertifiedBoard :=
  ⟨seed0270.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0271 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,2,1,2,1,1,1,1,0,0,1],
  [2,1,2,0,1,1,0,1,2,2,0,1,0,0,2],
  [0,1,2,0,2,1,0,0,1,0,2,0,0,0,2,2,1],
  [0,2,0,2,2,0,1,1,0,2,0,2,1,0,1,1,2,0,0]
]

def cert0271n : CertifiedBoard :=
  ⟨seed0271, by apply FastValid.valid; decide +kernel⟩

def cert0271r : CertifiedBoard :=
  ⟨seed0271.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0272 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,2,1,2,1,1,1,1,0,0,1],
  [2,1,2,0,2,0,2,2,0,1,1,0,2,0,0],
  [0,1,2,2,1,0,1,1,2,0,0,2,0,1,1,0,0],
  [0,0,1,0,2,1,0,1,2,0,2,2,0,1,0,0,0,2,1]
]

def cert0272n : CertifiedBoard :=
  ⟨seed0272, by apply FastValid.valid; decide +kernel⟩

def cert0272r : CertifiedBoard :=
  ⟨seed0272.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0273 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,2,1,2,1,1,1,1,0,1,2],
  [2,0,2,1,0,0,2,2,0,1,1,0,1,2,0],
  [1,0,2,2,1,0,0,1,1,2,0,0,0,2,0,1,0],
  [1,2,2,0,2,0,2,0,1,0,0,1,1,0,2,1,2,0,0]
]

def cert0273n : CertifiedBoard :=
  ⟨seed0273, by apply FastValid.valid; decide +kernel⟩

def cert0273r : CertifiedBoard :=
  ⟨seed0273.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0274 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,2,1,2,1,1,1,1,0,2,1],
  [1,0,2,1,0,0,0,1,2,0,1,1,0,1,0],
  [2,1,0,1,2,2,0,0,2,0,2,2,0,2,0,0,1],
  [0,1,1,0,0,2,2,1,2,0,1,1,2,0,2,0,1,0,0]
]

def cert0274n : CertifiedBoard :=
  ⟨seed0274, by apply FastValid.valid; decide +kernel⟩

def cert0274r : CertifiedBoard :=
  ⟨seed0274.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0275 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,2,1,2,1,1,1,1,0,2,2],
  [1,0,0,2,2,1,0,1,2,0,0,0,1,1,2],
  [1,2,2,0,2,0,1,1,0,0,1,0,2,0,1,0,0],
  [2,2,0,2,1,2,0,0,2,0,1,1,0,1,2,0,2,1,0]
]

def cert0275n : CertifiedBoard :=
  ⟨seed0275, by apply FastValid.valid; decide +kernel⟩

def cert0275r : CertifiedBoard :=
  ⟨seed0275.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0276 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,2,1,2,1,1,1,1,2,0,2],
  [2,0,0,1,1,0,0,1,2,2,0,2,1,0,0],
  [0,2,0,2,0,1,0,2,1,0,1,2,0,1,1,0,1],
  [0,1,0,2,2,1,2,0,1,1,0,0,2,2,0,0,0,2,0]
]

def cert0276n : CertifiedBoard :=
  ⟨seed0276, by apply FastValid.valid; decide +kernel⟩

def cert0276r : CertifiedBoard :=
  ⟨seed0276.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0277 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,2,1,2,1,1,1,2,0,1,1],
  [0,1,1,0,2,1,0,1,2,0,2,2,0,0,0],
  [2,1,0,0,2,0,2,0,1,1,0,0,1,2,0,2,1],
  [1,1,1,0,1,0,2,2,1,2,2,0,0,1,0,0,2,0,1]
]

def cert0277n : CertifiedBoard :=
  ⟨seed0277, by apply FastValid.valid; decide +kernel⟩

def cert0277r : CertifiedBoard :=
  ⟨seed0277.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0278 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,2,1,2,1,1,1,2,0,1,2],
  [1,2,0,0,2,1,0,1,2,0,2,2,0,0,1],
  [0,1,0,2,0,1,1,0,1,1,0,2,0,2,1,0,0],
  [1,0,0,2,2,1,2,2,0,2,0,1,1,1,0,0,0,1,0]
]

def cert0278n : CertifiedBoard :=
  ⟨seed0278, by apply FastValid.valid; decide +kernel⟩

def cert0278r : CertifiedBoard :=
  ⟨seed0278.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0279 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,2,1,2,2,1,0,0,1,1,0],
  [1,2,0,1,1,2,1,1,1,1,0,1,1,0,0],
  [2,2,0,2,0,0,2,0,1,0,0,0,1,2,0,2,2],
  [1,0,2,1,2,0,0,2,2,0,2,1,0,2,0,1,0,1,2]
]

def cert0279n : CertifiedBoard :=
  ⟨seed0279, by apply FastValid.valid; decide +kernel⟩

def cert0279r : CertifiedBoard :=
  ⟨seed0279.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0280 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,2,1,2,2,1,0,0,1,1,2],
  [1,2,0,0,2,0,2,1,1,1,0,1,1,0,1],
  [0,1,0,2,1,2,0,2,2,0,0,0,1,2,1,0,0],
  [1,0,0,2,0,2,0,1,1,1,0,2,2,0,1,2,0,1,0]
]

def cert0280n : CertifiedBoard :=
  ⟨seed0280, by apply FastValid.valid; decide +kernel⟩

def cert0280r : CertifiedBoard :=
  ⟨seed0280.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0281 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,2,1,2,2,1,0,0,1,2,0],
  [2,0,1,0,1,1,1,1,2,1,2,0,2,1,0],
  [2,0,1,1,0,0,2,0,1,0,1,1,0,2,2,0,0],
  [1,0,2,0,0,0,2,1,1,0,0,1,2,0,2,0,2,2,0]
]

def cert0281n : CertifiedBoard :=
  ⟨seed0281, by apply FastValid.valid; decide +kernel⟩

def cert0281r : CertifiedBoard :=
  ⟨seed0281.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0282 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,2,1,2,2,1,0,1,1,0,0],
  [2,1,0,1,1,1,1,2,0,0,1,1,0,2,1],
  [2,0,1,0,0,0,2,0,1,2,0,1,2,0,2,2,0],
  [0,0,1,0,0,2,2,0,2,0,2,1,2,1,1,0,2,0,0]
]

def cert0282n : CertifiedBoard :=
  ⟨seed0282, by apply FastValid.valid; decide +kernel⟩

def cert0282r : CertifiedBoard :=
  ⟨seed0282.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0283 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,2,1,2,2,1,0,1,1,0,2],
  [0,2,2,0,1,2,0,2,0,0,1,1,0,2,1],
  [2,1,2,0,1,0,0,1,1,1,0,1,2,1,0,0,0],
  [2,1,1,1,2,0,2,0,2,0,1,0,0,2,2,0,0,2,1]
]

def cert0283n : CertifiedBoard :=
  ⟨seed0283, by apply FastValid.valid; decide +kernel⟩

def cert0283r : CertifiedBoard :=
  ⟨seed0283.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0284 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,2,1,2,2,1,0,1,1,0,2],
  [2,1,2,0,0,1,1,2,0,0,1,2,1,0,0],
  [0,2,2,0,1,0,0,0,2,0,1,1,1,1,0,2,1],
  [2,0,2,1,1,0,0,2,2,0,2,0,2,0,1,0,1,2,0]
]

def cert0284n : CertifiedBoard :=
  ⟨seed0284, by apply FastValid.valid; decide +kernel⟩

def cert0284r : CertifiedBoard :=
  ⟨seed0284.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0285 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,2,1,2,2,1,0,1,1,1,2],
  [0,1,0,0,1,2,0,2,2,0,2,0,0,0,1],
  [1,2,0,2,0,1,0,0,2,1,1,0,2,1,0,1,1],
  [1,1,1,0,2,0,0,2,2,0,1,2,1,2,0,1,1,0,0]
]

def cert0285n : CertifiedBoard :=
  ⟨seed0285, by apply FastValid.valid; decide +kernel⟩

def cert0285r : CertifiedBoard :=
  ⟨seed0285.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0286 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,2,1,2,2,1,0,1,1,2,0],
  [2,0,1,0,0,1,1,0,0,2,2,0,2,0,0],
  [1,1,1,0,0,1,1,1,0,2,0,2,1,0,2,1,2],
  [1,2,0,1,2,0,2,0,0,0,2,2,0,1,0,1,2,1,1]
]

def cert0286n : CertifiedBoard :=
  ⟨seed0286, by apply FastValid.valid; decide +kernel⟩

def cert0286r : CertifiedBoard :=
  ⟨seed0286.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0287 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,2,1,2,2,1,0,1,2,0,1],
  [0,1,1,0,1,1,1,1,2,1,2,0,2,0,2],
  [0,2,2,0,0,2,0,1,0,0,1,1,0,2,1,0,0],
  [0,1,0,2,2,0,2,0,1,2,0,0,0,2,1,1,0,0,1]
]

def cert0287n : CertifiedBoard :=
  ⟨seed0287, by apply FastValid.valid; decide +kernel⟩

def cert0287r : CertifiedBoard :=
  ⟨seed0287.map List.reverse, by apply FastValid.valid; decide +kernel⟩

end TBoards.Extended
