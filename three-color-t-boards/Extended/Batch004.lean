import Extended.Batch000

/- Generated from extended_seeds.json. Published seeds 0–4:
   Qiyuan Ma, DOI 10.5281/zenodo.23631079, CC-BY-4.0. -/

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.Extended

def seed0128 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [2,2,1,2,2,0,1,1,0,1,2,0,1],
  [1,2,1,0,0,2,0,0,2,0,2,2,2,1,2],
  [1,2,1,1,1,2,1,2,2,2,1,0,1,2,0,2,2],
  [2,2,2,0,0,1,0,0,0,1,0,2,1,1,2,2,0,0,0]
]

def cert0128n : CertifiedBoard :=
  ⟨seed0128, by apply FastValid.valid; decide +kernel⟩

def cert0128r : CertifiedBoard :=
  ⟨seed0128.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0129 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [2,2,1,2,2,0,1,1,1,0,1,0,1],
  [2,1,2,0,0,2,0,0,1,2,0,2,1,1,2],
  [1,2,1,2,2,2,1,1,2,2,2,2,0,0,2,2,1],
  [1,2,1,0,0,1,0,2,0,2,2,0,1,2,1,0,0,0,0]
]

def cert0129n : CertifiedBoard :=
  ⟨seed0129, by apply FastValid.valid; decide +kernel⟩

def cert0129r : CertifiedBoard :=
  ⟨seed0129.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0130 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [2,2,2,0,2,2,1,1,1,0,1,0,2],
  [0,2,0,1,1,2,1,0,0,2,0,2,1,0,1],
  [1,2,2,0,1,2,2,1,2,1,2,2,2,2,1,1,2],
  [1,2,1,2,0,0,0,1,2,0,0,1,0,0,2,2,0,0,0]
]

def cert0130n : CertifiedBoard :=
  ⟨seed0130, by apply FastValid.valid; decide +kernel⟩

def cert0130r : CertifiedBoard :=
  ⟨seed0130.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0131 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [2,2,2,0,2,2,1,1,1,0,1,0,2],
  [0,2,0,1,1,2,1,0,0,2,0,2,1,0,1],
  [1,2,2,0,1,2,2,1,2,1,2,2,2,2,1,1,2],
  [1,2,1,2,0,0,0,2,2,0,0,1,0,0,1,2,0,0,0]
]

def cert0131n : CertifiedBoard :=
  ⟨seed0131, by apply FastValid.valid; decide +kernel⟩

def cert0131r : CertifiedBoard :=
  ⟨seed0131.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0132 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [2,2,2,1,2,0,0,1,0,0,2,0,1],
  [2,1,0,2,0,2,2,0,1,2,2,2,0,2,1],
  [1,2,2,1,2,1,0,1,1,2,2,2,1,2,1,1,1],
  [1,1,2,0,0,1,2,1,1,0,1,0,0,0,0,2,2,0,0]
]

def cert0132n : CertifiedBoard :=
  ⟨seed0132, by apply FastValid.valid; decide +kernel⟩

def cert0132r : CertifiedBoard :=
  ⟨seed0132.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0133 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [2,2,2,1,2,0,1,1,1,2,2,0,1],
  [2,2,1,0,1,2,0,0,1,0,0,2,2,0,0],
  [1,2,2,2,1,0,1,2,1,2,1,1,2,1,2,2,2],
  [0,0,0,1,0,2,0,2,1,1,0,0,2,2,0,2,0,0,0]
]

def cert0133n : CertifiedBoard :=
  ⟨seed0133, by apply FastValid.valid; decide +kernel⟩

def cert0133r : CertifiedBoard :=
  ⟨seed0133.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0134 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [2,2,2,1,2,1,2,2,0,2,0,0,1],
  [1,2,0,1,0,1,1,0,2,2,2,2,0,1,2],
  [1,2,2,0,2,1,1,1,2,2,1,2,1,1,2,0,0],
  [1,0,0,2,0,0,0,2,2,1,0,1,0,0,0,1,2,1,0]
]

def cert0134n : CertifiedBoard :=
  ⟨seed0134, by apply FastValid.valid; decide +kernel⟩

def cert0134r : CertifiedBoard :=
  ⟨seed0134.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0135 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [2,2,2,2,1,2,1,0,1,2,0,0,1],
  [1,2,2,0,0,2,1,2,1,1,2,1,2,2,0],
  [2,0,2,2,2,1,0,0,1,1,1,0,2,2,1,1,2],
  [1,2,0,1,0,1,2,2,0,0,0,2,0,2,0,1,0,0,0]
]

def cert0135n : CertifiedBoard :=
  ⟨seed0135, by apply FastValid.valid; decide +kernel⟩

def cert0135r : CertifiedBoard :=
  ⟨seed0135.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0136 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [2,2,2,2,1,2,1,0,1,2,0,0,1],
  [1,2,2,0,0,2,1,2,1,1,2,1,2,2,0],
  [2,0,2,2,2,1,0,0,1,1,1,0,2,2,1,1,2],
  [1,2,0,2,0,1,2,2,0,0,0,2,0,1,0,1,0,0,0]
]

def cert0136n : CertifiedBoard :=
  ⟨seed0136, by apply FastValid.valid; decide +kernel⟩

def cert0136r : CertifiedBoard :=
  ⟨seed0136.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0137 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [2,2,2,2,1,2,1,1,1,2,0,0,1],
  [1,2,2,0,1,2,1,0,0,0,2,2,0,2,0],
  [1,2,2,2,1,1,0,2,1,2,2,1,2,0,1,1,2],
  [2,0,2,0,0,2,2,0,0,0,1,0,1,2,1,0,1,0,0]
]

def cert0137n : CertifiedBoard :=
  ⟨seed0137, by apply FastValid.valid; decide +kernel⟩

def cert0137r : CertifiedBoard :=
  ⟨seed0137.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0138 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [2,2,2,2,1,2,1,1,1,2,0,0,1],
  [1,2,2,2,1,0,0,0,2,0,2,2,1,0,1],
  [2,2,0,1,0,1,2,2,0,1,1,2,1,2,1,2,2],
  [0,1,2,0,2,1,1,0,2,0,0,1,0,0,0,2,2,0,0]
]

def cert0138n : CertifiedBoard :=
  ⟨seed0138, by apply FastValid.valid; decide +kernel⟩

def cert0138r : CertifiedBoard :=
  ⟨seed0138.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0139 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [2,2,2,2,1,2,1,1,2,2,0,0,1],
  [1,0,0,2,0,1,2,0,2,1,2,2,0,1,0],
  [1,2,1,2,2,0,2,2,2,1,0,1,2,1,1,1,2],
  [1,2,0,0,2,2,1,0,1,0,2,0,0,1,1,0,0,0,0]
]

def cert0139n : CertifiedBoard :=
  ⟨seed0139, by apply FastValid.valid; decide +kernel⟩

def cert0139r : CertifiedBoard :=
  ⟨seed0139.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0140 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [2,2,2,2,1,2,2,2,0,2,0,0,1],
  [1,2,2,0,0,2,1,0,2,0,2,2,1,1,2],
  [1,2,2,1,1,2,1,2,1,2,1,0,1,1,1,0,0],
  [0,1,2,0,1,0,0,0,1,0,1,2,0,0,0,2,2,0,1]
]

def cert0140n : CertifiedBoard :=
  ⟨seed0140, by apply FastValid.valid; decide +kernel⟩

def cert0140r : CertifiedBoard :=
  ⟨seed0140.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0141 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [2,2,2,2,1,2,2,2,0,2,0,0,1],
  [1,2,2,0,0,2,1,0,2,0,2,2,1,1,2],
  [1,2,2,1,1,2,1,2,1,2,1,0,1,1,1,0,0],
  [0,1,2,0,1,0,1,0,0,0,1,2,0,0,0,2,2,0,1]
]

def cert0141n : CertifiedBoard :=
  ⟨seed0141, by apply FastValid.valid; decide +kernel⟩

def cert0141r : CertifiedBoard :=
  ⟨seed0141.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0142 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,1,0,0,0,2,1,1,1,0,1],
  [0,1,0,1,1,1,0,2,2,1,2,0,2,0,0],
  [2,1,2,2,0,1,2,1,0,2,1,0,0,2,0,2,1],
  [2,0,1,1,2,0,0,2,2,0,1,1,0,0,1,2,0,2,0]
]

def cert0142n : CertifiedBoard :=
  ⟨seed0142, by apply FastValid.valid; decide +kernel⟩

def cert0142r : CertifiedBoard :=
  ⟨seed0142.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0143 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,1,0,0,0,2,1,1,1,2,0],
  [2,0,2,1,2,1,0,2,2,1,2,0,1,2,0],
  [1,0,0,2,1,0,1,1,0,2,2,0,1,1,1,0,0],
  [2,0,2,0,1,1,0,1,2,2,0,2,0,0,2,0,0,1,0]
]

def cert0143n : CertifiedBoard :=
  ⟨seed0143, by apply FastValid.valid; decide +kernel⟩

def cert0143r : CertifiedBoard :=
  ⟨seed0143.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0144 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,1,0,0,2,0,2,2,1,1,2],
  [0,0,2,2,0,0,1,1,1,0,1,1,1,0,0],
  [1,2,0,0,2,1,0,2,1,2,1,2,2,0,1,0,1],
  [0,1,2,0,2,0,2,0,1,2,0,1,1,0,2,1,0,0,0]
]

def cert0144n : CertifiedBoard :=
  ⟨seed0144, by apply FastValid.valid; decide +kernel⟩

def cert0144r : CertifiedBoard :=
  ⟨seed0144.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0145 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,1,0,0,2,1,0,1,1,2,0],
  [0,2,2,0,0,0,2,1,1,0,1,1,1,1,0],
  [1,0,2,2,1,0,0,1,2,2,0,1,2,1,2,0,2],
  [2,0,1,1,0,2,1,2,0,2,0,2,0,0,2,0,1,0,0]
]

def cert0145n : CertifiedBoard :=
  ⟨seed0145, by apply FastValid.valid; decide +kernel⟩

def cert0145r : CertifiedBoard :=
  ⟨seed0145.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0146 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,1,0,0,2,1,0,1,2,0,2],
  [2,2,0,1,1,1,0,1,1,0,0,0,2,1,1],
  [1,1,1,0,2,1,2,1,2,0,2,0,0,2,2,0,0],
  [0,2,0,1,2,0,1,1,2,2,1,0,0,1,0,2,0,2,2]
]

def cert0146n : CertifiedBoard :=
  ⟨seed0146, by apply FastValid.valid; decide +kernel⟩

def cert0146r : CertifiedBoard :=
  ⟨seed0146.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0147 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,1,1,0,0,2,0,1,1,1,0],
  [2,1,0,0,2,1,0,1,0,2,2,0,0,2,1],
  [2,1,1,1,0,2,1,2,0,2,0,2,0,0,1,2,1],
  [1,0,1,2,0,1,1,2,2,1,2,0,2,2,0,1,0,0,0]
]

def cert0147n : CertifiedBoard :=
  ⟨seed0147, by apply FastValid.valid; decide +kernel⟩

def cert0147r : CertifiedBoard :=
  ⟨seed0147.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0148 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,1,1,0,0,2,0,2,0,1,1],
  [2,1,0,2,1,2,0,1,0,1,1,2,0,0,0],
  [1,1,1,1,0,0,2,1,2,2,0,1,2,0,0,2,2],
  [2,2,0,2,1,0,0,1,2,1,1,0,1,0,2,0,2,2,1]
]

def cert0148n : CertifiedBoard :=
  ⟨seed0148, by apply FastValid.valid; decide +kernel⟩

def cert0148r : CertifiedBoard :=
  ⟨seed0148.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0149 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,1,1,0,0,2,1,1,1,0,1],
  [0,1,0,0,1,2,1,0,2,2,0,0,0,2,0],
  [2,0,1,0,1,1,1,2,2,0,1,2,0,2,2,1,2],
  [1,2,0,0,2,1,2,0,2,0,2,0,1,1,0,2,1,0,0]
]

def cert0149n : CertifiedBoard :=
  ⟨seed0149, by apply FastValid.valid; decide +kernel⟩

def cert0149r : CertifiedBoard :=
  ⟨seed0149.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0150 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,1,1,1,0,0,0,2,0,2,2],
  [1,2,0,2,2,0,1,0,0,1,0,1,1,1,2],
  [0,1,2,0,1,1,0,2,0,0,2,1,2,1,2,0,1],
  [2,2,0,2,1,0,0,2,1,1,0,1,2,2,1,0,2,0,0]
]

def cert0150n : CertifiedBoard :=
  ⟨seed0150, by apply FastValid.valid; decide +kernel⟩

def cert0150r : CertifiedBoard :=
  ⟨seed0150.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0151 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,1,1,1,0,0,0,2,2,1,1],
  [2,0,1,0,2,1,2,0,2,2,0,1,2,2,0],
  [1,1,2,0,0,2,1,0,1,1,1,0,1,0,2,0,0],
  [0,0,2,0,2,1,2,0,2,0,1,2,1,0,0,1,1,0,0]
]

def cert0151n : CertifiedBoard :=
  ⟨seed0151, by apply FastValid.valid; decide +kernel⟩

def cert0151r : CertifiedBoard :=
  ⟨seed0151.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0152 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,1,1,1,0,0,2,2,1,1,1],
  [0,0,2,1,2,0,2,1,0,1,1,2,1,0,0],
  [1,1,0,2,1,2,0,1,2,2,0,0,0,2,0,2,0],
  [2,0,1,2,0,1,0,2,2,0,2,0,0,1,0,1,1,0,0]
]

def cert0152n : CertifiedBoard :=
  ⟨seed0152, by apply FastValid.valid; decide +kernel⟩

def cert0152r : CertifiedBoard :=
  ⟨seed0152.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0153 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,1,1,1,0,0,2,2,1,1,1],
  [0,2,1,2,0,1,2,1,0,0,2,1,0,0,0],
  [1,1,0,1,0,2,2,0,2,0,1,1,2,2,0,0,2],
  [1,2,0,2,0,0,1,1,0,2,0,2,1,2,0,1,0,1,2]
]

def cert0153n : CertifiedBoard :=
  ⟨seed0153, by apply FastValid.valid; decide +kernel⟩

def cert0153r : CertifiedBoard :=
  ⟨seed0153.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0154 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,1,1,1,0,0,2,2,1,1,1],
  [1,2,0,0,2,0,2,1,0,0,2,0,1,0,0],
  [2,1,2,0,1,1,0,2,1,0,1,0,2,2,0,2,1],
  [1,1,2,0,2,0,0,0,1,2,1,2,2,0,1,1,0,1,2]
]

def cert0154n : CertifiedBoard :=
  ⟨seed0154, by apply FastValid.valid; decide +kernel⟩

def cert0154r : CertifiedBoard :=
  ⟨seed0154.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0155 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,1,1,1,0,1,0,2,1,1,2],
  [0,2,1,0,1,2,1,0,2,0,1,2,2,0,2],
  [0,1,0,0,2,0,2,0,1,1,1,0,0,2,2,0,1],
  [1,2,0,0,2,2,1,2,0,2,1,2,0,0,1,1,0,0,0]
]

def cert0155n : CertifiedBoard :=
  ⟨seed0155, by apply FastValid.valid; decide +kernel⟩

def cert0155r : CertifiedBoard :=
  ⟨seed0155.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0156 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,1,1,1,0,1,0,2,2,1,1],
  [1,1,0,0,2,1,2,2,0,1,1,1,2,1,0],
  [1,0,0,2,1,2,0,2,0,2,2,0,0,0,2,0,0],
  [0,1,2,0,1,2,0,1,0,0,1,1,0,2,0,2,1,0,1]
]

def cert0156n : CertifiedBoard :=
  ⟨seed0156, by apply FastValid.valid; decide +kernel⟩

def cert0156r : CertifiedBoard :=
  ⟨seed0156.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0157 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,1,1,1,0,1,2,0,2,2,1],
  [2,1,0,0,2,1,2,2,0,0,2,1,1,0,0],
  [1,0,0,2,0,2,0,1,1,2,0,1,2,1,0,1,0],
  [0,0,0,1,1,1,0,2,2,0,2,1,2,0,1,0,2,0,0]
]

def cert0157n : CertifiedBoard :=
  ⟨seed0157, by apply FastValid.valid; decide +kernel⟩

def cert0157r : CertifiedBoard :=
  ⟨seed0157.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0158 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,1,1,1,0,2,0,2,1,1,2],
  [1,0,2,1,2,0,0,0,1,2,0,1,2,2,1],
  [1,2,1,0,1,0,0,2,0,0,2,2,0,1,1,0,0],
  [2,1,2,0,2,2,0,1,1,1,0,0,2,0,2,1,0,1,0]
]

def cert0158n : CertifiedBoard :=
  ⟨seed0158, by apply FastValid.valid; decide +kernel⟩

def cert0158r : CertifiedBoard :=
  ⟨seed0158.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0159 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,1,1,1,0,2,1,1,0,1,1],
  [2,0,0,2,2,0,0,0,1,2,1,2,0,2,0],
  [1,1,1,0,0,2,2,0,2,1,0,0,2,1,2,0,1],
  [0,1,2,0,1,0,2,0,2,0,1,0,1,1,2,2,1,0,0]
]

def cert0159n : CertifiedBoard :=
  ⟨seed0159, by apply FastValid.valid; decide +kernel⟩

def cert0159r : CertifiedBoard :=
  ⟨seed0159.map List.reverse, by apply FastValid.valid; decide +kernel⟩

end TBoards.Extended
