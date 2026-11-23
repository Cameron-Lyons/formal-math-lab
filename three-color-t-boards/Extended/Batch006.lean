import Extended.Batch002

/- Generated from extended_seeds.json. Published seeds 0–4:
   Qiyuan Ma, DOI 10.5281/zenodo.23631079, CC-BY-4.0. -/

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.Extended

def seed0192 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,1,2,1,0,2,0,2,1,1,0],
  [1,0,2,2,0,2,0,1,0,0,1,2,2,0,0],
  [1,0,0,2,2,1,0,1,1,1,0,1,1,2,0,2,1],
  [2,1,2,0,1,1,1,0,0,0,2,1,2,0,0,2,0,1,0]
]

def cert0192n : CertifiedBoard :=
  ⟨seed0192, by apply FastValid.valid; decide +kernel⟩

def cert0192r : CertifiedBoard :=
  ⟨seed0192.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0193 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,1,2,1,0,2,0,2,2,1,1],
  [0,2,0,2,1,2,0,1,0,0,1,1,2,0,0],
  [1,1,0,1,1,1,1,0,0,0,2,2,0,2,1,0,2],
  [0,1,1,0,1,0,0,2,1,2,0,0,2,0,1,2,2,0,1]
]

def cert0193n : CertifiedBoard :=
  ⟨seed0193, by apply FastValid.valid; decide +kernel⟩

def cert0193r : CertifiedBoard :=
  ⟨seed0193.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0194 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,1,2,1,0,2,0,2,2,1,1],
  [1,1,0,0,1,1,1,0,2,0,1,2,0,0,0],
  [2,2,0,1,0,1,0,0,2,0,1,1,1,2,0,2,2],
  [1,1,0,0,2,1,2,2,0,0,2,1,2,0,2,1,0,1,1]
]

def cert0194n : CertifiedBoard :=
  ⟨seed0194, by apply FastValid.valid; decide +kernel⟩

def cert0194r : CertifiedBoard :=
  ⟨seed0194.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0195 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,1,2,1,0,2,1,1,1,0,0],
  [2,1,0,0,1,1,2,2,0,1,0,0,0,2,1],
  [0,2,0,1,0,2,0,2,2,1,2,0,2,0,1,1,1],
  [1,1,0,1,1,0,1,2,0,2,1,2,0,0,2,2,0,0,2]
]

def cert0195n : CertifiedBoard :=
  ⟨seed0195, by apply FastValid.valid; decide +kernel⟩

def cert0195r : CertifiedBoard :=
  ⟨seed0195.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0196 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,1,2,1,0,2,1,1,1,2,0],
  [2,0,1,0,1,0,0,2,2,1,2,0,2,0,0],
  [0,2,1,2,2,0,1,1,0,1,1,1,0,0,2,1,0],
  [1,0,2,2,0,1,2,0,0,0,1,1,0,0,2,0,2,0,2]
]

def cert0196n : CertifiedBoard :=
  ⟨seed0196, by apply FastValid.valid; decide +kernel⟩

def cert0196r : CertifiedBoard :=
  ⟨seed0196.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0197 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,1,2,1,0,2,1,1,1,2,0],
  [2,0,2,1,2,2,1,2,0,2,0,0,0,2,0],
  [1,0,0,1,1,0,1,2,0,1,1,0,1,0,2,1,0],
  [2,0,2,2,0,1,0,0,2,0,1,1,1,0,0,2,2,0,0]
]

def cert0197n : CertifiedBoard :=
  ⟨seed0197, by apply FastValid.valid; decide +kernel⟩

def cert0197r : CertifiedBoard :=
  ⟨seed0197.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0198 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,1,2,1,2,0,0,2,0,2,2],
  [0,0,2,0,1,1,1,1,0,2,1,1,0,1,2],
  [1,2,0,2,1,2,0,2,1,0,1,1,0,0,1,0,0],
  [2,2,0,1,1,2,2,1,0,2,0,0,0,2,2,0,1,0,0]
]

def cert0198n : CertifiedBoard :=
  ⟨seed0198, by apply FastValid.valid; decide +kernel⟩

def cert0198r : CertifiedBoard :=
  ⟨seed0198.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0199 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,1,2,1,2,0,0,2,1,1,1],
  [1,1,0,1,1,0,1,1,0,2,2,1,0,0,0],
  [2,0,1,0,0,2,1,2,0,2,0,2,2,0,2,1,0],
  [1,0,0,2,0,0,1,1,1,2,0,1,0,2,0,1,2,2,0]
]

def cert0199n : CertifiedBoard :=
  ⟨seed0199, by apply FastValid.valid; decide +kernel⟩

def cert0199r : CertifiedBoard :=
  ⟨seed0199.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0200 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,1,2,1,2,0,1,1,1,0,1],
  [0,1,0,1,1,1,2,2,1,2,0,0,0,1,0],
  [1,0,2,0,0,2,1,0,2,0,2,2,0,2,2,0,1],
  [0,1,1,0,0,2,1,1,0,0,2,0,1,2,0,2,1,0,0]
]

def cert0200n : CertifiedBoard :=
  ⟨seed0200, by apply FastValid.valid; decide +kernel⟩

def cert0200r : CertifiedBoard :=
  ⟨seed0200.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0201 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,1,2,1,2,0,1,1,1,0,1],
  [0,1,0,1,1,1,2,2,1,2,0,0,2,1,0],
  [2,0,2,0,1,1,0,0,2,2,0,2,2,0,1,0,0],
  [1,0,0,1,2,0,2,1,0,2,1,1,0,2,0,0,0,2,0]
]

def cert0201n : CertifiedBoard :=
  ⟨seed0201, by apply FastValid.valid; decide +kernel⟩

def cert0201r : CertifiedBoard :=
  ⟨seed0201.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0202 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,1,2,1,2,0,2,0,2,2,1],
  [0,1,0,1,1,0,1,1,1,0,0,2,1,1,1],
  [2,1,2,0,2,1,0,0,0,2,0,0,1,2,2,0,0],
  [1,1,0,0,2,0,1,0,2,1,0,2,2,0,1,1,2,0,1]
]

def cert0202n : CertifiedBoard :=
  ⟨seed0202, by apply FastValid.valid; decide +kernel⟩

def cert0202r : CertifiedBoard :=
  ⟨seed0202.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0203 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,1,2,1,2,0,2,0,2,2,1],
  [2,1,0,0,1,1,1,1,0,1,1,0,0,2,1],
  [2,1,1,0,2,1,0,0,0,2,2,0,0,2,0,1,0],
  [1,0,2,0,1,1,2,2,0,1,0,1,2,0,2,1,2,0,0]
]

def cert0203n : CertifiedBoard :=
  ⟨seed0203, by apply FastValid.valid; decide +kernel⟩

def cert0203r : CertifiedBoard :=
  ⟨seed0203.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0204 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,1,2,1,2,0,2,0,2,2,1],
  [2,1,0,0,1,1,1,1,0,1,1,0,0,2,1],
  [2,1,1,0,2,2,0,0,0,2,1,0,0,2,0,1,0],
  [1,0,2,0,1,0,1,2,0,1,1,2,2,0,2,1,2,0,0]
]

def cert0204n : CertifiedBoard :=
  ⟨seed0204, by apply FastValid.valid; decide +kernel⟩

def cert0204r : CertifiedBoard :=
  ⟨seed0204.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0205 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,1,2,1,2,0,2,0,2,2,1],
  [2,2,0,1,1,1,1,0,1,0,0,1,1,2,0],
  [2,0,1,2,0,0,2,1,0,1,0,2,0,1,1,0,0],
  [2,1,1,0,0,2,1,0,2,0,0,0,2,1,2,2,0,2,2]
]

def cert0205n : CertifiedBoard :=
  ⟨seed0205, by apply FastValid.valid; decide +kernel⟩

def cert0205r : CertifiedBoard :=
  ⟨seed0205.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0206 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,1,2,1,2,0,2,1,1,0,1],
  [0,1,0,1,1,1,2,2,1,0,0,2,0,1,1],
  [2,1,2,0,2,1,0,0,2,2,0,0,1,2,0,0,0],
  [1,1,1,0,2,0,1,0,0,2,0,2,2,0,1,1,0,2,1]
]

def cert0206n : CertifiedBoard :=
  ⟨seed0206, by apply FastValid.valid; decide +kernel⟩

def cert0206r : CertifiedBoard :=
  ⟨seed0206.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0207 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,1,2,1,2,0,2,2,1,1,0],
  [1,0,2,1,2,0,1,1,2,0,2,0,1,0,0],
  [2,1,0,1,1,0,1,0,0,2,1,0,2,2,0,0,1],
  [0,1,2,2,0,0,0,2,0,1,1,1,1,0,0,2,0,2,1]
]

def cert0207n : CertifiedBoard :=
  ⟨seed0207, by apply FastValid.valid; decide +kernel⟩

def cert0207r : CertifiedBoard :=
  ⟨seed0207.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0208 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,1,2,1,2,0,2,2,1,1,1],
  [2,0,0,2,1,0,2,0,1,0,1,2,2,0,1],
  [1,1,0,1,1,2,0,2,1,0,0,1,0,0,2,0,0],
  [0,1,1,0,0,0,2,0,1,1,1,0,2,1,2,0,2,2,0]
]

def cert0208n : CertifiedBoard :=
  ⟨seed0208, by apply FastValid.valid; decide +kernel⟩

def cert0208r : CertifiedBoard :=
  ⟨seed0208.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0209 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,1,2,2,0,1,0,0,2,1,1],
  [2,0,2,0,1,1,0,2,1,0,2,2,1,2,0],
  [1,1,1,0,1,0,0,0,1,1,0,1,2,0,2,2,0],
  [2,0,0,2,1,2,1,0,0,2,0,1,1,1,2,0,2,0,0]
]

def cert0209n : CertifiedBoard :=
  ⟨seed0209, by apply FastValid.valid; decide +kernel⟩

def cert0209r : CertifiedBoard :=
  ⟨seed0209.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0210 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,1,2,2,0,1,0,1,1,0,0],
  [2,1,0,1,0,0,2,2,0,0,1,1,0,0,2],
  [0,1,2,1,2,0,1,1,1,2,0,2,1,0,2,2,1],
  [0,2,0,2,1,2,0,0,0,2,0,2,1,1,1,0,2,0,1]
]

def cert0210n : CertifiedBoard :=
  ⟨seed0210, by apply FastValid.valid; decide +kernel⟩

def cert0210r : CertifiedBoard :=
  ⟨seed0210.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0211 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,1,2,2,0,1,0,1,1,1,0],
  [0,2,2,0,2,1,1,2,0,1,1,1,0,0,2],
  [1,0,2,2,1,2,0,0,0,2,1,2,1,0,1,0,0],
  [0,1,1,0,2,0,2,1,0,0,1,2,0,2,0,0,2,0,1]
]

def cert0211n : CertifiedBoard :=
  ⟨seed0211, by apply FastValid.valid; decide +kernel⟩

def cert0211r : CertifiedBoard :=
  ⟨seed0211.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0212 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,1,2,2,0,1,0,1,1,2,0],
  [2,0,0,1,1,1,1,0,2,0,1,1,0,2,1],
  [0,1,2,0,2,1,2,0,2,2,1,0,0,0,2,0,1],
  [2,1,2,1,1,0,0,2,2,0,2,1,0,1,0,0,2,0,0]
]

def cert0212n : CertifiedBoard :=
  ⟨seed0212, by apply FastValid.valid; decide +kernel⟩

def cert0212r : CertifiedBoard :=
  ⟨seed0212.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0213 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,1,2,2,0,1,0,2,2,1,1],
  [2,2,0,1,1,1,2,0,0,2,0,2,0,0,0],
  [1,1,1,0,1,1,0,0,2,1,0,0,1,1,0,2,2],
  [1,2,0,2,1,2,1,0,0,2,1,2,0,2,0,1,0,1,2]
]

def cert0213n : CertifiedBoard :=
  ⟨seed0213, by apply FastValid.valid; decide +kernel⟩

def cert0213r : CertifiedBoard :=
  ⟨seed0213.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0214 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,1,2,2,0,1,0,2,2,1,1],
  [2,2,0,1,1,1,2,0,0,2,0,2,0,0,0],
  [1,1,1,0,1,1,0,0,2,1,0,0,1,1,0,2,2],
  [1,2,0,2,1,2,1,2,0,2,1,0,0,2,0,1,0,1,2]
]

def cert0214n : CertifiedBoard :=
  ⟨seed0214, by apply FastValid.valid; decide +kernel⟩

def cert0214r : CertifiedBoard :=
  ⟨seed0214.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0215 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,1,2,2,0,1,1,0,1,1,2],
  [1,0,1,0,0,0,2,2,0,0,2,0,2,1,1],
  [1,2,1,0,0,1,1,0,2,0,2,2,1,2,0,1,0],
  [1,1,1,1,0,2,1,2,0,1,2,0,2,1,0,0,2,0,0]
]

def cert0215n : CertifiedBoard :=
  ⟨seed0215, by apply FastValid.valid; decide +kernel⟩

def cert0215r : CertifiedBoard :=
  ⟨seed0215.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0216 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,1,2,2,0,1,1,0,1,2,0],
  [0,1,1,0,2,0,2,1,2,1,2,0,2,0,1],
  [0,2,0,1,0,0,2,1,1,1,1,0,2,2,1,0,0],
  [2,0,2,2,0,0,1,0,0,0,2,1,0,1,1,2,0,0,2]
]

def cert0216n : CertifiedBoard :=
  ⟨seed0216, by apply FastValid.valid; decide +kernel⟩

def cert0216r : CertifiedBoard :=
  ⟨seed0216.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0217 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,1,2,2,0,1,1,1,2,0,2],
  [0,2,0,1,1,0,2,2,0,1,0,0,2,2,1],
  [2,1,0,0,2,1,0,1,1,0,0,0,1,0,1,2,1],
  [2,1,1,1,0,2,1,2,0,2,0,2,1,2,0,0,2,0,0]
]

def cert0217n : CertifiedBoard :=
  ⟨seed0217, by apply FastValid.valid; decide +kernel⟩

def cert0217r : CertifiedBoard :=
  ⟨seed0217.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0218 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,1,2,2,0,2,0,1,1,2,0],
  [0,1,0,0,1,0,0,2,2,1,2,0,2,0,1],
  [0,1,1,0,2,1,2,0,2,1,1,1,1,0,2,0,1],
  [2,0,0,2,1,0,1,1,0,1,2,1,0,0,0,2,2,0,0]
]

def cert0218n : CertifiedBoard :=
  ⟨seed0218, by apply FastValid.valid; decide +kernel⟩

def cert0218r : CertifiedBoard :=
  ⟨seed0218.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0219 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,1,2,2,0,2,1,1,0,2,0],
  [2,0,2,2,0,2,2,1,0,1,1,1,0,0,1],
  [2,0,1,1,2,0,1,1,1,0,2,0,1,0,1,0,0],
  [0,1,2,0,0,2,1,2,1,2,0,0,2,1,0,0,0,2,0]
]

def cert0219n : CertifiedBoard :=
  ⟨seed0219, by apply FastValid.valid; decide +kernel⟩

def cert0219r : CertifiedBoard :=
  ⟨seed0219.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0220 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,1,2,2,0,2,1,1,0,2,1],
  [0,1,0,0,1,0,0,2,2,1,2,1,2,0,1],
  [2,1,0,0,2,1,0,2,0,1,1,0,1,1,2,0,0],
  [1,1,1,1,0,1,2,0,2,2,0,2,0,0,0,2,0,1,1]
]

def cert0220n : CertifiedBoard :=
  ⟨seed0220, by apply FastValid.valid; decide +kernel⟩

def cert0220r : CertifiedBoard :=
  ⟨seed0220.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0221 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,1,2,2,0,2,1,1,0,2,1],
  [1,0,0,1,1,1,2,0,1,2,1,2,0,1,1],
  [2,1,0,1,0,0,0,2,2,0,2,0,0,2,0,1,0],
  [1,1,1,0,2,0,2,1,0,1,1,0,0,2,2,1,2,0,0]
]

def cert0221n : CertifiedBoard :=
  ⟨seed0221, by apply FastValid.valid; decide +kernel⟩

def cert0221r : CertifiedBoard :=
  ⟨seed0221.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0222 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,1,2,2,0,2,1,1,1,0,0],
  [1,0,2,2,0,1,1,2,0,1,1,1,0,1,0],
  [1,2,0,2,2,1,0,0,0,2,1,2,1,0,0,2,0],
  [2,0,2,0,1,2,0,0,1,1,0,1,0,2,0,0,2,1,2]
]

def cert0222n : CertifiedBoard :=
  ⟨seed0222, by apply FastValid.valid; decide +kernel⟩

def cert0222r : CertifiedBoard :=
  ⟨seed0222.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0223 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,1,2,2,0,2,1,1,1,2,0],
  [0,1,0,1,1,1,0,2,2,1,2,0,2,0,0],
  [2,0,1,0,2,0,1,1,0,1,1,0,0,1,2,0,2],
  [0,2,2,0,0,2,1,2,1,0,0,0,2,1,0,0,2,0,1]
]

def cert0223n : CertifiedBoard :=
  ⟨seed0223, by apply FastValid.valid; decide +kernel⟩

def cert0223r : CertifiedBoard :=
  ⟨seed0223.map List.reverse, by apply FastValid.valid; decide +kernel⟩

end TBoards.Extended
