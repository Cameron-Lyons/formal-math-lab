import Extended.Batch003

/- Generated from extended_seeds.json. Published seeds 0–4:
   Qiyuan Ma, DOI 10.5281/zenodo.23631079, CC-BY-4.0. -/

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.Extended

def seed0224 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,2,0,0,0,1,0,2,2,1,1],
  [2,2,0,2,0,1,0,0,1,2,0,2,1,2,2],
  [1,1,2,0,1,1,0,0,2,1,0,1,1,1,1,0,0],
  [2,2,0,2,0,0,2,1,0,1,2,1,2,0,1,1,0,2,2]
]

def cert0224n : CertifiedBoard :=
  ⟨seed0224, by apply FastValid.valid; decide +kernel⟩

def cert0224r : CertifiedBoard :=
  ⟨seed0224.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0225 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,2,0,0,0,1,1,1,0,2,2],
  [1,1,0,2,0,1,0,0,2,1,2,0,1,2,0],
  [2,2,0,2,2,1,2,1,0,1,1,0,0,1,0,1,1],
  [2,0,2,0,2,1,1,1,2,2,0,1,2,0,0,2,1,0,0]
]

def cert0225n : CertifiedBoard :=
  ⟨seed0225, by apply FastValid.valid; decide +kernel⟩

def cert0225r : CertifiedBoard :=
  ⟨seed0225.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0226 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,2,0,0,0,1,1,2,0,1,1],
  [1,0,2,0,2,2,0,0,2,1,0,0,1,2,1],
  [2,1,2,0,2,2,1,1,0,1,2,0,1,1,1,0,0],
  [1,1,1,0,1,0,2,0,1,0,0,2,1,2,2,0,2,1,0]
]

def cert0226n : CertifiedBoard :=
  ⟨seed0226, by apply FastValid.valid; decide +kernel⟩

def cert0226r : CertifiedBoard :=
  ⟨seed0226.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0227 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,2,0,0,0,1,1,2,0,2,1],
  [2,1,0,1,0,1,1,0,2,1,0,2,2,1,2],
  [0,1,2,1,2,0,1,0,0,2,0,2,1,1,1,0,0],
  [1,2,0,1,1,1,0,0,2,0,2,2,0,1,2,2,0,0,1]
]

def cert0227n : CertifiedBoard :=
  ⟨seed0227, by apply FastValid.valid; decide +kernel⟩

def cert0227r : CertifiedBoard :=
  ⟨seed0227.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0228 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,2,0,0,0,1,2,0,1,1,2],
  [1,0,0,2,1,1,0,1,1,1,0,2,1,0,0],
  [1,2,0,2,2,1,2,2,0,1,0,0,1,2,1,2,0],
  [2,0,2,1,0,2,2,0,2,0,0,2,0,1,1,1,0,1,0]
]

def cert0228n : CertifiedBoard :=
  ⟨seed0228, by apply FastValid.valid; decide +kernel⟩

def cert0228r : CertifiedBoard :=
  ⟨seed0228.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0229 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,2,0,0,2,0,2,2,1,1,1],
  [1,0,2,2,0,2,0,1,1,0,0,1,2,1,2],
  [1,1,0,1,2,0,2,1,0,0,0,2,1,0,1,1,0],
  [1,2,0,1,1,1,2,0,1,0,0,1,0,2,1,2,2,0,0]
]

def cert0229n : CertifiedBoard :=
  ⟨seed0229, by apply FastValid.valid; decide +kernel⟩

def cert0229r : CertifiedBoard :=
  ⟨seed0229.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0230 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,2,0,0,2,1,2,0,2,2,1],
  [2,1,0,0,2,0,2,1,1,1,0,1,1,2,1],
  [1,0,0,0,1,0,2,0,1,2,2,0,1,1,0,1,0],
  [2,1,0,2,2,0,1,1,1,0,0,1,2,0,2,1,2,0,0]
]

def cert0230n : CertifiedBoard :=
  ⟨seed0230, by apply FastValid.valid; decide +kernel⟩

def cert0230r : CertifiedBoard :=
  ⟨seed0230.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0231 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,2,0,1,0,0,2,2,1,1,1],
  [1,1,0,0,1,2,0,2,0,1,1,2,0,0,0],
  [0,1,1,0,1,1,1,0,2,1,2,2,0,2,2,0,2],
  [0,2,1,0,0,2,1,2,1,0,1,2,0,1,0,2,0,0,1]
]

def cert0231n : CertifiedBoard :=
  ⟨seed0231, by apply FastValid.valid; decide +kernel⟩

def cert0231r : CertifiedBoard :=
  ⟨seed0231.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0232 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,2,0,1,0,1,1,1,2,0,2],
  [2,1,0,0,2,1,2,0,1,2,1,0,2,0,1],
  [0,2,2,0,0,1,1,1,0,2,1,1,0,1,2,0,0],
  [0,1,0,0,1,1,0,0,0,2,2,1,2,2,0,2,0,2,1]
]

def cert0232n : CertifiedBoard :=
  ⟨seed0232, by apply FastValid.valid; decide +kernel⟩

def cert0232r : CertifiedBoard :=
  ⟨seed0232.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0233 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,2,0,1,1,1,0,2,0,1,1],
  [1,1,0,2,0,2,1,2,0,2,2,1,2,2,0],
  [0,2,1,0,0,1,0,1,0,0,2,1,1,1,2,0,0],
  [2,0,1,2,1,0,1,2,0,0,1,1,0,0,0,2,2,0,2]
]

def cert0233n : CertifiedBoard :=
  ⟨seed0233, by apply FastValid.valid; decide +kernel⟩

def cert0233r : CertifiedBoard :=
  ⟨seed0233.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0234 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,2,0,1,1,1,0,2,1,1,0],
  [1,0,0,2,2,1,2,1,0,0,1,2,2,0,0],
  [0,2,1,0,1,1,2,0,1,0,2,1,2,0,2,0,1],
  [0,1,0,1,2,0,0,0,1,1,1,0,0,2,0,2,2,0,2]
]

def cert0234n : CertifiedBoard :=
  ⟨seed0234, by apply FastValid.valid; decide +kernel⟩

def cert0234r : CertifiedBoard :=
  ⟨seed0234.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0235 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,2,0,1,1,1,1,0,0,1,1],
  [1,1,0,0,2,0,1,2,2,0,2,1,0,0,0],
  [1,2,1,2,0,2,1,2,0,2,2,0,1,0,1,0,2],
  [0,2,1,1,0,2,2,1,0,1,1,2,0,0,2,0,0,1,2]
]

def cert0235n : CertifiedBoard :=
  ⟨seed0235, by apply FastValid.valid; decide +kernel⟩

def cert0235r : CertifiedBoard :=
  ⟨seed0235.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0236 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,2,0,1,1,1,1,0,0,1,1],
  [2,0,1,0,2,1,2,2,0,0,0,1,1,0,0],
  [1,1,2,0,2,2,1,2,0,2,1,0,1,2,0,0,2],
  [0,2,1,0,2,0,1,2,1,1,0,1,0,0,2,2,0,2,0]
]

def cert0236n : CertifiedBoard :=
  ⟨seed0236, by apply FastValid.valid; decide +kernel⟩

def cert0236r : CertifiedBoard :=
  ⟨seed0236.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0237 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,2,0,1,1,1,1,0,1,1,2],
  [0,0,1,0,2,0,1,2,1,2,2,0,2,1,1],
  [1,2,0,0,2,2,1,0,0,1,0,2,1,2,0,0,0],
  [1,1,0,0,2,0,2,2,0,2,1,0,1,2,0,1,1,0,0]
]

def cert0237n : CertifiedBoard :=
  ⟨seed0237, by apply FastValid.valid; decide +kernel⟩

def cert0237r : CertifiedBoard :=
  ⟨seed0237.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0238 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,2,0,1,1,1,1,0,2,2,1],
  [0,2,2,0,2,1,2,1,0,0,2,0,2,0,0],
  [2,1,0,0,1,1,2,0,1,0,2,1,1,0,1,0,1],
  [0,1,1,0,0,2,1,2,0,0,0,1,2,2,0,1,2,0,2]
]

def cert0238n : CertifiedBoard :=
  ⟨seed0238, by apply FastValid.valid; decide +kernel⟩

def cert0238r : CertifiedBoard :=
  ⟨seed0238.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0239 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,2,0,1,1,1,1,2,0,2,2],
  [2,1,0,0,2,1,2,0,0,0,2,0,0,1,1],
  [2,2,1,2,0,1,2,1,1,0,1,0,0,1,1,0,0],
  [1,1,0,1,0,2,2,0,1,2,2,0,2,0,2,1,0,2,1]
]

def cert0239n : CertifiedBoard :=
  ⟨seed0239, by apply FastValid.valid; decide +kernel⟩

def cert0239r : CertifiedBoard :=
  ⟨seed0239.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0240 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,2,0,1,1,2,0,2,1,1,0],
  [0,2,1,0,1,1,0,0,0,1,1,1,1,0,0],
  [1,0,2,2,0,1,2,2,0,2,0,2,1,2,1,2,0],
  [2,0,0,1,2,0,0,2,0,1,0,2,2,1,0,1,0,0,2]
]

def cert0240n : CertifiedBoard :=
  ⟨seed0240, by apply FastValid.valid; decide +kernel⟩

def cert0240r : CertifiedBoard :=
  ⟨seed0240.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0241 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,2,0,1,1,2,0,2,2,1,1],
  [1,2,0,0,2,1,2,1,0,0,1,1,0,0,0],
  [1,1,1,1,0,0,1,2,0,2,2,0,0,2,1,0,2],
  [0,2,1,2,2,0,1,1,0,1,0,2,0,2,0,1,0,1,2]
]

def cert0241n : CertifiedBoard :=
  ⟨seed0241, by apply FastValid.valid; decide +kernel⟩

def cert0241r : CertifiedBoard :=
  ⟨seed0241.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0242 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,2,0,1,1,2,2,1,1,0,0],
  [1,0,2,2,0,1,1,1,0,2,2,0,0,2,1],
  [2,1,0,1,1,1,0,0,2,1,2,0,2,0,0,1,0],
  [0,1,2,0,1,2,1,2,0,2,0,2,1,0,1,0,0,0,1]
]

def cert0242n : CertifiedBoard :=
  ⟨seed0242, by apply FastValid.valid; decide +kernel⟩

def cert0242r : CertifiedBoard :=
  ⟨seed0242.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0243 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,2,0,1,1,2,2,1,1,0,0],
  [2,0,0,1,0,2,2,0,2,0,1,2,1,0,2],
  [0,2,2,0,1,0,0,1,1,0,1,1,1,1,0,1,2],
  [1,2,0,2,1,2,0,2,0,0,0,2,1,0,0,2,1,2,0]
]

def cert0243n : CertifiedBoard :=
  ⟨seed0243, by apply FastValid.valid; decide +kernel⟩

def cert0243r : CertifiedBoard :=
  ⟨seed0243.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0244 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,2,0,1,1,2,2,1,1,1,0],
  [1,0,0,1,0,2,1,2,0,2,0,0,0,2,2],
  [1,1,1,0,1,0,2,1,0,0,2,2,0,2,0,1,1],
  [2,2,0,2,1,2,1,0,1,2,0,1,2,0,0,1,1,0,0]
]

def cert0244n : CertifiedBoard :=
  ⟨seed0244, by apply FastValid.valid; decide +kernel⟩

def cert0244r : CertifiedBoard :=
  ⟨seed0244.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0245 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,2,0,1,2,0,0,1,1,0,1],
  [0,1,1,0,2,1,2,2,1,0,1,1,0,0,0],
  [0,2,2,0,2,1,1,1,1,2,0,2,1,2,0,0,2],
  [0,2,0,2,0,1,2,1,0,0,2,2,0,1,0,0,1,0,2]
]

def cert0245n : CertifiedBoard :=
  ⟨seed0245, by apply FastValid.valid; decide +kernel⟩

def cert0245r : CertifiedBoard :=
  ⟨seed0245.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0246 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,2,0,2,1,1,0,1,1,0,0],
  [0,2,2,0,0,1,1,2,0,0,1,2,1,0,2],
  [2,1,2,0,1,0,1,1,1,1,0,0,2,2,0,2,1],
  [2,2,1,0,2,1,2,0,1,0,0,0,2,0,2,0,1,2,2]
]

def cert0246n : CertifiedBoard :=
  ⟨seed0246, by apply FastValid.valid; decide +kernel⟩

def cert0246r : CertifiedBoard :=
  ⟨seed0246.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0247 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,2,0,2,1,1,1,1,0,1,1],
  [1,1,0,1,0,0,2,2,0,1,2,1,0,0,0],
  [0,1,1,0,0,2,2,0,2,1,2,2,1,0,2,0,2],
  [0,2,1,2,0,1,1,2,0,0,1,0,2,0,0,1,2,0,1]
]

def cert0247n : CertifiedBoard :=
  ⟨seed0247, by apply FastValid.valid; decide +kernel⟩

def cert0247r : CertifiedBoard :=
  ⟨seed0247.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0248 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,2,0,2,1,1,1,2,0,1,1],
  [1,1,0,1,0,0,2,1,2,1,0,2,0,0,0],
  [2,0,1,0,0,2,1,0,1,1,1,0,2,2,0,2,2],
  [2,2,1,2,0,1,1,0,0,1,2,2,0,0,1,2,0,2,0]
]

def cert0248n : CertifiedBoard :=
  ⟨seed0248, by apply FastValid.valid; decide +kernel⟩

def cert0248r : CertifiedBoard :=
  ⟨seed0248.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0249 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,2,1,0,0,1,0,1,1,0,0],
  [1,1,0,0,1,2,1,2,0,2,0,0,0,2,1],
  [2,1,2,2,0,0,2,2,0,2,2,1,0,1,1,1,1],
  [2,0,1,1,2,0,1,0,2,0,2,1,1,0,2,0,1,2,0]
]

def cert0249n : CertifiedBoard :=
  ⟨seed0249, by apply FastValid.valid; decide +kernel⟩

def cert0249r : CertifiedBoard :=
  ⟨seed0249.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0250 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,2,1,0,0,1,0,1,1,0,0],
  [2,0,0,2,1,1,1,0,0,0,1,2,1,2,0],
  [2,2,1,0,2,1,2,2,0,1,0,1,1,1,0,2,2],
  [0,1,2,0,1,1,2,0,2,2,0,2,0,0,2,0,2,0,1]
]

def cert0250n : CertifiedBoard :=
  ⟨seed0250, by apply FastValid.valid; decide +kernel⟩

def cert0250r : CertifiedBoard :=
  ⟨seed0250.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0251 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,2,1,0,0,1,0,2,2,1,1],
  [1,1,0,1,1,2,1,0,0,0,1,1,1,1,0],
  [2,0,0,2,2,0,1,2,2,0,2,1,2,0,2,0,0],
  [1,0,0,2,0,2,0,1,2,0,1,0,1,1,0,2,1,2,0]
]

def cert0251n : CertifiedBoard :=
  ⟨seed0251, by apply FastValid.valid; decide +kernel⟩

def cert0251r : CertifiedBoard :=
  ⟨seed0251.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0252 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,2,1,0,0,1,1,2,0,1,1],
  [2,1,0,1,0,1,0,2,1,2,2,1,2,0,0],
  [0,2,0,2,2,0,0,0,1,2,1,1,1,1,0,0,2],
  [1,1,0,2,0,2,2,0,1,1,0,0,2,0,1,2,0,2,1]
]

def cert0252n : CertifiedBoard :=
  ⟨seed0252, by apply FastValid.valid; decide +kernel⟩

def cert0252r : CertifiedBoard :=
  ⟨seed0252.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0253 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,2,1,2,0,1,1,0,2,1,1],
  [1,0,2,0,1,1,1,1,0,0,0,2,2,0,1],
  [1,1,0,1,2,0,2,0,0,2,2,0,2,0,2,1,0],
  [0,1,2,1,2,2,1,0,0,1,1,2,0,0,1,0,1,0,0]
]

def cert0253n : CertifiedBoard :=
  ⟨seed0253, by apply FastValid.valid; decide +kernel⟩

def cert0253r : CertifiedBoard :=
  ⟨seed0253.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0254 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,2,1,2,0,1,1,2,0,2,2],
  [1,0,2,0,1,2,2,1,2,1,0,1,1,0,0],
  [2,2,0,2,0,0,0,1,1,1,1,0,1,0,0,1,0],
  [0,2,1,1,0,2,1,0,0,2,0,1,2,0,2,2,0,0,2]
]

def cert0254n : CertifiedBoard :=
  ⟨seed0254, by apply FastValid.valid; decide +kernel⟩

def cert0254r : CertifiedBoard :=
  ⟨seed0254.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0255 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,2,1,2,0,2,0,1,1,0,0],
  [0,2,0,2,1,1,1,1,0,2,2,0,0,1,0],
  [1,0,2,1,0,1,2,1,0,0,2,2,1,2,0,1,1],
  [1,1,0,0,1,0,1,1,2,2,0,1,2,0,2,0,0,0,2]
]

def cert0255n : CertifiedBoard :=
  ⟨seed0255, by apply FastValid.valid; decide +kernel⟩

def cert0255r : CertifiedBoard :=
  ⟨seed0255.map List.reverse, by apply FastValid.valid; decide +kernel⟩

end TBoards.Extended
