import Extended.Batch005

/- Generated from extended_seeds.json. Published seeds 0–4:
   Qiyuan Ma, DOI 10.5281/zenodo.23631079, CC-BY-4.0. -/

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.Extended

def seed0288 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,2,1,2,2,1,0,2,0,2,2],
  [1,0,2,2,0,1,1,0,0,2,1,1,0,1,1],
  [2,2,0,0,1,2,0,0,0,1,1,1,1,0,1,0,0],
  [1,1,2,0,2,0,2,1,0,0,2,0,1,2,1,2,0,1,0]
]

def cert0288n : CertifiedBoard :=
  ⟨seed0288, by apply FastValid.valid; decide +kernel⟩

def cert0288r : CertifiedBoard :=
  ⟨seed0288.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0289 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,2,1,2,2,1,0,2,1,1,0],
  [0,1,0,0,2,0,1,1,1,1,0,1,1,0,1],
  [2,1,2,0,2,0,2,2,0,2,0,0,1,2,1,0,0],
  [1,0,0,2,2,0,1,1,2,0,1,2,0,0,0,1,0,2,1]
]

def cert0289n : CertifiedBoard :=
  ⟨seed0289, by apply FastValid.valid; decide +kernel⟩

def cert0289r : CertifiedBoard :=
  ⟨seed0289.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0290 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,2,1,2,2,1,0,2,1,1,0],
  [1,0,2,1,0,1,1,1,2,1,2,0,2,0,0],
  [0,1,0,1,1,1,0,0,0,2,0,1,2,0,2,0,2],
  [0,2,2,0,1,2,0,0,1,0,0,1,1,0,0,2,2,0,1]
]

def cert0290n : CertifiedBoard :=
  ⟨seed0290, by apply FastValid.valid; decide +kernel⟩

def cert0290r : CertifiedBoard :=
  ⟨seed0290.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0291 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,2,1,2,2,1,0,2,1,1,1],
  [2,1,0,1,1,2,0,1,1,0,0,1,0,0,2],
  [0,2,2,0,1,1,1,0,2,0,2,2,0,0,1,0,0],
  [1,1,0,1,2,0,1,2,1,2,0,2,0,2,0,0,0,2,1]
]

def cert0291n : CertifiedBoard :=
  ⟨seed0291, by apply FastValid.valid; decide +kernel⟩

def cert0291r : CertifiedBoard :=
  ⟨seed0291.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0292 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,2,1,2,2,1,0,2,1,1,1],
  [2,2,0,0,1,2,0,1,1,1,0,1,0,0,0],
  [1,1,2,0,1,1,0,0,2,0,0,2,0,2,1,2,0],
  [2,0,1,1,0,1,2,1,0,0,1,0,2,0,2,2,0,2,2]
]

def cert0292n : CertifiedBoard :=
  ⟨seed0292, by apply FastValid.valid; decide +kernel⟩

def cert0292r : CertifiedBoard :=
  ⟨seed0292.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0293 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,2,1,2,2,1,0,2,1,1,2],
  [0,1,0,0,1,1,0,1,2,1,2,0,0,0,1],
  [1,2,0,2,0,1,2,0,2,0,1,1,0,2,1,0,0],
  [0,1,0,0,2,0,0,2,2,0,2,2,0,1,1,1,1,0,1]
]

def cert0293n : CertifiedBoard :=
  ⟨seed0293, by apply FastValid.valid; decide +kernel⟩

def cert0293r : CertifiedBoard :=
  ⟨seed0293.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0294 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,0,2,1,2,2,1,0,2,1,1,2],
  [2,0,1,0,0,1,1,1,0,0,1,1,1,0,0],
  [1,2,0,0,2,1,2,0,0,0,2,0,1,2,1,0,2],
  [0,2,0,2,2,0,1,0,1,1,0,1,2,0,2,2,0,2,0]
]

def cert0294n : CertifiedBoard :=
  ⟨seed0294, by apply FastValid.valid; decide +kernel⟩

def cert0294r : CertifiedBoard :=
  ⟨seed0294.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0295 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,1,0,0,0,0,2,0,2,2,1],
  [2,2,0,2,1,0,0,2,1,0,1,1,2,0,0],
  [2,1,1,0,2,1,2,0,0,2,0,1,1,1,1,0,1],
  [0,1,2,0,2,0,1,0,0,1,0,2,2,0,1,2,1,2,2]
]

def cert0295n : CertifiedBoard :=
  ⟨seed0295, by apply FastValid.valid; decide +kernel⟩

def cert0295r : CertifiedBoard :=
  ⟨seed0295.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0296 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,1,0,0,0,0,2,1,1,0,0],
  [1,0,0,2,1,2,0,2,0,0,2,0,2,1,2],
  [1,1,1,0,1,2,0,2,2,1,0,2,2,0,1,1,1],
  [1,2,2,0,0,1,0,1,0,2,0,1,1,2,0,1,2,1,0]
]

def cert0296n : CertifiedBoard :=
  ⟨seed0296, by apply FastValid.valid; decide +kernel⟩

def cert0296r : CertifiedBoard :=
  ⟨seed0296.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0297 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,1,0,0,0,0,2,1,1,0,0],
  [1,0,0,2,1,2,0,2,0,0,2,0,2,1,2],
  [1,1,1,0,1,2,0,2,2,1,0,2,2,0,1,1,1],
  [1,2,2,0,0,1,0,1,1,2,0,1,0,2,0,1,2,1,0]
]

def cert0297n : CertifiedBoard :=
  ⟨seed0297, by apply FastValid.valid; decide +kernel⟩

def cert0297r : CertifiedBoard :=
  ⟨seed0297.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0298 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,1,0,0,0,0,2,1,1,1,2],
  [1,0,0,2,1,2,0,2,0,0,2,0,1,0,1],
  [1,2,1,0,1,2,0,1,1,0,2,2,1,2,2,0,0],
  [0,1,2,0,2,1,0,0,1,1,1,0,2,2,0,2,0,1,0]
]

def cert0298n : CertifiedBoard :=
  ⟨seed0298, by apply FastValid.valid; decide +kernel⟩

def cert0298r : CertifiedBoard :=
  ⟨seed0298.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0299 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,1,0,0,0,2,1,1,0,2,2],
  [2,1,0,1,2,2,0,1,0,1,1,1,0,0,0],
  [2,2,1,0,2,0,1,2,0,2,2,0,1,0,0,1,1],
  [1,1,1,2,0,2,0,0,2,1,2,0,2,0,0,2,1,2,1]
]

def cert0299n : CertifiedBoard :=
  ⟨seed0299, by apply FastValid.valid; decide +kernel⟩

def cert0299r : CertifiedBoard :=
  ⟨seed0299.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0300 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,1,0,0,0,2,1,1,1,0,0],
  [1,2,0,1,1,1,0,1,1,2,2,0,2,1,2],
  [2,0,0,0,1,2,1,0,0,2,0,2,0,2,1,2,0],
  [2,2,1,0,2,0,1,2,0,0,2,2,0,1,0,1,0,2,2]
]

def cert0300n : CertifiedBoard :=
  ⟨seed0300, by apply FastValid.valid; decide +kernel⟩

def cert0300r : CertifiedBoard :=
  ⟨seed0300.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0301 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,1,0,0,0,2,1,1,1,0,0],
  [2,1,0,1,1,1,0,0,2,1,2,2,0,2,1],
  [0,1,2,1,2,0,1,2,0,0,0,2,0,2,2,1,0],
  [1,0,2,0,1,0,2,0,2,2,0,1,0,1,1,2,0,0,1]
]

def cert0301n : CertifiedBoard :=
  ⟨seed0301, by apply FastValid.valid; decide +kernel⟩

def cert0301r : CertifiedBoard :=
  ⟨seed0301.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0302 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,1,0,0,0,2,1,1,1,2,0],
  [0,2,0,1,1,1,0,2,2,1,2,0,2,0,2],
  [1,0,1,2,0,1,2,1,0,0,0,2,2,0,1,1,0],
  [2,0,0,2,0,2,1,0,1,0,0,1,0,2,1,2,2,0,0]
]

def cert0302n : CertifiedBoard :=
  ⟨seed0302, by apply FastValid.valid; decide +kernel⟩

def cert0302r : CertifiedBoard :=
  ⟨seed0302.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0303 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,1,0,0,0,2,1,1,1,2,0],
  [1,2,0,1,2,1,0,2,2,1,2,0,2,0,0],
  [0,1,1,0,1,0,0,2,0,2,1,0,1,0,2,1,2],
  [2,0,2,0,1,1,1,0,0,0,1,2,2,0,0,2,2,0,1]
]

def cert0303n : CertifiedBoard :=
  ⟨seed0303, by apply FastValid.valid; decide +kernel⟩

def cert0303r : CertifiedBoard :=
  ⟨seed0303.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0304 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,1,0,0,0,2,1,1,1,2,0],
  [2,1,0,1,1,1,0,0,1,2,0,1,0,1,1],
  [2,0,2,0,1,2,1,2,0,0,2,2,0,2,2,0,0],
  [1,1,0,2,1,2,2,1,0,2,0,2,0,1,0,0,0,2,1]
]

def cert0304n : CertifiedBoard :=
  ⟨seed0304, by apply FastValid.valid; decide +kernel⟩

def cert0304r : CertifiedBoard :=
  ⟨seed0304.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0305 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,1,0,0,2,0,1,2,0,2,1],
  [0,1,0,2,0,2,1,0,0,2,1,1,0,1,1],
  [2,1,2,0,2,2,0,1,0,1,1,2,1,2,0,0,0],
  [1,1,1,1,0,0,0,2,2,0,1,2,2,1,0,2,0,0,1]
]

def cert0305n : CertifiedBoard :=
  ⟨seed0305, by apply FastValid.valid; decide +kernel⟩

def cert0305r : CertifiedBoard :=
  ⟨seed0305.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0306 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,1,0,0,2,0,2,1,1,1,2],
  [1,2,0,1,1,1,0,0,0,1,2,1,2,0,1],
  [0,0,0,2,2,0,1,0,2,1,2,2,1,0,2,0,0],
  [0,1,0,1,1,0,0,2,1,0,1,2,0,2,0,2,2,0,0]
]

def cert0306n : CertifiedBoard :=
  ⟨seed0306, by apply FastValid.valid; decide +kernel⟩

def cert0306r : CertifiedBoard :=
  ⟨seed0306.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0307 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,1,0,0,2,1,0,0,0,2,2],
  [2,0,2,0,2,1,2,0,1,1,0,0,1,2,0],
  [2,2,1,0,1,1,1,1,0,2,0,1,0,1,0,2,1],
  [2,1,1,2,0,1,2,1,2,2,0,2,2,0,0,0,2,0,0]
]

def cert0307n : CertifiedBoard :=
  ⟨seed0307, by apply FastValid.valid; decide +kernel⟩

def cert0307r : CertifiedBoard :=
  ⟨seed0307.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0308 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,1,0,0,2,1,0,1,2,0,2],
  [0,2,1,2,0,1,0,2,2,0,2,1,1,0,2],
  [0,1,1,1,1,0,1,0,0,0,2,2,1,2,1,0,0],
  [0,2,0,2,0,0,0,1,2,0,0,2,0,1,1,2,2,0,1]
]

def cert0308n : CertifiedBoard :=
  ⟨seed0308, by apply FastValid.valid; decide +kernel⟩

def cert0308r : CertifiedBoard :=
  ⟨seed0308.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0309 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,1,1,0,0,0,0,2,1,1,0],
  [1,2,0,2,0,2,1,0,0,1,1,2,2,0,1],
  [0,1,1,1,0,2,2,1,0,2,0,0,2,0,2,1,2],
  [1,0,1,2,0,1,0,1,2,1,2,0,0,2,2,0,1,0,0]
]

def cert0309n : CertifiedBoard :=
  ⟨seed0309, by apply FastValid.valid; decide +kernel⟩

def cert0309r : CertifiedBoard :=
  ⟨seed0309.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0310 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,1,1,0,0,0,0,2,1,1,1],
  [1,1,0,1,2,2,0,0,2,0,1,2,1,2,0],
  [2,0,1,0,0,2,0,2,1,2,0,2,0,1,1,0,2],
  [0,2,2,0,0,1,0,2,2,1,0,1,1,2,0,2,1,0,0]
]

def cert0310n : CertifiedBoard :=
  ⟨seed0310, by apply FastValid.valid; decide +kernel⟩

def cert0310r : CertifiedBoard :=
  ⟨seed0310.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0311 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,1,1,0,0,0,0,2,1,1,2],
  [1,2,0,0,2,1,0,0,2,2,0,1,2,2,1],
  [0,1,1,1,0,2,2,0,1,1,0,2,0,1,2,0,0],
  [2,1,2,0,2,0,2,0,2,1,2,1,0,0,1,0,1,0,1]
]

def cert0311n : CertifiedBoard :=
  ⟨seed0311, by apply FastValid.valid; decide +kernel⟩

def cert0311r : CertifiedBoard :=
  ⟨seed0311.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0312 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,1,1,0,0,0,2,2,1,1,1],
  [0,0,2,2,0,1,1,0,1,1,0,2,1,2,1],
  [2,1,0,2,0,2,0,2,0,1,2,2,0,1,0,0,0],
  [1,1,2,0,2,1,2,0,0,2,1,0,1,2,0,0,1,0,0]
]

def cert0312n : CertifiedBoard :=
  ⟨seed0312, by apply FastValid.valid; decide +kernel⟩

def cert0312r : CertifiedBoard :=
  ⟨seed0312.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0313 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,1,1,0,0,0,2,2,1,1,2],
  [2,1,2,0,1,2,0,0,1,0,1,2,1,0,0],
  [1,2,0,2,0,1,1,1,0,1,0,0,0,2,0,2,2],
  [2,2,0,1,1,0,2,1,2,2,0,0,2,1,0,2,0,2,1]
]

def cert0313n : CertifiedBoard :=
  ⟨seed0313, by apply FastValid.valid; decide +kernel⟩

def cert0313r : CertifiedBoard :=
  ⟨seed0313.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0314 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,1,1,0,0,2,1,1,1,0,0],
  [0,2,1,2,1,2,2,0,2,2,0,1,1,0,2],
  [0,1,1,2,0,1,0,2,1,0,1,2,0,0,0,2,0],
  [2,0,0,2,0,2,0,2,2,1,0,1,2,0,1,0,0,0,1]
]

def cert0314n : CertifiedBoard :=
  ⟨seed0314, by apply FastValid.valid; decide +kernel⟩

def cert0314r : CertifiedBoard :=
  ⟨seed0314.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0315 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,1,1,0,0,2,1,1,1,0,0],
  [1,1,0,0,0,2,0,2,2,1,2,0,2,1,2],
  [1,2,1,0,1,0,2,1,0,2,0,0,0,2,2,0,1],
  [0,1,0,1,2,0,1,1,2,2,0,2,0,0,1,2,0,1,1]
]

def cert0315n : CertifiedBoard :=
  ⟨seed0315, by apply FastValid.valid; decide +kernel⟩

def cert0315r : CertifiedBoard :=
  ⟨seed0315.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0316 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,1,1,0,0,2,1,1,1,0,0],
  [1,1,0,1,2,1,0,0,2,2,0,0,2,2,0],
  [2,0,2,0,1,1,2,0,2,0,2,1,0,2,0,1,1],
  [1,0,1,0,2,1,2,2,1,2,0,0,0,0,1,2,0,1,0]
]

def cert0316n : CertifiedBoard :=
  ⟨seed0316, by apply FastValid.valid; decide +kernel⟩

def cert0316r : CertifiedBoard :=
  ⟨seed0316.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0317 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,1,1,0,0,2,1,1,1,0,0],
  [2,2,0,2,0,1,1,0,1,2,1,2,0,1,0],
  [0,2,0,1,1,2,0,0,2,1,0,1,0,2,0,2,2],
  [1,0,0,0,1,2,2,1,0,2,2,0,0,0,2,1,2,0,2]
]

def cert0317n : CertifiedBoard :=
  ⟨seed0317, by apply FastValid.valid; decide +kernel⟩

def cert0317r : CertifiedBoard :=
  ⟨seed0317.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0318 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,1,1,0,0,2,1,1,1,0,2],
  [0,1,0,1,2,2,0,2,0,2,0,1,1,0,1],
  [0,2,1,2,0,2,2,1,0,0,2,1,2,1,0,0,0],
  [2,0,0,0,2,0,1,2,0,0,1,1,2,0,1,0,2,2,0]
]

def cert0318n : CertifiedBoard :=
  ⟨seed0318, by apply FastValid.valid; decide +kernel⟩

def cert0318r : CertifiedBoard :=
  ⟨seed0318.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0319 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,1,1,0,0,2,1,1,1,0,2],
  [0,2,1,2,2,0,2,0,2,1,2,1,0,0,0],
  [0,1,0,0,2,0,2,2,1,0,1,2,0,1,1,0,1],
  [1,0,2,0,0,2,2,0,1,2,0,1,1,2,0,0,0,1,0]
]

def cert0319n : CertifiedBoard :=
  ⟨seed0319, by apply FastValid.valid; decide +kernel⟩

def cert0319r : CertifiedBoard :=
  ⟨seed0319.map List.reverse, by apply FastValid.valid; decide +kernel⟩

end TBoards.Extended
