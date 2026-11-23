import Extended.Batch010

/- Generated from extended_seeds.json. Published seeds 0–4:
   Qiyuan Ma, DOI 10.5281/zenodo.23631079, CC-BY-4.0. -/

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.Extended

def seed0448 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,0,1,0,0,1,1,1,0,2,2],
  [1,1,0,2,1,2,0,2,0,0,2,1,0,1,2],
  [2,2,0,2,1,1,1,2,0,1,0,1,1,0,0,0,0],
  [1,2,0,2,2,1,2,1,0,0,2,0,1,2,2,0,0,1,1]
]

def cert0448n : CertifiedBoard :=
  ⟨seed0448, by apply FastValid.valid; decide +kernel⟩

def cert0448r : CertifiedBoard :=
  ⟨seed0448.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0449 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,0,1,0,0,1,2,0,2,2,1],
  [2,1,0,1,2,0,0,2,2,0,1,1,0,1,1],
  [1,1,1,0,0,0,0,1,0,2,1,2,1,0,2,0,2],
  [0,2,1,2,2,0,2,0,0,2,1,1,1,2,0,1,1,0,0]
]

def cert0449n : CertifiedBoard :=
  ⟨seed0449, by apply FastValid.valid; decide +kernel⟩

def cert0449r : CertifiedBoard :=
  ⟨seed0449.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0450 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,0,1,1,0,0,0,1,1,2,0],
  [1,1,0,1,2,0,2,0,0,2,1,2,0,1,1],
  [0,1,2,1,2,2,1,0,1,0,2,1,0,2,2,0,0],
  [2,0,2,1,1,1,1,0,0,1,0,0,0,2,0,2,2,0,1]
]

def cert0450n : CertifiedBoard :=
  ⟨seed0450, by apply FastValid.valid; decide +kernel⟩

def cert0450r : CertifiedBoard :=
  ⟨seed0450.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0451 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,0,1,1,0,1,0,0,1,2,0],
  [2,0,2,2,1,0,0,0,2,1,2,0,2,2,0],
  [2,0,1,1,1,2,0,1,0,1,1,1,0,2,1,1,0],
  [1,0,2,1,2,2,0,2,0,0,1,2,1,0,0,0,2,0,0]
]

def cert0451n : CertifiedBoard :=
  ⟨seed0451, by apply FastValid.valid; decide +kernel⟩

def cert0451r : CertifiedBoard :=
  ⟨seed0451.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0452 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,0,1,1,0,1,0,2,1,1,1],
  [2,1,0,2,2,0,0,0,1,2,0,2,1,0,0],
  [1,1,2,0,1,1,0,0,2,2,0,1,0,0,2,1,2],
  [1,2,1,2,0,2,0,2,0,0,0,1,1,1,0,1,2,2,1]
]

def cert0452n : CertifiedBoard :=
  ⟨seed0452, by apply FastValid.valid; decide +kernel⟩

def cert0452r : CertifiedBoard :=
  ⟨seed0452.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0453 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,0,1,1,0,1,2,0,2,1,1],
  [2,0,2,2,1,2,2,0,1,0,0,1,2,0,0],
  [1,1,0,0,1,1,1,1,2,0,2,0,0,0,0,2,1],
  [2,1,2,1,0,2,1,0,0,2,2,0,1,0,1,1,0,2,0]
]

def cert0453n : CertifiedBoard :=
  ⟨seed0453, by apply FastValid.valid; decide +kernel⟩

def cert0453r : CertifiedBoard :=
  ⟨seed0453.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0454 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,0,1,1,0,1,2,0,2,1,1],
  [2,0,2,2,1,2,2,0,1,0,0,1,2,0,0],
  [1,1,0,0,1,1,1,1,2,0,2,0,0,0,0,2,1],
  [2,1,2,1,0,2,1,0,0,2,2,0,1,1,0,1,0,2,0]
]

def cert0454n : CertifiedBoard :=
  ⟨seed0454, by apply FastValid.valid; decide +kernel⟩

def cert0454r : CertifiedBoard :=
  ⟨seed0454.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0455 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,0,1,1,0,1,2,0,2,2,1],
  [2,1,0,2,1,2,0,2,0,0,0,1,1,0,0],
  [1,0,0,2,1,1,1,1,0,2,2,0,2,1,0,1,0],
  [0,2,0,1,1,2,1,2,2,0,0,1,2,0,1,0,0,0,2]
]

def cert0455n : CertifiedBoard :=
  ⟨seed0455, by apply FastValid.valid; decide +kernel⟩

def cert0455r : CertifiedBoard :=
  ⟨seed0455.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0456 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,0,1,1,0,2,0,1,1,2,0],
  [1,0,2,2,1,2,2,0,1,2,0,0,2,1,0],
  [2,0,2,1,1,1,1,0,1,0,0,1,1,0,0,0,2],
  [0,2,2,0,2,1,2,1,0,1,0,0,1,2,0,2,0,0,0]
]

def cert0456n : CertifiedBoard :=
  ⟨seed0456, by apply FastValid.valid; decide +kernel⟩

def cert0456r : CertifiedBoard :=
  ⟨seed0456.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0457 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,0,1,1,0,2,1,1,1,0,0],
  [2,1,0,0,0,1,0,0,2,1,2,1,0,1,1],
  [0,2,2,0,2,1,2,2,0,1,1,1,2,0,0,0,2],
  [1,1,0,1,2,0,1,2,0,2,0,2,0,0,1,0,2,2,1]
]

def cert0457n : CertifiedBoard :=
  ⟨seed0457, by apply FastValid.valid; decide +kernel⟩

def cert0457r : CertifiedBoard :=
  ⟨seed0457.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0458 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,0,1,1,1,1,0,0,1,1,2],
  [0,1,0,2,1,2,1,2,2,0,2,0,0,0,0],
  [1,2,0,2,2,1,0,1,0,2,2,0,1,1,0,0,1],
  [1,2,0,2,1,1,0,0,2,0,1,2,0,0,2,1,0,1,2]
]

def cert0458n : CertifiedBoard :=
  ⟨seed0458, by apply FastValid.valid; decide +kernel⟩

def cert0458r : CertifiedBoard :=
  ⟨seed0458.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0459 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,0,1,1,1,1,0,2,1,1,2],
  [2,0,1,1,0,1,2,2,0,0,1,2,0,2,2],
  [2,2,1,0,0,2,1,0,1,1,0,0,0,1,0,0,0],
  [1,2,0,1,0,2,0,2,1,2,1,2,0,0,2,0,2,2,0]
]

def cert0459n : CertifiedBoard :=
  ⟨seed0459, by apply FastValid.valid; decide +kernel⟩

def cert0459r : CertifiedBoard :=
  ⟨seed0459.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0460 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,0,1,1,1,1,0,2,2,1,1],
  [2,2,0,1,2,0,0,2,0,2,0,2,1,0,0],
  [1,1,2,0,0,0,0,1,1,0,1,1,0,1,0,2,2],
  [0,1,2,0,1,0,0,2,1,2,1,2,2,0,2,1,0,0,1]
]

def cert0460n : CertifiedBoard :=
  ⟨seed0460, by apply FastValid.valid; decide +kernel⟩

def cert0460r : CertifiedBoard :=
  ⟨seed0460.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0461 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,0,1,1,1,2,0,2,1,1,1],
  [0,1,0,0,0,1,2,1,2,0,2,2,0,0,0],
  [1,1,0,0,2,1,2,2,1,0,1,1,0,2,2,0,0],
  [0,0,2,1,0,1,1,0,0,1,0,2,0,2,0,1,2,0,1]
]

def cert0461n : CertifiedBoard :=
  ⟨seed0461, by apply FastValid.valid; decide +kernel⟩

def cert0461r : CertifiedBoard :=
  ⟨seed0461.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0462 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,0,1,1,1,2,0,2,1,1,1],
  [1,1,0,2,2,0,2,0,0,0,1,1,0,0,2],
  [0,1,2,1,2,0,1,0,0,2,0,2,1,2,0,0,1],
  [0,2,1,0,1,0,2,2,0,1,1,0,1,2,2,1,0,0,0]
]

def cert0462n : CertifiedBoard :=
  ⟨seed0462, by apply FastValid.valid; decide +kernel⟩

def cert0462r : CertifiedBoard :=
  ⟨seed0462.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0463 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,0,1,1,1,2,1,1,0,2,2],
  [2,0,0,2,1,2,0,2,0,2,1,0,0,1,2],
  [2,2,1,0,1,1,0,1,1,1,0,0,0,1,0,0,0],
  [1,2,0,1,2,0,0,2,1,2,2,0,2,0,1,0,2,2,0]
]

def cert0463n : CertifiedBoard :=
  ⟨seed0463, by apply FastValid.valid; decide +kernel⟩

def cert0463r : CertifiedBoard :=
  ⟨seed0463.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0464 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,0,1,1,1,2,2,1,1,0,0],
  [0,2,0,2,2,0,2,1,0,2,1,2,1,2,0],
  [1,0,0,0,1,1,1,0,1,0,1,2,0,2,0,1,0],
  [2,0,0,2,1,0,0,0,2,2,0,1,2,0,0,1,1,0,2]
]

def cert0464n : CertifiedBoard :=
  ⟨seed0464, by apply FastValid.valid; decide +kernel⟩

def cert0464r : CertifiedBoard :=
  ⟨seed0464.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0465 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,0,1,1,1,2,2,1,1,0,2],
  [0,1,0,1,2,0,0,2,0,2,1,2,1,0,1],
  [0,2,2,0,1,2,0,2,0,1,1,1,0,0,0,1,0],
  [1,0,0,1,1,0,0,0,2,2,0,2,1,0,2,1,2,0,0]
]

def cert0465n : CertifiedBoard :=
  ⟨seed0465, by apply FastValid.valid; decide +kernel⟩

def cert0465r : CertifiedBoard :=
  ⟨seed0465.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0466 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,0,1,1,1,2,2,1,1,1,0],
  [0,2,1,0,1,1,0,0,0,1,2,0,2,0,1],
  [0,1,0,2,1,2,1,2,0,0,1,2,0,2,2,0,0],
  [1,0,1,0,0,0,2,1,0,0,2,2,0,2,0,1,1,0,2]
]

def cert0466n : CertifiedBoard :=
  ⟨seed0466, by apply FastValid.valid; decide +kernel⟩

def cert0466r : CertifiedBoard :=
  ⟨seed0466.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0467 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,0,1,1,1,2,2,1,1,1,0],
  [0,2,2,0,2,1,2,0,0,0,1,2,1,0,0],
  [1,1,0,2,1,0,1,0,0,2,0,0,2,2,0,1,1],
  [1,0,0,0,1,1,0,2,1,2,0,1,0,1,2,0,2,0,2]
]

def cert0467n : CertifiedBoard :=
  ⟨seed0467, by apply FastValid.valid; decide +kernel⟩

def cert0467r : CertifiedBoard :=
  ⟨seed0467.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0468 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,0,1,2,0,1,0,1,1,1,2],
  [0,1,0,0,1,1,1,0,2,0,0,2,1,0,0],
  [1,2,0,2,1,2,2,0,0,2,2,0,1,2,1,0,1],
  [1,1,0,2,2,1,2,0,2,0,2,1,1,0,0,0,0,1,1]
]

def cert0468n : CertifiedBoard :=
  ⟨seed0468, by apply FastValid.valid; decide +kernel⟩

def cert0468r : CertifiedBoard :=
  ⟨seed0468.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0469 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,0,1,2,0,1,1,0,2,2,1],
  [2,1,0,0,0,1,0,1,1,1,0,1,1,2,2],
  [0,1,2,1,2,0,0,2,2,0,0,0,2,1,0,0,1],
  [2,2,0,2,1,2,0,2,1,1,1,0,2,0,2,0,1,0,0]
]

def cert0469n : CertifiedBoard :=
  ⟨seed0469, by apply FastValid.valid; decide +kernel⟩

def cert0469r : CertifiedBoard :=
  ⟨seed0469.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0470 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,0,1,2,0,2,0,1,1,2,0],
  [2,0,0,1,2,0,0,0,2,1,2,1,0,1,1],
  [1,1,0,2,0,2,2,0,2,1,1,1,1,0,1,0,0],
  [0,0,0,2,2,1,0,0,1,0,2,1,2,2,0,1,1,0,0]
]

def cert0470n : CertifiedBoard :=
  ⟨seed0470, by apply FastValid.valid; decide +kernel⟩

def cert0470r : CertifiedBoard :=
  ⟨seed0470.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0471 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,0,1,2,0,2,0,1,1,2,0],
  [2,0,1,0,1,1,1,0,2,1,2,1,0,2,0],
  [0,1,2,0,2,1,2,2,0,0,1,1,1,0,0,0,1],
  [2,0,2,1,1,0,0,2,2,1,0,1,0,0,0,2,2,0,0]
]

def cert0471n : CertifiedBoard :=
  ⟨seed0471, by apply FastValid.valid; decide +kernel⟩

def cert0471r : CertifiedBoard :=
  ⟨seed0471.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0472 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,0,1,2,1,1,0,0,1,2,0],
  [2,0,2,2,1,2,0,2,0,2,0,1,1,1,0],
  [0,2,1,0,1,1,1,2,0,1,1,0,1,0,0,0,2],
  [1,0,2,2,0,0,2,1,0,2,1,2,2,0,0,1,0,0,0]
]

def cert0472n : CertifiedBoard :=
  ⟨seed0472, by apply FastValid.valid; decide +kernel⟩

def cert0472r : CertifiedBoard :=
  ⟨seed0472.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0473 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,0,1,2,1,1,0,1,1,1,0],
  [0,2,0,0,1,1,1,2,2,0,1,0,0,0,1],
  [1,0,2,2,0,2,1,2,0,1,2,0,2,1,0,0,2],
  [0,1,1,0,2,1,2,0,0,0,2,0,2,2,1,0,1,0,0]
]

def cert0473n : CertifiedBoard :=
  ⟨seed0473, by apply FastValid.valid; decide +kernel⟩

def cert0473r : CertifiedBoard :=
  ⟨seed0473.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0474 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,0,1,2,1,1,0,1,1,1,0],
  [1,2,0,0,0,1,1,2,0,2,0,0,2,1,2],
  [1,0,0,1,0,2,1,2,2,1,0,2,2,0,1,0,0],
  [1,1,1,0,0,0,2,2,0,2,1,0,1,2,0,2,0,1,1]
]

def cert0474n : CertifiedBoard :=
  ⟨seed0474, by apply FastValid.valid; decide +kernel⟩

def cert0474r : CertifiedBoard :=
  ⟨seed0474.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0475 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,0,1,2,1,1,1,0,0,0,1],
  [0,2,1,2,0,1,0,2,1,2,0,0,2,0,2],
  [0,1,0,1,1,1,0,0,1,2,2,1,0,2,2,0,1],
  [0,1,1,0,0,0,2,0,2,2,0,2,1,0,1,1,2,0,0]
]

def cert0475n : CertifiedBoard :=
  ⟨seed0475, by apply FastValid.valid; decide +kernel⟩

def cert0475r : CertifiedBoard :=
  ⟨seed0475.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0476 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,0,1,2,1,1,1,1,0,0,0],
  [0,2,1,2,0,1,1,2,2,0,0,2,2,0,2],
  [0,0,1,2,0,1,1,0,0,1,1,0,2,2,1,0,1],
  [0,1,0,1,0,2,0,2,0,0,2,1,2,0,2,1,0,0,0]
]

def cert0476n : CertifiedBoard :=
  ⟨seed0476, by apply FastValid.valid; decide +kernel⟩

def cert0476r : CertifiedBoard :=
  ⟨seed0476.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0477 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,0,1,2,1,1,1,1,0,1,1],
  [1,1,0,1,2,0,0,1,1,0,0,2,2,0,2],
  [0,2,1,0,0,0,0,2,1,2,2,0,2,2,1,0,0],
  [0,1,1,2,0,1,0,2,0,1,0,2,1,2,0,2,0,0,1]
]

def cert0477n : CertifiedBoard :=
  ⟨seed0477, by apply FastValid.valid; decide +kernel⟩

def cert0477r : CertifiedBoard :=
  ⟨seed0477.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0478 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,0,1,2,1,1,1,1,0,1,2],
  [0,2,0,2,2,0,2,1,0,0,2,1,2,0,2],
  [1,2,0,1,1,2,0,0,1,0,1,0,0,0,0,1,1],
  [1,1,0,2,1,2,2,1,0,2,0,1,1,0,0,2,2,0,0]
]

def cert0478n : CertifiedBoard :=
  ⟨seed0478, by apply FastValid.valid; decide +kernel⟩

def cert0478r : CertifiedBoard :=
  ⟨seed0478.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0479 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,2,0,1,2,1,1,1,1,2,0,2],
  [0,2,0,1,2,0,2,1,2,0,0,2,2,0,1],
  [0,1,1,0,1,0,2,2,1,0,1,0,0,1,1,0,0],
  [2,1,2,2,0,2,1,0,0,0,0,2,0,0,1,1,0,2,1]
]

def cert0479n : CertifiedBoard :=
  ⟨seed0479, by apply FastValid.valid; decide +kernel⟩

def cert0479r : CertifiedBoard :=
  ⟨seed0479.map List.reverse, by apply FastValid.valid; decide +kernel⟩

end TBoards.Extended
