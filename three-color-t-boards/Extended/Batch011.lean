import Extended.Batch007

/- Generated from extended_seeds.json. Published seeds 0–4:
   Qiyuan Ma, DOI 10.5281/zenodo.23631079, CC-BY-4.0. -/

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.Extended

def seed0352 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,0,1,1,2,2,1,1,0,2],
  [0,2,2,0,0,2,0,2,0,1,1,1,0,2,1],
  [1,2,0,2,0,1,1,1,0,1,0,0,2,1,0,0,0],
  [2,1,2,0,0,0,1,2,1,0,1,0,0,2,2,0,2,1,2]
]

def cert0352n : CertifiedBoard :=
  ⟨seed0352, by apply FastValid.valid; decide +kernel⟩

def cert0352r : CertifiedBoard :=
  ⟨seed0352.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0353 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,0,1,1,2,2,1,1,1,0],
  [0,2,2,0,2,0,2,1,0,1,1,1,0,0,1],
  [0,1,0,2,1,0,0,2,2,0,1,2,1,2,0,0,0],
  [1,0,1,0,0,0,2,1,2,0,2,0,0,2,0,1,1,0,2]
]

def cert0353n : CertifiedBoard :=
  ⟨seed0353, by apply FastValid.valid; decide +kernel⟩

def cert0353r : CertifiedBoard :=
  ⟨seed0353.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0354 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,0,1,2,0,0,0,2,2,1],
  [1,0,2,0,2,0,1,1,2,0,0,1,1,0,0],
  [2,2,0,2,1,0,1,1,1,0,2,1,2,1,0,1,0],
  [2,1,1,1,0,0,0,2,1,2,2,0,2,0,1,0,0,2,2]
]

def cert0354n : CertifiedBoard :=
  ⟨seed0354, by apply FastValid.valid; decide +kernel⟩

def cert0354r : CertifiedBoard :=
  ⟨seed0354.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0355 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,0,1,2,0,0,2,2,1,1],
  [1,1,0,1,1,0,0,0,0,1,0,1,1,1,0],
  [1,0,0,2,1,2,2,0,0,2,2,0,2,0,2,1,2],
  [1,2,1,0,2,1,0,2,0,1,1,1,2,0,2,0,1,0,0]
]

def cert0355n : CertifiedBoard :=
  ⟨seed0355, by apply FastValid.valid; decide +kernel⟩

def cert0355r : CertifiedBoard :=
  ⟨seed0355.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0356 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,0,1,2,0,2,0,2,2,1],
  [2,2,0,1,0,2,2,0,1,0,1,1,1,2,2],
  [0,1,1,0,0,0,2,1,1,0,0,1,1,1,0,0,0],
  [2,1,2,1,0,2,0,0,2,1,2,0,2,0,0,2,1,0,1]
]

def cert0356n : CertifiedBoard :=
  ⟨seed0356, by apply FastValid.valid; decide +kernel⟩

def cert0356r : CertifiedBoard :=
  ⟨seed0356.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0357 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,0,1,2,0,2,2,1,1,1],
  [0,1,0,1,1,0,0,0,0,1,1,2,1,0,0],
  [1,0,2,1,2,2,0,0,2,2,0,0,2,1,2,0,1],
  [1,1,1,0,1,0,0,2,0,2,0,2,1,0,2,0,1,1,0]
]

def cert0357n : CertifiedBoard :=
  ⟨seed0357, by apply FastValid.valid; decide +kernel⟩

def cert0357r : CertifiedBoard :=
  ⟨seed0357.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0358 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,0,1,2,0,2,2,1,1,1],
  [0,1,0,1,1,0,0,0,0,1,1,2,1,0,0],
  [1,0,2,1,2,2,0,0,2,2,0,0,2,1,2,0,1],
  [1,1,1,0,1,0,0,2,1,0,2,0,2,0,2,0,1,1,0]
]

def cert0358n : CertifiedBoard :=
  ⟨seed0358, by apply FastValid.valid; decide +kernel⟩

def cert0358r : CertifiedBoard :=
  ⟨seed0358.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0359 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,0,1,2,0,2,2,1,1,2],
  [1,0,1,0,0,0,1,1,1,0,1,1,1,0,0],
  [0,2,1,2,1,0,2,0,0,0,2,1,2,2,0,0,2],
  [1,2,0,2,0,1,0,0,2,2,0,2,1,0,2,0,1,1,0]
]

def cert0359n : CertifiedBoard :=
  ⟨seed0359, by apply FastValid.valid; decide +kernel⟩

def cert0359r : CertifiedBoard :=
  ⟨seed0359.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0360 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,0,2,0,1,0,1,1,1,2],
  [0,1,0,1,1,0,2,0,2,1,2,2,0,0,0],
  [1,2,0,1,1,1,0,0,2,2,1,2,0,2,0,0,1],
  [1,2,1,1,0,0,0,2,1,0,2,1,0,0,2,2,0,1,2]
]

def cert0360n : CertifiedBoard :=
  ⟨seed0360, by apply FastValid.valid; decide +kernel⟩

def cert0360r : CertifiedBoard :=
  ⟨seed0360.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0361 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,0,2,0,1,0,1,1,1,2],
  [1,0,1,1,0,0,2,0,1,2,0,0,2,1,1],
  [1,2,2,0,1,1,0,0,2,2,0,2,0,2,1,0,0],
  [1,1,1,0,2,1,2,1,0,2,2,1,2,0,0,0,0,1,0]
]

def cert0361n : CertifiedBoard :=
  ⟨seed0361, by apply FastValid.valid; decide +kernel⟩

def cert0361r : CertifiedBoard :=
  ⟨seed0361.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0362 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,0,2,0,1,0,2,1,1,2],
  [1,2,0,1,1,1,0,1,0,0,2,2,0,0,2],
  [1,1,1,0,1,2,1,0,0,2,0,2,0,2,1,0,0],
  [0,2,1,2,2,0,1,1,0,2,2,1,2,0,0,0,0,1,1]
]

def cert0362n : CertifiedBoard :=
  ⟨seed0362, by apply FastValid.valid; decide +kernel⟩

def cert0362r : CertifiedBoard :=
  ⟨seed0362.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0363 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,0,2,0,1,1,1,0,1,1],
  [0,0,2,1,2,0,0,2,0,1,2,2,0,0,0],
  [1,1,0,0,0,2,0,2,2,1,2,1,1,2,0,1,1],
  [1,1,1,0,1,0,2,1,0,2,2,0,2,1,0,0,1,0,0]
]

def cert0363n : CertifiedBoard :=
  ⟨seed0363, by apply FastValid.valid; decide +kernel⟩

def cert0363r : CertifiedBoard :=
  ⟨seed0363.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0364 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,0,2,0,1,2,0,2,1,1],
  [2,1,2,0,0,0,2,0,1,0,1,0,0,2,1],
  [1,1,1,0,2,2,0,0,2,1,0,0,0,1,1,2,1],
  [2,1,2,2,0,2,2,1,0,1,1,1,0,2,0,1,1,0,0]
]

def cert0364n : CertifiedBoard :=
  ⟨seed0364, by apply FastValid.valid; decide +kernel⟩

def cert0364r : CertifiedBoard :=
  ⟨seed0364.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0365 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,0,2,0,2,1,1,0,0,0],
  [2,0,2,1,2,0,0,2,2,1,0,0,1,0,2],
  [0,2,1,0,1,1,2,0,1,1,1,0,1,1,1,0,2],
  [0,2,0,1,0,0,0,2,2,0,1,2,1,2,2,0,0,2,0]
]

def cert0365n : CertifiedBoard :=
  ⟨seed0365, by apply FastValid.valid; decide +kernel⟩

def cert0365r : CertifiedBoard :=
  ⟨seed0365.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0366 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,0,2,0,2,1,1,1,0,0],
  [2,1,0,1,2,0,0,2,2,1,2,2,0,2,1],
  [1,0,1,0,0,0,0,1,0,2,0,1,1,2,0,1,1],
  [1,1,1,0,0,2,0,1,1,0,2,2,0,0,2,1,2,1,0]
]

def cert0366n : CertifiedBoard :=
  ⟨seed0366, by apply FastValid.valid; decide +kernel⟩

def cert0366r : CertifiedBoard :=
  ⟨seed0366.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0367 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,0,2,1,1,0,0,2,0,2],
  [0,1,0,1,0,2,2,1,0,0,2,0,1,1,0],
  [0,2,1,2,0,0,1,1,1,1,0,2,1,2,2,0,1],
  [1,0,0,0,2,2,0,2,0,1,2,1,0,1,1,2,0,0,0]
]

def cert0367n : CertifiedBoard :=
  ⟨seed0367, by apply FastValid.valid; decide +kernel⟩

def cert0367r : CertifiedBoard :=
  ⟨seed0367.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0368 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,0,2,1,1,0,1,1,2,0],
  [2,0,2,1,0,0,2,1,2,2,0,1,1,0,0],
  [2,0,1,1,1,1,0,2,2,0,2,0,1,0,0,1,0],
  [1,0,2,0,0,0,2,0,0,0,2,2,1,2,1,0,1,2,0]
]

def cert0368n : CertifiedBoard :=
  ⟨seed0368, by apply FastValid.valid; decide +kernel⟩

def cert0368r : CertifiedBoard :=
  ⟨seed0368.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0369 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,0,2,1,1,0,2,0,2,2],
  [2,2,0,2,0,1,1,2,1,0,2,1,0,0,0],
  [0,1,1,0,0,2,0,1,1,1,1,0,1,2,0,1,0],
  [1,0,1,0,0,2,2,1,2,2,0,0,2,1,2,0,0,0,1]
]

def cert0369n : CertifiedBoard :=
  ⟨seed0369, by apply FastValid.valid; decide +kernel⟩

def cert0369r : CertifiedBoard :=
  ⟨seed0369.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0370 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,0,2,1,1,1,0,0,0,2],
  [2,1,0,1,1,1,0,1,2,2,0,0,2,0,1],
  [0,1,1,0,0,0,2,0,1,0,2,0,2,2,1,2,1],
  [0,2,1,0,0,1,0,2,2,0,1,1,2,0,2,1,2,0,0]
]

def cert0370n : CertifiedBoard :=
  ⟨seed0370, by apply FastValid.valid; decide +kernel⟩

def cert0370r : CertifiedBoard :=
  ⟨seed0370.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0371 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,0,2,1,1,1,0,1,1,2],
  [2,1,0,1,1,1,0,0,0,2,0,1,0,0,0],
  [1,2,0,0,1,2,1,2,0,0,2,2,0,1,0,2,2],
  [2,2,0,2,1,2,2,1,0,2,0,2,0,1,1,0,0,2,1]
]

def cert0371n : CertifiedBoard :=
  ⟨seed0371, by apply FastValid.valid; decide +kernel⟩

def cert0371r : CertifiedBoard :=
  ⟨seed0371.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0372 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,0,2,1,1,1,1,0,2,1],
  [2,1,0,1,0,1,1,2,1,2,2,0,0,0,0],
  [0,1,1,0,0,2,1,0,0,2,0,2,2,0,2,0,1],
  [1,2,0,1,1,0,2,0,0,2,2,1,2,0,1,0,0,1,2]
]

def cert0372n : CertifiedBoard :=
  ⟨seed0372, by apply FastValid.valid; decide +kernel⟩

def cert0372r : CertifiedBoard :=
  ⟨seed0372.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0373 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,0,2,1,1,1,1,2,0,2],
  [2,1,0,0,2,2,0,1,2,2,0,0,2,2,1],
  [0,1,1,0,1,0,2,0,1,1,0,1,1,0,0,0,0],
  [0,2,1,0,0,2,0,2,1,2,1,2,0,1,0,2,0,0,1]
]

def cert0373n : CertifiedBoard :=
  ⟨seed0373, by apply FastValid.valid; decide +kernel⟩

def cert0373r : CertifiedBoard :=
  ⟨seed0373.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0374 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,1,0,0,0,0,2,1,1,2],
  [1,2,0,1,2,0,1,0,0,1,1,1,1,0,0],
  [1,2,2,1,2,0,2,2,0,0,2,0,0,2,1,0,1],
  [0,1,1,0,1,0,2,0,1,1,0,2,2,0,2,0,2,1,2]
]

def cert0374n : CertifiedBoard :=
  ⟨seed0374, by apply FastValid.valid; decide +kernel⟩

def cert0374r : CertifiedBoard :=
  ⟨seed0374.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0375 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,1,0,0,0,0,2,2,1,1],
  [0,1,0,1,1,1,0,0,2,1,2,0,2,0,2],
  [0,2,2,0,0,2,1,2,0,1,1,1,0,2,1,0,1],
  [1,1,0,2,0,2,0,1,0,0,1,2,0,1,1,2,2,0,0]
]

def cert0375n : CertifiedBoard :=
  ⟨seed0375, by apply FastValid.valid; decide +kernel⟩

def cert0375r : CertifiedBoard :=
  ⟨seed0375.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0376 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,1,0,0,0,0,2,2,1,1],
  [1,0,0,1,0,1,1,0,2,0,1,1,1,1,0],
  [2,0,0,2,1,2,0,2,1,2,0,2,0,1,2,2,0],
  [1,1,0,1,1,2,0,1,0,0,2,1,0,2,2,0,2,0,0]
]

def cert0376n : CertifiedBoard :=
  ⟨seed0376, by apply FastValid.valid; decide +kernel⟩

def cert0376r : CertifiedBoard :=
  ⟨seed0376.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0377 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,1,0,0,0,2,0,2,2,1],
  [2,1,2,0,0,2,1,0,1,0,1,1,2,0,2],
  [2,1,1,0,2,2,0,1,0,0,0,1,1,1,1,0,0],
  [0,2,1,2,0,1,1,0,2,0,0,2,0,1,2,2,0,2,1]
]

def cert0377n : CertifiedBoard :=
  ⟨seed0377, by apply FastValid.valid; decide +kernel⟩

def cert0377r : CertifiedBoard :=
  ⟨seed0377.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0378 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,1,0,0,0,2,1,1,0,0],
  [1,1,0,1,0,2,0,2,1,0,1,1,0,0,2],
  [2,0,2,1,2,2,0,2,2,1,2,0,0,0,1,1,1],
  [0,2,0,1,1,1,2,0,0,2,2,0,1,0,2,0,1,2,0]
]

def cert0378n : CertifiedBoard :=
  ⟨seed0378, by apply FastValid.valid; decide +kernel⟩

def cert0378r : CertifiedBoard :=
  ⟨seed0378.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0379 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,1,0,0,0,2,1,1,1,0],
  [1,0,2,1,2,0,0,2,2,0,1,1,1,0,0],
  [0,2,1,0,1,0,2,0,2,2,1,2,2,0,1,0,1],
  [0,1,1,2,0,0,0,1,1,0,0,2,0,2,0,1,2,0,2]
]

def cert0379n : CertifiedBoard :=
  ⟨seed0379, by apply FastValid.valid; decide +kernel⟩

def cert0379r : CertifiedBoard :=
  ⟨seed0379.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0380 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,1,0,0,0,2,1,1,2,0],
  [2,0,0,1,1,1,0,1,1,0,1,2,2,1,0],
  [1,0,2,1,2,0,0,0,2,1,2,0,2,0,1,0,2],
  [0,2,0,2,2,0,2,2,0,1,1,1,0,0,2,0,1,0,0]
]

def cert0380n : CertifiedBoard :=
  ⟨seed0380, by apply FastValid.valid; decide +kernel⟩

def cert0380r : CertifiedBoard :=
  ⟨seed0380.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0381 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,1,0,0,0,2,2,1,1,2],
  [2,2,0,0,0,2,1,0,0,1,1,1,1,0,2],
  [1,2,0,2,0,1,0,1,0,2,1,2,0,1,1,0,0],
  [0,2,0,1,1,0,1,2,0,0,2,0,2,1,2,2,0,2,2]
]

def cert0381n : CertifiedBoard :=
  ⟨seed0381, by apply FastValid.valid; decide +kernel⟩

def cert0381r : CertifiedBoard :=
  ⟨seed0381.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0382 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,1,0,0,2,1,1,0,0,0],
  [2,0,2,1,2,0,0,1,1,1,1,0,2,0,1],
  [0,1,1,0,1,1,2,0,0,0,2,0,2,2,1,2,2],
  [2,2,0,1,0,1,2,0,1,0,0,2,1,0,2,2,0,2,0]
]

def cert0382n : CertifiedBoard :=
  ⟨seed0382, by apply FastValid.valid; decide +kernel⟩

def cert0382r : CertifiedBoard :=
  ⟨seed0382.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0383 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,0,1,2,1,0,0,2,1,1,1,0,0],
  [1,0,2,0,2,1,2,0,0,0,0,2,0,2,2],
  [1,1,1,0,1,1,2,0,2,1,0,0,2,2,0,1,1],
  [2,2,0,1,0,1,2,2,1,2,0,0,1,0,2,0,1,1,0]
]

def cert0383n : CertifiedBoard :=
  ⟨seed0383, by apply FastValid.valid; decide +kernel⟩

def cert0383r : CertifiedBoard :=
  ⟨seed0383.map List.reverse, by apply FastValid.valid; decide +kernel⟩

end TBoards.Extended
