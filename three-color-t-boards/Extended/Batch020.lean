import Extended.Batch016

/- Generated from extended_seeds.json. Published seeds 0–4:
   Qiyuan Ma, DOI 10.5281/zenodo.23631079, CC-BY-4.0. -/

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.Extended

def seed0640 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,1,1,0,0,0,2,1,1,0,2],
  [0,2,2,0,2,1,2,0,2,0,2,0,1,1,2],
  [1,0,1,2,0,0,1,0,1,0,0,2,0,1,2,0,1],
  [1,2,1,2,2,1,0,0,0,1,1,0,2,2,0,0,2,1,0]
]

def cert0640n : CertifiedBoard :=
  ⟨seed0640, by apply FastValid.valid; decide +kernel⟩

def cert0640r : CertifiedBoard :=
  ⟨seed0640.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0641 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,1,1,0,0,0,2,1,1,2,0],
  [2,0,2,1,2,0,1,1,0,2,2,0,2,0,0],
  [0,0,1,0,1,1,0,1,2,2,0,1,2,0,2,0,1],
  [2,1,0,0,0,2,0,0,1,0,0,2,1,0,2,2,1,2,1]
]

def cert0641n : CertifiedBoard :=
  ⟨seed0641, by apply FastValid.valid; decide +kernel⟩

def cert0641r : CertifiedBoard :=
  ⟨seed0641.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0642 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,1,1,0,0,0,2,2,1,1,0],
  [0,2,2,0,2,0,0,2,1,0,1,2,1,0,2],
  [1,0,0,2,1,2,0,1,0,0,0,1,1,2,2,0,1],
  [2,1,2,0,0,1,0,2,0,1,1,0,1,2,0,2,0,2,1]
]

def cert0642n : CertifiedBoard :=
  ⟨seed0642, by apply FastValid.valid; decide +kernel⟩

def cert0642r : CertifiedBoard :=
  ⟨seed0642.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0643 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,1,1,0,0,0,2,2,1,1,2],
  [0,2,0,1,2,1,2,0,1,0,1,2,2,0,2],
  [1,1,0,0,2,0,1,0,2,1,0,0,0,2,0,0,1],
  [1,2,0,0,1,1,0,2,1,2,0,2,2,0,2,1,0,1,1]
]

def cert0643n : CertifiedBoard :=
  ⟨seed0643, by apply FastValid.valid; decide +kernel⟩

def cert0643r : CertifiedBoard :=
  ⟨seed0643.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0644 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,1,1,0,0,0,2,2,1,1,2],
  [0,2,2,0,1,2,1,0,1,0,2,0,0,0,2],
  [1,0,0,1,2,0,2,1,0,2,1,2,0,0,1,1,0],
  [1,2,2,0,2,0,2,0,1,1,0,1,0,0,2,1,2,0,1]
]

def cert0644n : CertifiedBoard :=
  ⟨seed0644, by apply FastValid.valid; decide +kernel⟩

def cert0644r : CertifiedBoard :=
  ⟨seed0644.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0645 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,1,1,0,0,0,2,2,1,1,2],
  [2,0,1,2,2,0,0,1,0,0,1,2,0,2,0],
  [1,2,0,0,0,2,1,0,2,0,2,1,0,1,1,0,1],
  [0,1,0,0,2,2,0,1,1,0,2,0,2,1,2,1,2,0,1]
]

def cert0645n : CertifiedBoard :=
  ⟨seed0645, by apply FastValid.valid; decide +kernel⟩

def cert0645r : CertifiedBoard :=
  ⟨seed0645.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0646 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,1,1,0,0,1,0,0,0,2,0],
  [2,1,2,0,1,2,1,0,0,2,0,1,1,0,1],
  [2,2,1,2,0,2,0,1,1,0,2,2,0,0,0,2,1],
  [2,0,2,1,0,1,0,2,2,0,2,1,1,2,0,0,1,2,2]
]

def cert0646n : CertifiedBoard :=
  ⟨seed0646, by apply FastValid.valid; decide +kernel⟩

def cert0646r : CertifiedBoard :=
  ⟨seed0646.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0647 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,1,1,0,0,1,0,0,0,2,2],
  [1,0,1,2,1,2,2,0,1,1,0,2,1,1,0],
  [2,0,2,0,1,2,0,2,0,0,2,1,2,0,0,0,1],
  [2,2,1,0,2,2,0,1,1,2,0,2,1,0,1,0,0,2,0]
]

def cert0647n : CertifiedBoard :=
  ⟨seed0647, by apply FastValid.valid; decide +kernel⟩

def cert0647r : CertifiedBoard :=
  ⟨seed0647.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0648 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,1,1,0,0,1,0,0,0,2,2],
  [2,2,0,0,0,2,0,0,1,1,0,0,2,1,1],
  [1,1,0,2,0,2,2,1,0,2,1,0,1,1,2,2,0],
  [2,0,1,2,0,1,0,1,2,1,2,0,2,1,2,0,2,0,1]
]

def cert0648n : CertifiedBoard :=
  ⟨seed0648, by apply FastValid.valid; decide +kernel⟩

def cert0648r : CertifiedBoard :=
  ⟨seed0648.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0649 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,1,1,0,0,1,0,0,2,2,1],
  [1,0,2,0,2,1,2,0,0,2,0,1,2,0,1],
  [2,0,0,2,1,0,1,1,0,1,0,2,2,0,2,1,0],
  [2,1,1,0,0,0,0,1,2,1,2,0,2,0,1,1,2,2,0]
]

def cert0649n : CertifiedBoard :=
  ⟨seed0649, by apply FastValid.valid; decide +kernel⟩

def cert0649r : CertifiedBoard :=
  ⟨seed0649.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0650 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,1,1,0,0,1,0,1,2,0,2],
  [1,0,1,2,0,2,1,0,0,2,2,0,1,0,0],
  [0,0,0,1,1,0,2,1,2,0,2,2,1,2,2,0,1],
  [0,2,0,0,2,0,1,1,2,1,1,0,2,0,0,0,2,1,0]
]

def cert0650n : CertifiedBoard :=
  ⟨seed0650, by apply FastValid.valid; decide +kernel⟩

def cert0650r : CertifiedBoard :=
  ⟨seed0650.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0651 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,1,1,0,0,1,1,0,0,0,2],
  [0,2,2,0,1,2,2,0,0,2,1,0,1,0,1],
  [1,0,2,2,1,2,1,1,2,0,2,0,0,2,0,1,0],
  [0,0,0,1,2,0,2,1,2,0,2,0,1,1,0,2,1,0,0]
]

def cert0651n : CertifiedBoard :=
  ⟨seed0651, by apply FastValid.valid; decide +kernel⟩

def cert0651r : CertifiedBoard :=
  ⟨seed0651.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0652 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,1,1,0,0,1,1,0,0,0,2],
  [1,0,0,2,1,2,0,2,2,0,1,0,2,0,1],
  [0,2,0,0,1,2,1,1,0,2,1,2,2,0,2,1,0],
  [0,1,1,2,0,1,2,0,0,0,2,0,2,2,1,0,1,0,1]
]

def cert0652n : CertifiedBoard :=
  ⟨seed0652, by apply FastValid.valid; decide +kernel⟩

def cert0652r : CertifiedBoard :=
  ⟨seed0652.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0653 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,1,1,0,0,1,1,0,0,2,1],
  [0,2,0,1,2,0,2,1,2,1,2,0,0,0,2],
  [0,0,2,0,2,0,2,2,1,0,2,1,1,0,1,0,1],
  [2,1,0,2,2,0,1,1,2,0,0,1,2,2,0,1,0,0,0]
]

def cert0653n : CertifiedBoard :=
  ⟨seed0653, by apply FastValid.valid; decide +kernel⟩

def cert0653r : CertifiedBoard :=
  ⟨seed0653.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0654 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,1,1,0,0,1,1,0,2,2,1],
  [2,1,2,1,2,0,0,2,0,1,0,1,2,0,2],
  [0,0,2,0,2,1,1,0,2,0,0,2,1,0,1,0,0],
  [0,2,2,0,1,1,2,2,0,2,1,0,0,0,0,1,2,0,1]
]

def cert0654n : CertifiedBoard :=
  ⟨seed0654, by apply FastValid.valid; decide +kernel⟩

def cert0654r : CertifiedBoard :=
  ⟨seed0654.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0655 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,1,1,0,0,1,1,0,2,2,1],
  [2,1,2,1,2,2,0,0,1,2,0,1,2,0,1],
  [2,0,1,0,0,2,1,1,0,0,0,2,0,0,0,2,0],
  [1,1,2,0,2,2,0,2,1,0,1,0,2,0,2,1,0,1,1]
]

def cert0655n : CertifiedBoard :=
  ⟨seed0655, by apply FastValid.valid; decide +kernel⟩

def cert0655r : CertifiedBoard :=
  ⟨seed0655.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0656 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,1,1,0,0,1,1,2,0,2,1],
  [2,0,1,2,1,2,2,0,0,0,2,0,2,2,0],
  [0,1,2,0,0,2,1,1,0,2,1,0,1,0,0,0,1],
  [2,1,2,0,1,1,0,2,0,2,2,1,0,1,0,0,2,0,1]
]

def cert0656n : CertifiedBoard :=
  ⟨seed0656, by apply FastValid.valid; decide +kernel⟩

def cert0656r : CertifiedBoard :=
  ⟨seed0656.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0657 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,1,1,0,0,1,1,2,0,2,2],
  [2,0,1,2,0,0,2,1,2,2,0,1,0,2,0],
  [0,0,0,2,1,1,0,2,1,0,0,2,0,1,1,0,1],
  [2,2,0,2,2,1,2,1,0,1,0,0,1,2,0,2,0,0,0]
]

def cert0657n : CertifiedBoard :=
  ⟨seed0657, by apply FastValid.valid; decide +kernel⟩

def cert0657r : CertifiedBoard :=
  ⟨seed0657.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0658 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,1,1,0,0,1,2,0,2,0,1],
  [2,2,0,2,0,1,1,0,1,0,1,1,0,0,0],
  [0,0,2,1,0,2,1,2,0,2,1,2,2,0,1,0,2],
  [0,2,0,0,0,2,2,1,0,0,1,2,1,1,2,0,0,2,2]
]

def cert0658n : CertifiedBoard :=
  ⟨seed0658, by apply FastValid.valid; decide +kernel⟩

def cert0658r : CertifiedBoard :=
  ⟨seed0658.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0659 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,1,1,0,0,1,2,0,2,2,1],
  [2,1,2,2,0,2,0,0,2,1,1,0,2,0,0],
  [0,0,0,0,2,1,0,0,1,1,2,1,2,0,1,0,1],
  [1,0,2,2,0,1,2,0,2,0,1,0,1,1,0,0,2,1,0]
]

def cert0659n : CertifiedBoard :=
  ⟨seed0659, by apply FastValid.valid; decide +kernel⟩

def cert0659r : CertifiedBoard :=
  ⟨seed0659.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0660 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,1,1,0,0,2,0,1,2,0,2],
  [0,2,2,0,0,0,2,0,0,0,1,1,0,0,1],
  [1,1,0,2,1,0,1,1,2,0,2,1,2,2,0,1,2],
  [1,2,0,1,0,1,0,2,1,0,0,2,0,2,2,1,2,1,1]
]

def cert0660n : CertifiedBoard :=
  ⟨seed0660, by apply FastValid.valid; decide +kernel⟩

def cert0660r : CertifiedBoard :=
  ⟨seed0660.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0661 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,1,1,0,0,2,0,2,1,1,0],
  [0,2,2,0,0,0,2,1,0,1,0,2,1,0,2],
  [1,0,0,1,2,0,1,1,2,1,2,0,2,0,2,0,1],
  [0,1,1,0,1,0,0,1,2,2,1,2,0,0,0,2,2,0,1]
]

def cert0661n : CertifiedBoard :=
  ⟨seed0661, by apply FastValid.valid; decide +kernel⟩

def cert0661r : CertifiedBoard :=
  ⟨seed0661.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0662 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,1,1,0,0,2,1,1,0,0,0],
  [1,0,1,2,0,0,0,1,1,2,1,2,0,2,2],
  [0,0,2,0,2,1,0,0,2,0,1,2,2,1,2,0,1],
  [2,2,0,0,1,0,1,1,0,2,0,1,0,2,2,0,2,1,0]
]

def cert0662n : CertifiedBoard :=
  ⟨seed0662, by apply FastValid.valid; decide +kernel⟩

def cert0662r : CertifiedBoard :=
  ⟨seed0662.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0663 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,1,1,0,0,2,1,1,0,0,1],
  [0,2,0,1,2,2,0,2,2,1,2,1,0,0,2],
  [1,0,2,1,2,0,2,0,1,2,0,0,0,0,1,0,1],
  [0,1,1,0,2,0,1,1,2,0,2,2,0,0,2,1,0,1,0]
]

def cert0663n : CertifiedBoard :=
  ⟨seed0663, by apply FastValid.valid; decide +kernel⟩

def cert0663r : CertifiedBoard :=
  ⟨seed0663.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0664 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,1,1,0,0,2,1,1,0,0,1],
  [1,0,0,2,0,1,1,0,2,1,2,2,0,0,0],
  [2,0,0,2,2,1,2,1,0,1,2,0,2,0,2,1,0],
  [0,0,0,1,1,2,0,2,2,0,1,0,1,0,2,0,1,2,0]
]

def cert0664n : CertifiedBoard :=
  ⟨seed0664, by apply FastValid.valid; decide +kernel⟩

def cert0664r : CertifiedBoard :=
  ⟨seed0664.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0665 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,1,1,0,0,2,1,1,0,0,1],
  [1,0,0,2,0,1,1,0,2,1,2,2,0,0,0],
  [2,0,0,2,2,1,2,1,0,1,2,0,2,0,2,1,0],
  [0,0,0,1,1,2,0,2,2,0,1,0,2,0,1,0,1,2,0]
]

def cert0665n : CertifiedBoard :=
  ⟨seed0665, by apply FastValid.valid; decide +kernel⟩

def cert0665r : CertifiedBoard :=
  ⟨seed0665.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0666 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,1,1,0,0,2,1,1,0,0,1],
  [2,1,2,1,2,0,1,0,1,2,2,0,2,1,0],
  [1,0,1,2,0,2,2,0,0,1,0,2,0,0,0,0,2],
  [0,2,0,1,1,2,0,2,1,0,0,2,0,1,1,0,2,2,1]
]

def cert0666n : CertifiedBoard :=
  ⟨seed0666, by apply FastValid.valid; decide +kernel⟩

def cert0666r : CertifiedBoard :=
  ⟨seed0666.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0667 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,1,1,0,0,2,1,1,0,1,2],
  [1,0,2,0,1,2,0,0,2,1,2,2,0,0,0],
  [1,2,1,0,0,1,0,2,0,2,2,0,2,0,1,0,1],
  [0,0,0,1,1,0,0,2,2,1,2,0,1,1,2,0,2,1,0]
]

def cert0667n : CertifiedBoard :=
  ⟨seed0667, by apply FastValid.valid; decide +kernel⟩

def cert0667r : CertifiedBoard :=
  ⟨seed0667.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0668 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,1,1,0,0,2,1,1,0,2,1],
  [0,0,1,2,2,0,1,0,1,2,1,0,0,1,0],
  [2,1,0,2,0,2,2,0,2,0,0,0,2,1,2,0,1],
  [1,0,1,1,0,0,2,0,1,1,2,0,2,2,1,2,0,0,0]
]

def cert0668n : CertifiedBoard :=
  ⟨seed0668, by apply FastValid.valid; decide +kernel⟩

def cert0668r : CertifiedBoard :=
  ⟨seed0668.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0669 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,1,1,0,0,2,1,1,2,0,1],
  [0,0,2,0,1,2,1,0,2,1,2,2,1,2,0],
  [0,1,0,1,2,0,2,2,0,2,0,0,0,1,0,0,1],
  [2,0,0,2,1,0,1,1,0,2,0,2,2,0,1,1,0,0,0]
]

def cert0669n : CertifiedBoard :=
  ⟨seed0669, by apply FastValid.valid; decide +kernel⟩

def cert0669r : CertifiedBoard :=
  ⟨seed0669.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0670 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,1,1,0,0,2,1,1,2,0,1],
  [0,2,2,0,0,0,2,1,0,1,2,2,1,2,1],
  [1,0,0,0,1,0,2,0,2,0,1,0,2,0,2,1,0],
  [2,1,2,0,0,1,1,0,0,2,2,0,1,1,0,1,2,0,2]
]

def cert0670n : CertifiedBoard :=
  ⟨seed0670, by apply FastValid.valid; decide +kernel⟩

def cert0670r : CertifiedBoard :=
  ⟨seed0670.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0671 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,1,1,0,0,2,1,1,2,0,2],
  [0,2,1,2,0,1,1,0,2,0,0,2,1,0,1],
  [2,0,1,2,2,1,2,1,0,0,0,1,0,0,0,2,0],
  [1,1,0,1,0,2,2,0,1,2,0,2,0,2,2,0,0,1,1]
]

def cert0671n : CertifiedBoard :=
  ⟨seed0671, by apply FastValid.valid; decide +kernel⟩

def cert0671r : CertifiedBoard :=
  ⟨seed0671.map List.reverse, by apply FastValid.valid; decide +kernel⟩

end TBoards.Extended
