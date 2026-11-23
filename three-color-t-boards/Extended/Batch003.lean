import CertifiedFamily

/- Generated from extended_seeds.json. Published seeds 0–4:
   Qiyuan Ma, DOI 10.5281/zenodo.23631079, CC-BY-4.0. -/

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.Extended

def seed0096 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [2,2,0,2,2,2,0,0,0,1,2,0,1],
  [1,2,2,1,0,0,1,2,1,1,2,2,2,1,2],
  [1,2,1,0,2,1,2,2,1,1,1,2,1,2,0,2,0],
  [2,0,0,2,0,1,1,0,1,0,1,0,0,0,2,2,2,0,0]
]

def cert0096n : CertifiedBoard :=
  ⟨seed0096, by apply FastValid.valid; decide +kernel⟩

def cert0096r : CertifiedBoard :=
  ⟨seed0096.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0097 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [2,2,0,2,2,2,0,0,1,0,1,2,0],
  [1,2,2,0,1,0,1,2,2,2,1,2,1,1,2],
  [1,2,2,2,1,1,2,1,2,1,0,2,1,2,0,0,1],
  [2,0,2,0,1,1,1,0,0,0,2,0,0,0,2,2,1,0,0]
]

def cert0097n : CertifiedBoard :=
  ⟨seed0097, by apply FastValid.valid; decide +kernel⟩

def cert0097r : CertifiedBoard :=
  ⟨seed0097.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0098 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [2,2,0,2,2,2,1,0,0,0,1,0,0],
  [1,2,1,2,2,0,1,1,1,2,1,2,2,0,1],
  [2,1,2,0,2,2,1,0,1,2,1,1,2,2,2,2,1],
  [2,0,0,2,0,0,0,2,1,1,0,2,0,0,1,0,1,2,0]
]

def cert0098n : CertifiedBoard :=
  ⟨seed0098, by apply FastValid.valid; decide +kernel⟩

def cert0098r : CertifiedBoard :=
  ⟨seed0098.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0099 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [2,2,0,2,2,2,1,2,2,1,2,1,1],
  [0,2,2,0,1,2,1,0,0,0,1,2,0,0,2],
  [1,2,2,2,1,0,1,1,1,2,1,1,2,2,2,0,1],
  [1,1,0,1,0,2,1,2,0,2,0,0,1,0,0,2,0,0,0]
]

def cert0099n : CertifiedBoard :=
  ⟨seed0099, by apply FastValid.valid; decide +kernel⟩

def cert0099r : CertifiedBoard :=
  ⟨seed0099.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0100 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [2,2,1,0,1,2,1,0,0,2,0,0,1],
  [2,2,1,1,1,2,2,2,2,0,2,2,1,1,0],
  [1,0,1,1,2,1,2,0,1,2,1,2,2,0,2,2,2],
  [1,2,0,0,1,0,2,1,2,2,0,0,0,2,0,1,0,0,0]
]

def cert0100n : CertifiedBoard :=
  ⟨seed0100, by apply FastValid.valid; decide +kernel⟩

def cert0100r : CertifiedBoard :=
  ⟨seed0100.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0101 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [2,2,1,0,1,2,1,1,1,2,1,2,2],
  [2,2,1,2,0,1,0,0,0,2,2,2,2,0,1],
  [1,2,0,0,1,1,2,2,2,1,2,1,0,1,2,2,0],
  [2,0,2,2,0,2,0,0,0,1,0,0,2,1,1,0,2,0,0]
]

def cert0101n : CertifiedBoard :=
  ⟨seed0101, by apply FastValid.valid; decide +kernel⟩

def cert0101r : CertifiedBoard :=
  ⟨seed0101.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0102 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [2,2,1,0,1,2,1,2,1,2,0,2,0],
  [2,0,0,2,0,2,1,1,0,0,1,1,2,2,2],
  [2,2,1,2,2,0,1,2,2,2,1,1,1,2,1,0,1],
  [1,2,0,1,0,2,2,0,0,0,1,0,0,2,2,2,0,0,0]
]

def cert0102n : CertifiedBoard :=
  ⟨seed0102, by apply FastValid.valid; decide +kernel⟩

def cert0102r : CertifiedBoard :=
  ⟨seed0102.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0103 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [2,2,1,0,1,2,2,0,0,0,1,0,1],
  [2,1,0,2,0,2,1,2,1,2,1,1,1,2,1],
  [1,2,2,2,2,2,1,1,0,0,2,2,0,2,2,1,2],
  [1,2,0,0,2,0,1,1,2,2,0,1,2,0,0,1,0,0,0]
]

def cert0103n : CertifiedBoard :=
  ⟨seed0103, by apply FastValid.valid; decide +kernel⟩

def cert0103r : CertifiedBoard :=
  ⟨seed0103.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0104 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [2,2,1,1,1,2,1,0,0,2,2,0,1],
  [1,0,0,2,0,2,1,2,2,0,2,2,0,1,0],
  [1,2,1,2,2,1,0,1,2,1,1,2,2,2,2,2,1],
  [2,1,2,0,0,1,2,0,0,1,1,0,1,0,2,0,0,0,0]
]

def cert0104n : CertifiedBoard :=
  ⟨seed0104, by apply FastValid.valid; decide +kernel⟩

def cert0104r : CertifiedBoard :=
  ⟨seed0104.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0105 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [2,2,1,1,1,2,1,0,1,2,2,0,1],
  [1,2,0,0,0,2,1,2,0,0,1,2,1,0,0],
  [1,2,1,1,2,2,2,1,2,2,0,2,2,2,2,1,2],
  [0,1,0,2,0,0,0,2,0,2,2,0,1,0,0,1,1,0,1]
]

def cert0105n : CertifiedBoard :=
  ⟨seed0105, by apply FastValid.valid; decide +kernel⟩

def cert0105r : CertifiedBoard :=
  ⟨seed0105.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0106 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [2,2,1,1,1,2,1,1,0,1,2,1,0],
  [1,2,2,0,2,2,0,0,2,0,2,1,2,0,1],
  [1,0,0,2,2,0,1,1,2,2,2,2,1,2,1,2,2],
  [2,2,2,1,0,2,0,0,0,1,0,1,2,0,0,1,0,0,0]
]

def cert0106n : CertifiedBoard :=
  ⟨seed0106, by apply FastValid.valid; decide +kernel⟩

def cert0106r : CertifiedBoard :=
  ⟨seed0106.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0107 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [2,2,1,1,1,2,1,2,0,0,2,0,1],
  [2,2,0,0,1,2,1,0,1,1,2,2,1,2,2],
  [1,2,2,2,2,0,2,2,0,2,1,2,1,1,0,0,1],
  [0,1,0,1,0,2,0,1,2,0,0,0,0,2,2,2,1,0,0]
]

def cert0107n : CertifiedBoard :=
  ⟨seed0107, by apply FastValid.valid; decide +kernel⟩

def cert0107r : CertifiedBoard :=
  ⟨seed0107.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0108 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [2,2,1,1,1,2,1,2,0,2,0,0,1],
  [1,2,1,1,0,1,0,0,1,1,2,2,1,0,0],
  [2,2,0,1,2,1,2,2,0,2,2,2,2,1,2,2,2],
  [1,0,2,0,0,0,0,2,2,0,1,2,0,0,2,1,0,1,0]
]

def cert0108n : CertifiedBoard :=
  ⟨seed0108, by apply FastValid.valid; decide +kernel⟩

def cert0108r : CertifiedBoard :=
  ⟨seed0108.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0109 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [2,2,1,1,1,2,1,2,2,0,2,0,1],
  [1,2,1,1,0,0,2,0,0,1,1,2,0,0,1],
  [2,2,2,1,2,1,2,2,2,1,0,1,2,2,0,2,2],
  [0,1,0,0,0,0,2,1,0,1,2,0,1,0,2,2,2,0,0]
]

def cert0109n : CertifiedBoard :=
  ⟨seed0109, by apply FastValid.valid; decide +kernel⟩

def cert0109r : CertifiedBoard :=
  ⟨seed0109.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0110 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [2,2,1,1,1,2,1,2,2,0,2,1,1],
  [0,2,0,0,1,2,1,0,1,2,1,2,0,0,2],
  [1,2,2,2,0,1,0,2,2,2,2,1,2,2,1,0,1],
  [1,1,0,0,1,1,2,0,2,2,0,1,0,0,0,2,0,0,0]
]

def cert0110n : CertifiedBoard :=
  ⟨seed0110, by apply FastValid.valid; decide +kernel⟩

def cert0110r : CertifiedBoard :=
  ⟨seed0110.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0111 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [2,2,1,1,1,2,2,0,0,2,0,2,2],
  [0,1,0,0,1,2,0,1,2,1,2,2,1,0,1],
  [2,2,2,2,0,2,1,1,2,2,1,2,1,2,1,0,1],
  [1,2,0,0,2,0,1,1,0,0,0,1,0,2,2,2,0,0,0]
]

def cert0111n : CertifiedBoard :=
  ⟨seed0111, by apply FastValid.valid; decide +kernel⟩

def cert0111r : CertifiedBoard :=
  ⟨seed0111.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0112 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [2,2,1,1,1,2,2,0,2,1,2,0,1],
  [1,2,1,2,2,0,0,2,0,2,2,2,1,0,0],
  [1,2,1,0,1,2,2,2,1,1,2,0,0,1,2,1,2],
  [1,1,0,2,0,1,0,1,0,0,2,2,2,0,0,0,0,1,1]
]

def cert0112n : CertifiedBoard :=
  ⟨seed0112, by apply FastValid.valid; decide +kernel⟩

def cert0112r : CertifiedBoard :=
  ⟨seed0112.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0113 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [2,2,1,1,1,2,2,0,2,2,0,0,1],
  [1,2,0,1,2,2,2,2,1,0,2,2,0,0,0],
  [1,0,1,1,2,1,0,1,2,1,2,1,2,2,2,1,2],
  [1,2,0,1,0,0,2,0,2,1,1,0,0,2,0,0,0,1,0]
]

def cert0113n : CertifiedBoard :=
  ⟨seed0113, by apply FastValid.valid; decide +kernel⟩

def cert0113r : CertifiedBoard :=
  ⟨seed0113.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0114 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [2,2,1,1,1,2,2,2,2,0,2,2,0],
  [2,0,0,0,1,2,0,1,0,1,2,1,2,0,1],
  [1,2,2,2,0,2,1,1,2,1,2,2,1,2,1,0,1],
  [0,1,0,0,2,2,1,0,0,2,0,0,1,1,0,2,0,0,0]
]

def cert0114n : CertifiedBoard :=
  ⟨seed0114, by apply FastValid.valid; decide +kernel⟩

def cert0114r : CertifiedBoard :=
  ⟨seed0114.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0115 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [2,2,1,1,2,0,1,1,1,0,0,0,1],
  [2,1,0,1,2,2,2,2,0,2,1,2,2,0,0],
  [1,0,2,2,1,2,1,2,2,0,2,2,2,1,1,2,1],
  [1,2,1,0,0,0,1,0,1,2,0,0,2,0,0,2,0,1,0]
]

def cert0115n : CertifiedBoard :=
  ⟨seed0115, by apply FastValid.valid; decide +kernel⟩

def cert0115r : CertifiedBoard :=
  ⟨seed0115.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0116 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [2,2,1,1,2,0,1,1,1,0,1,0,1],
  [1,2,0,0,1,2,2,1,2,2,0,2,2,0,0],
  [0,2,1,2,2,2,2,2,0,2,2,1,2,1,1,2,1],
  [2,1,0,2,0,1,0,0,2,0,0,1,2,1,0,0,0,0,2]
]

def cert0116n : CertifiedBoard :=
  ⟨seed0116, by apply FastValid.valid; decide +kernel⟩

def cert0116r : CertifiedBoard :=
  ⟨seed0116.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0117 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [2,2,1,1,2,0,1,1,1,0,1,0,1],
  [2,1,0,2,0,2,0,2,1,2,1,2,2,2,0],
  [2,0,1,2,1,1,2,0,0,2,2,2,2,1,2,2,1],
  [1,2,1,0,0,0,0,1,2,2,0,0,1,0,0,2,2,0,0]
]

def cert0117n : CertifiedBoard :=
  ⟨seed0117, by apply FastValid.valid; decide +kernel⟩

def cert0117r : CertifiedBoard :=
  ⟨seed0117.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0118 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [2,2,1,1,2,0,1,1,1,0,1,0,1],
  [2,2,0,0,2,1,2,1,2,2,2,2,0,2,2],
  [1,0,2,2,1,2,0,0,1,2,2,2,1,1,2,1,0],
  [1,2,1,0,0,0,1,2,2,0,2,0,1,0,0,0,2,0,0]
]

def cert0118n : CertifiedBoard :=
  ⟨seed0118, by apply FastValid.valid; decide +kernel⟩

def cert0118r : CertifiedBoard :=
  ⟨seed0118.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0119 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [2,2,1,1,2,1,0,0,1,0,0,2,2],
  [2,2,2,0,2,1,1,1,2,2,2,0,1,0,1],
  [1,2,2,1,2,1,0,1,2,0,1,2,1,2,2,2,0],
  [2,0,0,1,1,0,2,2,1,2,0,2,0,0,0,0,2,0,0]
]

def cert0119n : CertifiedBoard :=
  ⟨seed0119, by apply FastValid.valid; decide +kernel⟩

def cert0119r : CertifiedBoard :=
  ⟨seed0119.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0120 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [2,2,1,1,2,1,0,1,2,0,2,1,0],
  [1,2,0,1,0,0,2,0,2,2,0,1,1,1,2],
  [1,2,2,2,1,2,1,2,2,2,1,2,2,2,0,0,1],
  [1,0,1,2,1,1,0,0,2,0,0,0,1,0,2,2,0,0,0]
]

def cert0120n : CertifiedBoard :=
  ⟨seed0120, by apply FastValid.valid; decide +kernel⟩

def cert0120r : CertifiedBoard :=
  ⟨seed0120.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0121 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [2,2,1,1,2,2,1,1,1,0,1,0,0],
  [2,1,2,0,2,0,0,0,2,2,0,2,1,2,1],
  [1,2,2,2,0,1,1,2,2,2,2,1,0,1,2,1,2],
  [1,2,1,0,2,2,0,0,0,2,0,1,2,0,0,1,0,0,1]
]

def cert0121n : CertifiedBoard :=
  ⟨seed0121, by apply FastValid.valid; decide +kernel⟩

def cert0121r : CertifiedBoard :=
  ⟨seed0121.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0122 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [2,2,1,1,2,2,1,1,1,0,1,0,1],
  [2,2,0,1,2,1,0,2,0,2,2,2,0,0,1],
  [0,1,2,0,2,1,2,0,1,1,2,2,2,1,2,2,2],
  [1,2,1,2,1,0,0,2,2,0,0,0,0,1,0,0,2,0,0]
]

def cert0122n : CertifiedBoard :=
  ⟨seed0122, by apply FastValid.valid; decide +kernel⟩

def cert0122r : CertifiedBoard :=
  ⟨seed0122.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0123 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [2,2,1,1,2,2,1,1,1,0,1,2,2],
  [2,2,2,1,2,1,0,0,2,2,2,2,0,1,0],
  [1,2,1,2,0,0,2,1,2,2,0,0,1,1,2,0,1],
  [1,0,0,0,1,2,1,0,1,0,2,2,0,2,0,2,0,0,0]
]

def cert0123n : CertifiedBoard :=
  ⟨seed0123, by apply FastValid.valid; decide +kernel⟩

def cert0123r : CertifiedBoard :=
  ⟨seed0123.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0124 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [2,2,1,1,2,2,2,2,0,2,2,2,0],
  [2,0,1,1,0,1,0,2,2,1,0,1,2,2,1],
  [2,1,2,1,2,0,2,1,2,1,1,1,2,1,0,0,0],
  [1,2,0,0,0,2,0,0,2,0,0,1,0,0,1,2,2,0,1]
]

def cert0124n : CertifiedBoard :=
  ⟨seed0124, by apply FastValid.valid; decide +kernel⟩

def cert0124r : CertifiedBoard :=
  ⟨seed0124.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0125 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [2,2,1,2,1,2,1,2,2,0,2,2,2],
  [2,2,0,1,0,2,0,0,1,2,2,2,1,0,1],
  [1,2,1,1,2,0,2,2,1,0,1,0,0,2,1,1,1],
  [1,1,2,0,0,2,0,0,0,1,2,2,2,0,1,1,0,0,0]
]

def cert0125n : CertifiedBoard :=
  ⟨seed0125, by apply FastValid.valid; decide +kernel⟩

def cert0125r : CertifiedBoard :=
  ⟨seed0125.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0126 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [2,2,1,2,1,2,2,0,0,2,0,2,2],
  [1,2,1,2,0,0,1,2,2,2,1,1,2,0,1],
  [1,1,0,2,2,2,0,2,1,0,0,1,2,2,1,1,1],
  [2,2,2,0,0,0,2,0,1,1,2,1,0,1,0,1,0,0,0]
]

def cert0126n : CertifiedBoard :=
  ⟨seed0126, by apply FastValid.valid; decide +kernel⟩

def cert0126r : CertifiedBoard :=
  ⟨seed0126.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0127 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [2,2,1,2,2,0,0,1,0,1,2,0,0],
  [2,0,1,1,0,2,2,2,1,2,2,2,2,0,2],
  [1,2,1,1,1,2,1,0,1,2,1,2,2,1,1,2,0],
  [0,2,2,0,2,0,0,2,1,0,0,0,1,0,0,0,2,0,1]
]

def cert0127n : CertifiedBoard :=
  ⟨seed0127, by apply FastValid.valid; decide +kernel⟩

def cert0127r : CertifiedBoard :=
  ⟨seed0127.map List.reverse, by apply FastValid.valid; decide +kernel⟩

end TBoards.Extended
