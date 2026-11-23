import Extended.Batch015

/- Generated from extended_seeds.json. Published seeds 0–4:
   Qiyuan Ma, DOI 10.5281/zenodo.23631079, CC-BY-4.0. -/

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.Extended

def seed0608 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,0,0,2,0,1,0,2,1,1,2],
  [0,0,1,1,1,0,0,2,1,0,2,2,0,0,1],
  [0,2,2,0,1,2,0,1,1,1,0,1,2,0,2,0,2],
  [1,2,0,2,0,0,0,0,2,1,2,1,2,2,1,0,1,0,0]
]

def cert0608n : CertifiedBoard :=
  ⟨seed0608, by apply FastValid.valid; decide +kernel⟩

def cert0608r : CertifiedBoard :=
  ⟨seed0608.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0609 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,0,0,2,0,1,1,2,0,2,0],
  [1,0,2,1,2,0,2,1,2,1,0,2,2,1,0],
  [2,0,1,0,0,0,2,1,1,1,1,0,0,1,2,0,0],
  [0,0,0,1,0,1,1,0,1,2,2,0,0,2,0,2,2,0,1]
]

def cert0609n : CertifiedBoard :=
  ⟨seed0609, by apply FastValid.valid; decide +kernel⟩

def cert0609r : CertifiedBoard :=
  ⟨seed0609.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0610 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,0,0,2,0,1,2,0,2,2,1],
  [2,2,0,1,0,1,0,2,1,0,1,1,1,2,2],
  [0,0,0,2,2,0,0,0,1,2,0,1,1,1,0,0,1],
  [2,1,0,0,2,1,1,0,2,0,2,0,2,1,2,1,2,0,0]
]

def cert0610n : CertifiedBoard :=
  ⟨seed0610, by apply FastValid.valid; decide +kernel⟩

def cert0610r : CertifiedBoard :=
  ⟨seed0610.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0611 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,0,0,2,1,1,1,1,2,0,1],
  [1,2,0,1,1,0,1,2,1,2,2,0,2,0,2],
  [2,0,0,0,1,2,0,0,0,1,0,2,1,0,0,2,0],
  [0,2,2,0,1,1,0,1,0,2,1,0,0,2,0,2,2,1,2]
]

def cert0611n : CertifiedBoard :=
  ⟨seed0611, by apply FastValid.valid; decide +kernel⟩

def cert0611r : CertifiedBoard :=
  ⟨seed0611.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0612 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,0,0,2,1,1,1,1,2,0,1],
  [2,1,2,2,0,0,2,0,1,2,1,0,1,1,0],
  [1,0,0,0,0,2,0,2,2,0,0,1,0,2,0,2,1],
  [1,2,0,1,0,0,1,2,0,2,1,0,1,1,0,2,2,1,2]
]

def cert0612n : CertifiedBoard :=
  ⟨seed0612, by apply FastValid.valid; decide +kernel⟩

def cert0612r : CertifiedBoard :=
  ⟨seed0612.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0613 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,0,0,2,1,1,1,1,2,0,2],
  [0,2,1,2,0,0,2,0,2,0,1,0,1,0,0],
  [0,0,1,2,2,1,0,2,2,0,1,1,0,1,2,0,1],
  [2,0,2,0,0,0,1,1,0,2,1,2,1,0,0,0,2,2,0]
]

def cert0613n : CertifiedBoard :=
  ⟨seed0613, by apply FastValid.valid; decide +kernel⟩

def cert0613r : CertifiedBoard :=
  ⟨seed0613.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0614 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,0,0,2,1,1,1,1,2,0,2],
  [2,0,1,2,0,2,2,1,2,2,0,2,1,0,0],
  [0,0,1,1,0,1,0,2,0,0,0,2,0,1,1,0,1],
  [0,2,1,2,1,0,0,0,1,2,0,0,2,2,0,1,0,2,0]
]

def cert0614n : CertifiedBoard :=
  ⟨seed0614, by apply FastValid.valid; decide +kernel⟩

def cert0614r : CertifiedBoard :=
  ⟨seed0614.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0615 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,0,0,2,1,1,1,1,2,0,2],
  [2,0,1,2,0,2,2,1,2,2,0,2,1,0,0],
  [0,0,1,1,0,1,0,2,0,0,0,2,0,1,1,0,1],
  [0,2,1,2,1,0,0,0,2,2,0,0,1,2,0,1,0,2,0]
]

def cert0615n : CertifiedBoard :=
  ⟨seed0615, by apply FastValid.valid; decide +kernel⟩

def cert0615r : CertifiedBoard :=
  ⟨seed0615.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0616 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,0,0,2,1,1,1,2,0,2,1],
  [1,0,1,2,2,0,2,2,0,2,0,1,1,1,0],
  [2,1,0,0,0,2,0,0,0,1,0,2,1,2,0,0,1],
  [0,1,2,1,0,2,2,1,2,0,1,1,0,1,0,0,2,0,1]
]

def cert0616n : CertifiedBoard :=
  ⟨seed0616, by apply FastValid.valid; decide +kernel⟩

def cert0616r : CertifiedBoard :=
  ⟨seed0616.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0617 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,1,0,0,0,0,2,1,1,0,2],
  [0,2,1,2,0,1,0,2,2,0,2,1,0,0,1],
  [2,0,1,2,2,1,2,1,0,0,2,0,1,1,0,1,0],
  [1,0,1,1,1,2,0,2,2,0,0,2,0,2,0,0,1,2,0]
]

def cert0617n : CertifiedBoard :=
  ⟨seed0617, by apply FastValid.valid; decide +kernel⟩

def cert0617r : CertifiedBoard :=
  ⟨seed0617.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0618 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,1,0,0,0,1,0,0,2,1,1],
  [2,0,1,2,1,2,0,2,0,0,1,1,2,0,1],
  [0,2,0,0,2,2,0,2,2,1,0,1,1,1,0,2,0],
  [1,1,0,2,1,2,0,1,0,1,2,2,0,2,1,0,0,0,2]
]

def cert0618n : CertifiedBoard :=
  ⟨seed0618, by apply FastValid.valid; decide +kernel⟩

def cert0618r : CertifiedBoard :=
  ⟨seed0618.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0619 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,1,0,0,0,1,0,2,0,2,1],
  [2,0,2,0,2,1,0,2,1,0,0,0,1,2,2],
  [2,1,1,0,1,0,0,2,0,1,2,0,1,1,1,2,0],
  [2,2,1,2,1,2,0,0,2,2,0,0,2,2,0,1,1,0,1]
]

def cert0619n : CertifiedBoard :=
  ⟨seed0619, by apply FastValid.valid; decide +kernel⟩

def cert0619r : CertifiedBoard :=
  ⟨seed0619.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0620 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,1,0,0,0,1,1,0,1,2,0],
  [1,0,2,1,2,1,2,0,0,2,0,1,0,0,1],
  [2,0,2,1,1,1,2,2,1,0,0,2,2,0,2,0,0],
  [0,0,0,2,0,1,2,0,2,1,0,1,0,2,2,0,1,1,0]
]

def cert0620n : CertifiedBoard :=
  ⟨seed0620, by apply FastValid.valid; decide +kernel⟩

def cert0620r : CertifiedBoard :=
  ⟨seed0620.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0621 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,1,0,0,0,1,2,0,2,2,1],
  [0,2,1,2,0,0,1,0,1,1,0,2,1,1,1],
  [2,1,0,1,0,0,2,2,0,2,1,0,0,0,2,0,2],
  [1,1,2,2,0,1,1,0,2,0,1,2,1,2,0,0,2,0,1]
]

def cert0621n : CertifiedBoard :=
  ⟨seed0621, by apply FastValid.valid; decide +kernel⟩

def cert0621r : CertifiedBoard :=
  ⟨seed0621.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0622 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,1,0,0,0,2,1,1,2,0,1],
  [2,0,2,0,0,2,0,0,2,0,1,0,1,1,1],
  [1,1,0,0,1,0,2,2,0,1,2,0,2,1,2,2,0],
  [0,1,2,1,0,1,1,0,2,1,2,0,2,2,1,0,0,0,1]
]

def cert0622n : CertifiedBoard :=
  ⟨seed0622, by apply FastValid.valid; decide +kernel⟩

def cert0622r : CertifiedBoard :=
  ⟨seed0622.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0623 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,1,0,0,2,0,0,0,2,1,1],
  [0,2,0,1,2,0,2,2,1,0,0,2,2,0,2],
  [1,1,0,2,1,0,1,0,0,1,0,1,1,2,0,1,2],
  [1,2,1,2,0,2,1,2,2,0,0,0,1,1,1,0,2,0,1]
]

def cert0623n : CertifiedBoard :=
  ⟨seed0623, by apply FastValid.valid; decide +kernel⟩

def cert0623r : CertifiedBoard :=
  ⟨seed0623.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0624 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,1,0,0,2,1,0,0,0,2,2],
  [2,2,0,2,0,1,0,0,1,0,2,0,1,2,0],
  [2,1,1,2,0,2,2,0,0,1,1,0,1,1,1,0,1],
  [2,0,1,2,2,1,0,2,0,2,1,2,1,2,0,0,0,2,1]
]

def cert0624n : CertifiedBoard :=
  ⟨seed0624, by apply FastValid.valid; decide +kernel⟩

def cert0624r : CertifiedBoard :=
  ⟨seed0624.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0625 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,1,0,0,2,1,0,2,2,1,1],
  [2,0,2,0,2,1,2,0,1,1,0,1,2,0,1],
  [1,1,0,0,1,0,0,0,0,1,2,2,0,0,2,2,0],
  [2,1,2,1,0,1,0,2,0,1,1,1,2,0,0,2,0,2,1]
]

def cert0625n : CertifiedBoard :=
  ⟨seed0625, by apply FastValid.valid; decide +kernel⟩

def cert0625r : CertifiedBoard :=
  ⟨seed0625.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0626 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,1,1,0,0,0,0,1,2,0,1],
  [2,1,2,2,0,1,1,0,2,0,1,0,0,2,0],
  [2,0,2,1,1,0,1,2,0,2,2,0,0,1,0,2,1],
  [1,0,1,1,2,1,2,0,2,0,0,2,1,0,0,2,2,1,0]
]

def cert0626n : CertifiedBoard :=
  ⟨seed0626, by apply FastValid.valid; decide +kernel⟩

def cert0626r : CertifiedBoard :=
  ⟨seed0626.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0627 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,1,1,0,0,0,0,1,2,0,2],
  [0,2,2,0,1,2,0,1,1,0,1,1,0,0,2],
  [0,2,1,1,2,0,2,0,0,2,1,2,1,0,2,0,1],
  [0,0,2,1,2,2,1,0,0,1,0,1,0,2,0,2,2,0,0]
]

def cert0627n : CertifiedBoard :=
  ⟨seed0627, by apply FastValid.valid; decide +kernel⟩

def cert0627r : CertifiedBoard :=
  ⟨seed0627.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0628 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,1,1,0,0,0,0,1,2,0,2],
  [1,0,2,1,2,0,0,1,1,0,1,1,2,0,1],
  [2,0,2,2,1,0,2,0,1,2,2,0,1,0,0,2,0],
  [0,2,0,0,2,2,0,2,1,2,1,1,0,0,2,1,0,1,0]
]

def cert0628n : CertifiedBoard :=
  ⟨seed0628, by apply FastValid.valid; decide +kernel⟩

def cert0628r : CertifiedBoard :=
  ⟨seed0628.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0629 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,1,1,0,0,0,0,2,0,1,2],
  [2,1,2,2,0,1,1,0,1,0,2,2,0,0,1],
  [1,0,1,2,0,2,0,2,0,0,2,1,1,0,0,2,1],
  [1,2,0,1,0,2,2,1,0,0,1,1,2,1,2,0,2,1,0]
]

def cert0629n : CertifiedBoard :=
  ⟨seed0629, by apply FastValid.valid; decide +kernel⟩

def cert0629r : CertifiedBoard :=
  ⟨seed0629.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0630 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,1,1,0,0,0,0,2,0,2,1],
  [2,0,0,2,0,2,1,0,0,2,1,1,0,1,0],
  [1,0,0,1,1,0,1,2,0,2,2,1,2,1,2,2,0],
  [2,1,0,2,0,1,2,0,0,1,0,2,2,0,1,1,2,0,1]
]

def cert0630n : CertifiedBoard :=
  ⟨seed0630, by apply FastValid.valid; decide +kernel⟩

def cert0630r : CertifiedBoard :=
  ⟨seed0630.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0631 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,1,1,0,0,0,0,2,1,1,0],
  [1,0,1,2,2,0,1,1,0,0,1,2,1,0,2],
  [0,2,0,1,1,2,0,2,1,2,0,0,2,0,2,0,2],
  [0,2,2,1,2,0,0,1,0,1,0,2,1,0,0,2,2,0,1]
]

def cert0631n : CertifiedBoard :=
  ⟨seed0631, by apply FastValid.valid; decide +kernel⟩

def cert0631r : CertifiedBoard :=
  ⟨seed0631.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0632 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,1,1,0,0,0,0,2,2,1,1],
  [0,2,2,0,2,1,0,1,0,2,0,1,2,0,1],
  [1,1,0,2,1,2,0,0,2,0,2,0,1,1,0,0,2],
  [0,1,2,1,0,1,0,0,1,1,2,0,2,1,2,2,0,0,1]
]

def cert0632n : CertifiedBoard :=
  ⟨seed0632, by apply FastValid.valid; decide +kernel⟩

def cert0632r : CertifiedBoard :=
  ⟨seed0632.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0633 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,1,1,0,0,0,0,2,2,1,1],
  [1,0,0,2,1,2,2,0,1,1,0,1,2,0,1],
  [2,0,2,0,0,1,1,0,2,2,0,0,1,2,0,2,0],
  [1,1,2,0,2,1,2,1,0,2,0,1,0,1,0,0,2,1,0]
]

def cert0633n : CertifiedBoard :=
  ⟨seed0633, by apply FastValid.valid; decide +kernel⟩

def cert0633r : CertifiedBoard :=
  ⟨seed0633.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0634 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,1,1,0,0,0,0,2,2,1,1],
  [2,0,1,2,2,0,2,0,2,2,0,2,1,2,0],
  [1,1,0,0,2,0,1,0,1,1,2,0,0,1,0,0,1],
  [2,0,1,1,0,1,2,0,0,2,1,0,2,1,2,1,0,2,0]
]

def cert0634n : CertifiedBoard :=
  ⟨seed0634, by apply FastValid.valid; decide +kernel⟩

def cert0634r : CertifiedBoard :=
  ⟨seed0634.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0635 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,1,1,0,0,0,0,2,2,1,1],
  [2,2,0,1,2,2,0,0,1,0,0,1,2,0,0],
  [1,1,0,2,1,2,0,2,0,1,1,0,1,0,0,2,2],
  [0,0,2,0,2,1,0,1,1,2,0,2,1,2,1,0,2,0,1]
]

def cert0635n : CertifiedBoard :=
  ⟨seed0635, by apply FastValid.valid; decide +kernel⟩

def cert0635r : CertifiedBoard :=
  ⟨seed0635.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0636 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,1,1,0,0,0,2,0,1,2,0],
  [2,1,2,1,2,0,0,2,0,0,2,2,0,2,1],
  [1,0,0,0,1,1,0,1,1,2,0,2,2,1,0,1,0],
  [2,0,1,0,0,1,2,2,0,2,1,1,0,2,1,0,2,0,1]
]

def cert0636n : CertifiedBoard :=
  ⟨seed0636, by apply FastValid.valid; decide +kernel⟩

def cert0636r : CertifiedBoard :=
  ⟨seed0636.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0637 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,1,1,0,0,0,2,1,1,0,0],
  [1,0,2,0,1,2,2,0,2,2,1,2,1,0,1],
  [0,1,1,0,2,0,0,1,2,0,2,0,2,2,0,1,0],
  [0,0,2,1,0,0,2,1,2,0,1,0,1,1,2,0,0,0,1]
]

def cert0637n : CertifiedBoard :=
  ⟨seed0637, by apply FastValid.valid; decide +kernel⟩

def cert0637r : CertifiedBoard :=
  ⟨seed0637.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0638 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,1,1,0,0,0,2,1,1,0,1],
  [2,0,1,2,0,0,0,1,0,1,2,1,2,0,1],
  [0,0,2,2,0,2,1,0,2,1,2,2,1,0,0,2,0],
  [0,1,1,0,2,2,0,1,0,0,1,1,2,0,2,0,2,0,0]
]

def cert0638n : CertifiedBoard :=
  ⟨seed0638, by apply FastValid.valid; decide +kernel⟩

def cert0638r : CertifiedBoard :=
  ⟨seed0638.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0639 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,1,1,0,0,0,2,1,1,0,2],
  [0,0,1,2,2,0,1,1,0,1,2,1,2,0,1],
  [2,2,0,1,1,2,0,2,1,0,0,0,2,0,2,0,0],
  [0,2,2,1,2,0,2,0,0,1,0,2,1,0,1,0,0,2,2]
]

def cert0639n : CertifiedBoard :=
  ⟨seed0639, by apply FastValid.valid; decide +kernel⟩

def cert0639r : CertifiedBoard :=
  ⟨seed0639.map List.reverse, by apply FastValid.valid; decide +kernel⟩

end TBoards.Extended
