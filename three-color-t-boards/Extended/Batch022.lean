import Extended.Batch018

/- Generated from extended_seeds.json. Published seeds 0–4:
   Qiyuan Ma, DOI 10.5281/zenodo.23631079, CC-BY-4.0. -/

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.Extended

def seed0704 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,0,2,1,1,1,0,0,0,2],
  [2,1,2,1,0,1,1,1,0,0,2,0,2,2,1],
  [0,2,2,0,1,0,2,0,1,1,0,0,1,0,2,0,0],
  [0,0,1,2,0,1,2,0,2,1,2,2,0,0,0,2,1,0,1]
]

def cert0704n : CertifiedBoard :=
  ⟨seed0704, by apply FastValid.valid; decide +kernel⟩

def cert0704r : CertifiedBoard :=
  ⟨seed0704.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0705 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,0,2,1,1,1,0,0,2,1],
  [1,0,2,0,0,0,2,0,1,1,0,1,0,1,2],
  [1,2,2,0,2,0,2,2,1,0,0,2,1,0,0,0,1],
  [2,1,2,0,1,1,1,0,2,2,0,0,1,2,1,2,0,1,0]
]

def cert0705n : CertifiedBoard :=
  ⟨seed0705, by apply FastValid.valid; decide +kernel⟩

def cert0705r : CertifiedBoard :=
  ⟨seed0705.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0706 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,0,2,1,1,1,0,1,2,0],
  [2,0,2,0,0,0,2,2,0,1,1,0,0,1,0],
  [1,0,2,0,2,1,0,0,2,1,2,1,2,0,1,0,1],
  [1,2,2,0,1,1,1,0,2,2,1,0,0,2,0,0,0,1,2]
]

def cert0706n : CertifiedBoard :=
  ⟨seed0706, by apply FastValid.valid; decide +kernel⟩

def cert0706r : CertifiedBoard :=
  ⟨seed0706.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0707 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,0,2,1,1,1,0,2,0,2],
  [2,0,2,0,0,2,2,1,2,1,0,1,2,0,1],
  [0,2,1,0,1,0,0,0,1,2,0,1,1,0,0,1,0],
  [1,0,2,2,0,0,0,2,0,1,1,1,0,0,2,1,2,2,0]
]

def cert0707n : CertifiedBoard :=
  ⟨seed0707, by apply FastValid.valid; decide +kernel⟩

def cert0707r : CertifiedBoard :=
  ⟨seed0707.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0708 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,0,2,1,1,1,1,0,0,1],
  [1,0,0,0,2,0,2,1,2,2,0,0,1,1,0],
  [0,1,1,0,2,2,1,0,2,0,2,2,0,1,0,0,2],
  [0,2,0,1,2,0,1,2,1,2,0,0,0,2,1,0,1,0,1]
]

def cert0708n : CertifiedBoard :=
  ⟨seed0708, by apply FastValid.valid; decide +kernel⟩

def cert0708r : CertifiedBoard :=
  ⟨seed0708.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0709 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,0,2,1,1,1,1,0,0,1],
  [2,0,0,0,2,0,2,1,2,2,0,1,0,1,0],
  [1,0,1,1,0,0,2,2,1,0,2,2,0,0,1,2,0],
  [0,2,0,1,1,0,2,0,1,2,1,2,0,2,1,0,0,0,2]
]

def cert0709n : CertifiedBoard :=
  ⟨seed0709, by apply FastValid.valid; decide +kernel⟩

def cert0709r : CertifiedBoard :=
  ⟨seed0709.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0710 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,0,2,1,1,1,1,0,0,1],
  [2,1,0,0,2,1,2,0,1,2,1,2,0,0,0],
  [2,2,1,0,0,2,0,0,0,1,0,2,0,1,0,2,1],
  [0,0,2,2,0,2,0,2,2,0,1,1,0,1,1,0,1,2,2]
]

def cert0710n : CertifiedBoard :=
  ⟨seed0710, by apply FastValid.valid; decide +kernel⟩

def cert0710r : CertifiedBoard :=
  ⟨seed0710.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0711 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,0,2,1,1,1,1,0,0,2],
  [0,2,2,0,0,0,2,0,1,2,1,0,0,1,2],
  [1,2,0,2,2,0,2,0,1,0,0,1,0,1,1,0,1],
  [1,2,2,1,0,2,1,2,0,1,1,0,2,0,0,0,2,1,2]
]

def cert0711n : CertifiedBoard :=
  ⟨seed0711, by apply FastValid.valid; decide +kernel⟩

def cert0711r : CertifiedBoard :=
  ⟨seed0711.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0712 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,0,2,1,1,1,1,0,1,2],
  [2,0,2,0,0,0,2,0,1,1,0,0,1,2,0],
  [1,0,2,2,1,2,0,0,2,1,2,1,0,0,0,1,0],
  [1,2,2,0,2,2,0,1,1,0,0,2,1,0,2,0,1,0,1]
]

def cert0712n : CertifiedBoard :=
  ⟨seed0712, by apply FastValid.valid; decide +kernel⟩

def cert0712r : CertifiedBoard :=
  ⟨seed0712.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0713 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,1,0,0,0,0,2,0,2,1],
  [2,1,2,2,0,1,0,1,1,0,0,1,0,1,1],
  [1,1,1,0,2,2,0,0,2,1,2,0,0,2,0,2,0],
  [2,0,1,2,0,1,2,0,2,1,1,1,0,2,2,1,0,0,1]
]

def cert0713n : CertifiedBoard :=
  ⟨seed0713, by apply FastValid.valid; decide +kernel⟩

def cert0713r : CertifiedBoard :=
  ⟨seed0713.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0714 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,1,0,0,0,0,2,1,1,0],
  [0,2,1,2,0,2,1,0,0,1,1,1,1,0,1],
  [1,0,2,2,0,1,0,0,2,0,2,0,1,2,2,0,2],
  [0,1,1,0,1,2,0,0,2,2,1,2,0,1,0,2,0,0,1]
]

def cert0714n : CertifiedBoard :=
  ⟨seed0714, by apply FastValid.valid; decide +kernel⟩

def cert0714r : CertifiedBoard :=
  ⟨seed0714.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0715 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,1,0,0,0,0,2,1,1,1],
  [2,0,0,2,0,1,1,0,0,2,2,1,2,2,0],
  [2,0,2,1,0,1,1,1,0,1,0,0,1,0,2,2,0],
  [1,1,0,2,0,2,0,1,2,0,2,1,2,0,0,1,2,0,1]
]

def cert0715n : CertifiedBoard :=
  ⟨seed0715, by apply FastValid.valid; decide +kernel⟩

def cert0715r : CertifiedBoard :=
  ⟨seed0715.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0716 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,1,0,0,0,2,1,1,0,1],
  [2,1,2,2,0,2,1,0,2,2,1,2,0,0,0],
  [0,0,1,2,0,1,1,1,1,0,2,0,0,2,0,1,0],
  [1,0,0,1,0,0,2,0,1,1,0,1,2,0,2,2,0,2,1]
]

def cert0716n : CertifiedBoard :=
  ⟨seed0716, by apply FastValid.valid; decide +kernel⟩

def cert0716r : CertifiedBoard :=
  ⟨seed0716.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0717 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,1,0,0,0,2,1,1,1,0],
  [1,0,1,1,0,0,0,2,2,0,1,2,2,0,2],
  [0,2,1,2,0,0,1,0,0,1,2,0,2,2,1,0,1],
  [1,1,0,2,0,2,0,1,0,2,1,2,0,0,2,0,1,1,1]
]

def cert0717n : CertifiedBoard :=
  ⟨seed0717, by apply FastValid.valid; decide +kernel⟩

def cert0717r : CertifiedBoard :=
  ⟨seed0717.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0718 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,1,0,0,0,2,1,1,1,0],
  [1,0,1,1,0,2,1,0,0,1,2,2,0,2,1],
  [1,2,0,2,0,1,0,0,0,2,0,0,2,2,0,1,2],
  [2,1,2,0,0,1,1,1,0,2,2,1,2,0,2,0,1,0,1]
]

def cert0718n : CertifiedBoard :=
  ⟨seed0718, by apply FastValid.valid; decide +kernel⟩

def cert0718r : CertifiedBoard :=
  ⟨seed0718.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0719 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,1,0,0,0,2,1,1,1,0],
  [1,0,1,2,0,2,0,1,0,2,2,0,0,0,2],
  [0,2,1,2,2,1,0,1,1,1,0,0,2,2,0,0,1],
  [1,2,0,1,0,2,0,2,0,1,1,0,0,1,2,0,2,1,2]
]

def cert0719n : CertifiedBoard :=
  ⟨seed0719, by apply FastValid.valid; decide +kernel⟩

def cert0719r : CertifiedBoard :=
  ⟨seed0719.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0720 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,1,0,0,0,2,1,1,1,0],
  [1,0,1,2,0,2,1,0,0,2,0,1,1,1,0],
  [2,0,2,1,2,0,1,2,2,0,0,2,2,0,0,0,1],
  [1,0,2,0,1,0,1,1,0,0,1,0,2,2,1,2,0,2,0]
]

def cert0720n : CertifiedBoard :=
  ⟨seed0720, by apply FastValid.valid; decide +kernel⟩

def cert0720r : CertifiedBoard :=
  ⟨seed0720.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0721 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,1,0,0,0,2,1,1,1,0],
  [2,1,2,0,1,2,2,0,0,2,2,0,0,0,1],
  [1,0,1,2,0,1,0,0,2,0,2,0,2,1,0,1,1],
  [1,1,0,2,0,1,1,1,0,0,1,0,2,2,1,2,0,2,1]
]

def cert0721n : CertifiedBoard :=
  ⟨seed0721, by apply FastValid.valid; decide +kernel⟩

def cert0721r : CertifiedBoard :=
  ⟨seed0721.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0722 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,1,0,0,0,2,2,1,1,0],
  [1,0,1,1,1,1,0,0,1,0,2,1,2,2,0],
  [2,0,2,2,0,1,2,0,0,2,1,0,0,0,2,0,1],
  [2,0,2,0,1,2,0,0,1,1,0,1,0,2,1,2,0,2,0]
]

def cert0722n : CertifiedBoard :=
  ⟨seed0722, by apply FastValid.valid; decide +kernel⟩

def cert0722r : CertifiedBoard :=
  ⟨seed0722.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0723 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,1,0,0,1,0,0,2,1,1],
  [0,0,2,0,1,2,2,0,1,2,0,2,0,2,1],
  [2,1,0,0,0,1,1,0,1,1,0,2,2,1,2,0,0],
  [1,1,1,1,0,2,1,2,0,0,0,2,0,2,2,0,1,0,1]
]

def cert0723n : CertifiedBoard :=
  ⟨seed0723, by apply FastValid.valid; decide +kernel⟩

def cert0723r : CertifiedBoard :=
  ⟨seed0723.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0724 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,1,0,0,1,0,0,2,2,1],
  [1,2,0,2,1,1,0,0,2,0,1,0,1,2,0],
  [2,1,2,0,0,0,0,2,2,0,2,0,1,1,1,0,1],
  [2,0,1,1,1,0,2,1,0,2,0,2,1,2,2,0,0,1,2]
]

def cert0724n : CertifiedBoard :=
  ⟨seed0724, by apply FastValid.valid; decide +kernel⟩

def cert0724r : CertifiedBoard :=
  ⟨seed0724.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0725 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,1,0,0,1,1,1,0,2,0],
  [1,2,0,0,0,2,1,0,0,2,0,1,0,0,2],
  [2,0,2,2,0,2,1,1,0,2,0,1,1,1,0,1,2],
  [0,2,1,2,0,2,2,1,2,0,0,0,1,2,2,0,1,0,1]
]

def cert0725n : CertifiedBoard :=
  ⟨seed0725, by apply FastValid.valid; decide +kernel⟩

def cert0725r : CertifiedBoard :=
  ⟨seed0725.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0726 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,1,0,0,1,2,0,2,1,1],
  [0,2,0,0,0,2,1,2,0,2,0,2,2,0,1],
  [1,1,0,0,2,1,0,2,0,1,0,1,1,1,0,0,2],
  [2,1,2,2,0,1,2,0,0,0,1,0,1,1,1,0,2,2,1]
]

def cert0726n : CertifiedBoard :=
  ⟨seed0726, by apply FastValid.valid; decide +kernel⟩

def cert0726r : CertifiedBoard :=
  ⟨seed0726.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0727 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,1,0,0,1,2,0,2,2,1],
  [0,2,1,2,0,1,0,1,1,0,1,0,2,0,1],
  [2,1,0,0,2,1,2,2,0,0,0,2,0,0,0,1,1],
  [1,1,1,1,0,0,2,1,1,0,2,0,1,2,0,2,2,0,2]
]

def cert0727n : CertifiedBoard :=
  ⟨seed0727, by apply FastValid.valid; decide +kernel⟩

def cert0727r : CertifiedBoard :=
  ⟨seed0727.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0728 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,1,0,0,2,0,2,2,1,1],
  [0,0,1,1,0,1,0,0,2,1,2,0,1,2,2],
  [1,1,0,2,1,2,0,2,1,0,0,2,0,0,0,0,1],
  [2,2,0,1,1,1,1,0,1,2,0,1,0,2,0,2,2,0,0]
]

def cert0728n : CertifiedBoard :=
  ⟨seed0728, by apply FastValid.valid; decide +kernel⟩

def cert0728r : CertifiedBoard :=
  ⟨seed0728.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0729 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,1,0,0,2,0,2,2,1,1],
  [0,0,1,1,0,1,0,0,2,1,2,0,1,2,2],
  [1,1,0,2,1,2,0,2,1,0,0,2,0,0,0,0,1],
  [2,2,0,1,1,1,1,0,1,2,0,1,0,2,2,0,2,0,0]
]

def cert0729n : CertifiedBoard :=
  ⟨seed0729, by apply FastValid.valid; decide +kernel⟩

def cert0729r : CertifiedBoard :=
  ⟨seed0729.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0730 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,1,0,0,2,1,1,0,0,1],
  [0,2,0,1,2,0,0,1,0,1,1,1,0,1,0],
  [1,0,2,1,2,0,2,2,0,2,1,2,2,0,0,0,2],
  [1,1,0,0,0,2,0,2,2,1,0,2,0,1,2,0,1,1,1]
]

def cert0730n : CertifiedBoard :=
  ⟨seed0730, by apply FastValid.valid; decide +kernel⟩

def cert0730r : CertifiedBoard :=
  ⟨seed0730.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0731 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,1,0,0,2,1,1,1,0,1],
  [1,0,1,2,2,1,2,0,0,1,1,1,0,0,0],
  [0,0,2,2,0,2,0,2,2,0,2,0,1,0,2,1,0],
  [0,1,1,0,0,0,2,1,2,0,1,0,2,0,0,1,2,0,1]
]

def cert0731n : CertifiedBoard :=
  ⟨seed0731, by apply FastValid.valid; decide +kernel⟩

def cert0731r : CertifiedBoard :=
  ⟨seed0731.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0732 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,1,2,0,1,0,0,0,2,2],
  [1,2,0,1,1,1,1,0,0,0,1,1,0,1,2],
  [2,0,2,0,0,2,1,0,0,2,0,1,2,2,0,0,1],
  [2,2,1,2,0,2,1,1,0,1,0,2,2,0,2,1,0,2,0]
]

def cert0732n : CertifiedBoard :=
  ⟨seed0732, by apply FastValid.valid; decide +kernel⟩

def cert0732r : CertifiedBoard :=
  ⟨seed0732.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0733 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,1,2,0,1,0,0,1,2,0],
  [1,0,1,1,1,1,0,2,2,0,1,0,0,0,1],
  [0,1,2,0,2,0,0,0,2,2,1,2,2,0,2,0,1],
  [2,0,0,2,1,0,1,1,0,2,0,2,1,1,0,0,2,1,0]
]

def cert0733n : CertifiedBoard :=
  ⟨seed0733, by apply FastValid.valid; decide +kernel⟩

def cert0733r : CertifiedBoard :=
  ⟨seed0733.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0734 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,1,2,0,1,0,0,1,2,0],
  [2,0,2,0,0,0,2,0,0,0,2,0,2,1,2],
  [1,0,1,1,1,0,2,2,1,0,1,0,2,1,1,1,0],
  [1,2,2,0,1,1,0,0,2,2,0,1,2,0,2,1,0,0,1]
]

def cert0734n : CertifiedBoard :=
  ⟨seed0734, by apply FastValid.valid; decide +kernel⟩

def cert0734r : CertifiedBoard :=
  ⟨seed0734.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0735 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,1,2,1,2,0,1,0,0,1,2,0],
  [2,0,2,0,0,0,2,0,0,0,2,0,2,1,2],
  [1,0,2,1,1,0,2,2,1,0,1,0,1,1,1,1,0],
  [1,2,2,0,2,1,0,0,2,2,0,1,2,0,1,1,0,0,1]
]

def cert0735n : CertifiedBoard :=
  ⟨seed0735, by apply FastValid.valid; decide +kernel⟩

def cert0735r : CertifiedBoard :=
  ⟨seed0735.map List.reverse, by apply FastValid.valid; decide +kernel⟩

end TBoards.Extended
