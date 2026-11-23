import Extended.Batch026

/- Generated from extended_seeds.json. Published seeds 0–4:
   Qiyuan Ma, DOI 10.5281/zenodo.23631079, CC-BY-4.0. -/

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.Extended

def seed0960 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,2,0,2,1,1,1,1,2,0,1],
  [1,1,0,1,1,0,0,1,2,2,0,0,0,1,1],
  [2,1,2,0,1,0,0,2,1,0,0,2,2,0,0,0,2],
  [0,1,1,0,2,0,1,0,1,2,1,0,2,2,1,2,0,2,1]
]

def cert0960n : CertifiedBoard :=
  ⟨seed0960, by apply FastValid.valid; decide +kernel⟩

def cert0960r : CertifiedBoard :=
  ⟨seed0960.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0961 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,2,1,0,0,0,0,1,1,0,2],
  [1,1,0,0,1,2,2,0,0,2,0,1,0,0,2],
  [2,1,2,1,0,1,1,2,0,1,0,1,1,0,2,2,1],
  [0,2,2,0,1,2,0,0,2,1,2,0,2,0,2,1,1,1,1]
]

def cert0961n : CertifiedBoard :=
  ⟨seed0961, by apply FastValid.valid; decide +kernel⟩

def cert0961r : CertifiedBoard :=
  ⟨seed0961.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0962 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,2,1,0,0,0,0,2,1,1,1],
  [0,1,0,0,1,2,1,0,0,2,2,1,2,2,0],
  [2,0,1,1,0,1,0,1,2,0,0,1,1,1,2,0,2],
  [1,1,0,2,0,2,0,1,1,0,2,1,2,0,0,2,2,0,1]
]

def cert0962n : CertifiedBoard :=
  ⟨seed0962, by apply FastValid.valid; decide +kernel⟩

def cert0962r : CertifiedBoard :=
  ⟨seed0962.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0963 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,2,1,0,0,1,0,1,1,0,2],
  [1,0,1,2,0,1,1,0,0,2,1,2,1,2,0],
  [0,2,0,0,0,2,2,0,0,1,1,1,1,2,2,1,0],
  [2,0,2,2,0,1,0,0,0,2,0,1,2,0,2,1,1,0,2]
]

def cert0963n : CertifiedBoard :=
  ⟨seed0963, by apply FastValid.valid; decide +kernel⟩

def cert0963r : CertifiedBoard :=
  ⟨seed0963.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0964 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,2,1,0,0,1,1,0,0,2,1],
  [2,1,2,0,0,0,0,2,1,2,1,0,1,1,0],
  [2,1,1,1,1,0,2,0,1,2,0,1,0,0,2,0,2],
  [1,0,1,2,2,0,1,1,2,0,2,2,0,0,1,0,2,2,1]
]

def cert0964n : CertifiedBoard :=
  ⟨seed0964, by apply FastValid.valid; decide +kernel⟩

def cert0964r : CertifiedBoard :=
  ⟨seed0964.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0965 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,2,1,2,0,1,0,0,0,1,1],
  [1,1,0,1,1,0,0,2,0,2,1,0,2,0,1],
  [0,1,2,1,2,2,0,1,0,2,2,1,0,1,2,0,0],
  [0,0,1,1,1,1,2,0,0,0,2,1,1,0,0,2,2,0,2]
]

def cert0965n : CertifiedBoard :=
  ⟨seed0965, by apply FastValid.valid; decide +kernel⟩

def cert0965r : CertifiedBoard :=
  ⟨seed0965.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0966 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,2,1,2,0,1,0,0,0,1,1],
  [1,1,0,1,1,1,1,0,0,0,2,0,1,2,2],
  [2,2,0,0,1,1,0,0,2,2,0,0,2,1,0,2,1],
  [2,1,1,2,0,2,0,1,0,2,2,1,0,1,2,1,2,0,2]
]

def cert0966n : CertifiedBoard :=
  ⟨seed0966, by apply FastValid.valid; decide +kernel⟩

def cert0966r : CertifiedBoard :=
  ⟨seed0966.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0967 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,2,1,2,1,1,0,0,0,2,1],
  [2,1,0,1,1,1,1,2,2,0,0,2,0,1,1],
  [0,0,1,0,0,0,2,0,1,1,0,2,2,1,2,0,0],
  [1,1,0,1,2,0,1,0,2,1,0,0,1,2,0,2,2,0,2]
]

def cert0967n : CertifiedBoard :=
  ⟨seed0967, by apply FastValid.valid; decide +kernel⟩

def cert0967r : CertifiedBoard :=
  ⟨seed0967.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0968 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,2,1,2,1,1,1,0,0,2,2],
  [0,1,1,1,0,1,0,2,0,1,2,0,0,0,1],
  [2,2,0,0,0,2,1,0,2,1,2,0,1,0,0,1,1],
  [1,1,2,0,2,0,1,1,0,1,2,2,1,0,0,2,2,0,2]
]

def cert0968n : CertifiedBoard :=
  ⟨seed0968, by apply FastValid.valid; decide +kernel⟩

def cert0968r : CertifiedBoard :=
  ⟨seed0968.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0969 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,2,1,2,1,1,1,0,1,1,1],
  [0,0,1,2,0,1,2,0,0,2,0,1,1,0,0],
  [1,1,0,0,0,2,1,0,2,0,2,1,2,0,2,2,0],
  [2,0,1,0,1,0,2,2,0,0,1,1,2,2,1,0,0,0,2]
]

def cert0969n : CertifiedBoard :=
  ⟨seed0969, by apply FastValid.valid; decide +kernel⟩

def cert0969r : CertifiedBoard :=
  ⟨seed0969.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0970 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,2,1,2,1,1,1,0,1,1,1],
  [1,0,1,2,0,1,1,2,2,0,1,1,0,0,2],
  [0,0,0,1,2,0,2,0,0,2,1,2,0,2,0,0,0],
  [1,1,0,2,1,0,2,2,1,0,0,1,0,0,2,2,0,1,0]
]

def cert0970n : CertifiedBoard :=
  ⟨seed0970, by apply FastValid.valid; decide +kernel⟩

def cert0970r : CertifiedBoard :=
  ⟨seed0970.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0971 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,2,1,2,1,1,1,1,0,0,0],
  [0,0,1,1,0,1,2,0,1,1,0,0,2,1,0],
  [1,0,2,0,2,0,0,2,1,2,2,0,1,1,2,0,2],
  [2,1,0,1,2,0,1,0,0,1,0,2,2,0,0,0,2,2,1]
]

def cert0971n : CertifiedBoard :=
  ⟨seed0971, by apply FastValid.valid; decide +kernel⟩

def cert0971r : CertifiedBoard :=
  ⟨seed0971.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0972 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,2,1,2,1,1,1,1,0,0,0],
  [0,0,2,2,0,1,0,1,1,0,0,2,1,2,0],
  [1,0,1,1,2,0,2,0,1,2,0,0,1,2,2,1,0],
  [2,0,2,2,0,0,1,0,2,0,1,1,0,0,0,2,1,0,2]
]

def cert0972n : CertifiedBoard :=
  ⟨seed0972, by apply FastValid.valid; decide +kernel⟩

def cert0972r : CertifiedBoard :=
  ⟨seed0972.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0973 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,2,1,2,1,1,1,1,0,0,0],
  [0,0,2,2,0,1,0,1,1,0,0,2,1,2,0],
  [1,0,1,1,2,0,2,0,1,2,0,0,1,2,2,1,0],
  [2,0,2,2,0,1,1,0,2,0,0,1,0,0,0,2,1,0,2]
]

def cert0973n : CertifiedBoard :=
  ⟨seed0973, by apply FastValid.valid; decide +kernel⟩

def cert0973r : CertifiedBoard :=
  ⟨seed0973.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0974 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,2,1,2,1,1,1,1,0,0,2],
  [1,0,0,0,2,1,0,1,2,0,0,2,1,2,0],
  [0,1,0,2,2,0,1,1,0,0,1,0,1,2,2,1,0],
  [2,0,0,0,1,1,2,0,2,0,2,0,1,1,0,2,2,0,1]
]

def cert0974n : CertifiedBoard :=
  ⟨seed0974, by apply FastValid.valid; decide +kernel⟩

def cert0974r : CertifiedBoard :=
  ⟨seed0974.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0975 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,2,1,2,1,1,1,1,0,1,1],
  [2,1,2,0,1,2,0,1,2,2,0,1,1,0,0],
  [0,0,1,1,2,0,0,0,1,0,0,2,0,2,0,0,2],
  [1,1,0,0,0,2,2,0,2,1,0,1,0,2,2,1,0,2,1]
]

def cert0975n : CertifiedBoard :=
  ⟨seed0975, by apply FastValid.valid; decide +kernel⟩

def cert0975r : CertifiedBoard :=
  ⟨seed0975.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0976 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,2,1,2,1,1,1,1,2,0,1],
  [0,1,1,0,1,1,0,2,0,1,2,2,1,2,0],
  [2,0,0,0,2,1,0,0,2,2,0,0,0,1,0,0,1],
  [0,1,2,0,1,0,1,1,0,0,2,1,0,2,2,0,2,0,2]
]

def cert0976n : CertifiedBoard :=
  ⟨seed0976, by apply FastValid.valid; decide +kernel⟩

def cert0976r : CertifiedBoard :=
  ⟨seed0976.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0977 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,2,1,2,1,1,1,1,2,0,1],
  [2,0,0,2,2,1,0,1,1,0,0,2,2,0,2],
  [0,1,1,0,0,0,1,2,0,0,0,1,1,0,0,2,1],
  [2,1,2,2,0,2,0,1,0,2,1,0,2,0,1,0,1,2,0]
]

def cert0977n : CertifiedBoard :=
  ⟨seed0977, by apply FastValid.valid; decide +kernel⟩

def cert0977r : CertifiedBoard :=
  ⟨seed0977.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0978 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,2,1,2,1,1,1,2,0,1,2],
  [0,1,0,2,2,1,0,1,2,0,2,2,0,0,2],
  [0,0,2,0,1,1,1,0,1,1,0,0,0,1,1,0,0],
  [1,2,0,2,1,0,0,0,2,0,1,0,2,1,2,2,0,0,1]
]

def cert0978n : CertifiedBoard :=
  ⟨seed0978, by apply FastValid.valid; decide +kernel⟩

def cert0978r : CertifiedBoard :=
  ⟨seed0978.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0979 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,2,1,2,2,1,0,0,1,1,0],
  [1,1,0,2,1,1,1,1,2,0,0,1,1,0,2],
  [2,0,1,0,0,0,0,2,0,0,2,0,1,2,1,2,0],
  [1,0,1,0,0,2,2,0,2,1,0,1,2,0,2,2,0,1,1]
]

def cert0979n : CertifiedBoard :=
  ⟨seed0979, by apply FastValid.valid; decide +kernel⟩

def cert0979r : CertifiedBoard :=
  ⟨seed0979.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0980 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,2,1,2,2,1,0,1,1,0,2],
  [0,1,1,1,0,0,0,1,2,0,1,2,1,2,0],
  [1,0,1,1,1,0,2,0,0,2,2,0,0,2,0,1,0],
  [2,0,2,2,0,1,0,0,0,2,1,1,2,0,2,1,0,0,1]
]

def cert0980n : CertifiedBoard :=
  ⟨seed0980, by apply FastValid.valid; decide +kernel⟩

def cert0980r : CertifiedBoard :=
  ⟨seed0980.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0981 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,2,1,2,2,1,0,1,1,1,0],
  [1,0,0,0,1,2,1,1,2,0,1,1,1,0,1],
  [0,0,0,2,0,2,0,1,0,0,2,2,0,1,2,0,2],
  [0,1,1,0,2,1,2,0,0,2,1,0,2,2,0,0,1,0,0]
]

def cert0981n : CertifiedBoard :=
  ⟨seed0981, by apply FastValid.valid; decide +kernel⟩

def cert0981r : CertifiedBoard :=
  ⟨seed0981.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0982 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,2,1,2,2,1,0,1,1,1,0],
  [1,0,0,2,1,1,0,0,0,0,1,2,0,1,0],
  [1,2,1,2,0,1,1,1,0,2,0,0,2,2,0,0,2],
  [1,0,0,1,0,2,2,0,2,0,2,1,0,1,2,0,1,1,2]
]

def cert0982n : CertifiedBoard :=
  ⟨seed0982, by apply FastValid.valid; decide +kernel⟩

def cert0982r : CertifiedBoard :=
  ⟨seed0982.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0983 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,2,1,2,2,1,0,1,2,0,1],
  [1,0,0,2,1,1,1,1,2,1,0,0,1,1,0],
  [0,1,2,0,0,0,0,2,0,2,2,0,2,0,1,1,0],
  [1,0,1,0,2,2,0,1,0,0,1,1,0,2,1,2,0,0,2]
]

def cert0983n : CertifiedBoard :=
  ⟨seed0983, by apply FastValid.valid; decide +kernel⟩

def cert0983r : CertifiedBoard :=
  ⟨seed0983.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0984 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,2,1,2,2,1,0,2,1,1,0],
  [1,0,0,0,1,1,1,1,2,1,0,1,2,0,1],
  [1,0,0,2,2,0,0,2,0,2,2,0,0,0,1,1,0],
  [0,1,1,0,1,2,0,2,0,1,0,0,2,1,2,0,1,0,2]
]

def cert0984n : CertifiedBoard :=
  ⟨seed0984, by apply FastValid.valid; decide +kernel⟩

def cert0984r : CertifiedBoard :=
  ⟨seed0984.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0985 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,2,1,2,2,1,0,2,1,1,1],
  [1,1,0,0,2,2,0,1,2,1,0,1,2,0,2],
  [0,0,2,0,0,1,1,2,0,0,1,0,1,1,0,0,0],
  [0,2,1,2,0,1,0,0,0,2,2,0,1,1,1,0,2,0,2]
]

def cert0985n : CertifiedBoard :=
  ⟨seed0985, by apply FastValid.valid; decide +kernel⟩

def cert0985r : CertifiedBoard :=
  ⟨seed0985.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0986 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,2,1,2,2,1,0,2,1,1,1],
  [2,0,0,1,1,2,0,1,2,1,2,0,0,2,0],
  [1,1,0,0,1,1,0,1,0,0,0,0,2,1,0,0,2],
  [2,2,0,2,2,0,1,0,1,2,0,2,0,1,1,1,0,2,2]
]

def cert0986n : CertifiedBoard :=
  ⟨seed0986, by apply FastValid.valid; decide +kernel⟩

def cert0986r : CertifiedBoard :=
  ⟨seed0986.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0987 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,1,1,0,0,0,1,0,1,1,0,2],
  [0,0,1,2,1,0,0,2,0,2,2,0,1,1,2],
  [1,2,0,1,1,1,1,0,2,0,2,2,1,2,0,0,0],
  [0,1,2,0,0,2,1,2,2,0,1,0,0,2,0,2,1,0,1]
]

def cert0987n : CertifiedBoard :=
  ⟨seed0987, by apply FastValid.valid; decide +kernel⟩

def cert0987r : CertifiedBoard :=
  ⟨seed0987.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0988 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,1,1,0,0,0,1,0,1,1,2,0],
  [1,0,0,0,2,0,2,2,0,2,1,2,2,1,0],
  [1,2,0,0,1,0,0,2,0,1,1,1,1,0,2,1,2],
  [2,0,0,2,0,1,1,0,1,2,0,1,2,1,0,2,2,0,2]
]

def cert0988n : CertifiedBoard :=
  ⟨seed0988, by apply FastValid.valid; decide +kernel⟩

def cert0988r : CertifiedBoard :=
  ⟨seed0988.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0989 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,1,1,0,0,0,1,1,0,0,0,2],
  [1,1,0,2,0,1,0,0,1,2,1,0,1,1,1],
  [2,2,0,0,2,0,0,2,1,2,0,1,0,2,1,2,2],
  [1,2,0,2,0,2,2,0,1,1,1,2,0,2,2,1,0,1,2]
]

def cert0989n : CertifiedBoard :=
  ⟨seed0989, by apply FastValid.valid; decide +kernel⟩

def cert0989r : CertifiedBoard :=
  ⟨seed0989.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0990 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,1,1,0,0,0,1,1,1,0,0,2],
  [1,0,1,2,1,0,0,2,0,1,2,2,0,1,1],
  [0,0,2,2,0,2,1,2,0,1,1,1,2,0,2,0,0],
  [1,1,0,2,2,1,0,1,0,2,1,2,0,2,0,0,0,1,0]
]

def cert0990n : CertifiedBoard :=
  ⟨seed0990, by apply FastValid.valid; decide +kernel⟩

def cert0990r : CertifiedBoard :=
  ⟨seed0990.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0991 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,1,1,0,0,0,1,1,1,0,2,0],
  [2,0,1,2,0,1,0,0,2,1,2,1,2,0,2],
  [1,1,2,0,0,2,1,0,2,0,2,0,1,0,0,1,1],
  [2,2,0,2,2,0,0,0,2,2,1,0,1,1,1,0,1,2,2]
]

def cert0991n : CertifiedBoard :=
  ⟨seed0991, by apply FastValid.valid; decide +kernel⟩

def cert0991r : CertifiedBoard :=
  ⟨seed0991.map List.reverse, by apply FastValid.valid; decide +kernel⟩

end TBoards.Extended
