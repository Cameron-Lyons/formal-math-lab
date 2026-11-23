import CertifiedFamily

/- Generated from extended_seeds.json. Published seeds 0–4:
   Qiyuan Ma, DOI 10.5281/zenodo.23631079, CC-BY-4.0. -/

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.Extended

def seed0064 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [1,2,2,0,2,0,1,0,1,2,0,0,1],
  [2,2,2,2,0,2,2,2,0,0,1,2,1,1,0],
  [2,2,1,0,1,1,2,1,2,2,1,2,1,1,1,2,2],
  [1,0,0,2,1,0,0,0,0,2,0,1,0,2,2,1,2,0,0]
]

def cert0064n : CertifiedBoard :=
  ⟨seed0064, by apply FastValid.valid; decide +kernel⟩

def cert0064r : CertifiedBoard :=
  ⟨seed0064.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0065 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [1,2,2,0,2,0,1,1,0,1,0,0,2],
  [0,2,1,2,1,2,0,2,2,1,1,2,1,0,0],
  [2,2,2,1,2,2,2,2,1,0,1,2,1,1,1,2,2],
  [2,2,0,0,0,0,1,0,2,2,0,0,1,2,0,0,2,0,1]
]

def cert0065n : CertifiedBoard :=
  ⟨seed0065, by apply FastValid.valid; decide +kernel⟩

def cert0065r : CertifiedBoard :=
  ⟨seed0065.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0066 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [1,2,2,0,2,0,1,1,1,0,1,0,0],
  [1,1,2,1,2,2,0,0,2,2,0,2,1,1,2],
  [2,2,2,1,0,0,2,2,1,2,2,2,2,1,2,1,1],
  [1,2,0,0,1,2,1,0,1,2,0,1,0,2,0,0,0,0,1]
]

def cert0066n : CertifiedBoard :=
  ⟨seed0066, by apply FastValid.valid; decide +kernel⟩

def cert0066r : CertifiedBoard :=
  ⟨seed0066.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0067 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [1,2,2,0,2,1,0,0,1,0,1,2,0],
  [2,2,2,2,0,2,2,1,1,2,0,0,2,0,1],
  [1,2,1,0,1,2,2,1,1,2,1,2,1,2,2,1,2],
  [2,0,0,2,2,2,0,1,1,1,0,2,0,0,0,1,0,0,0]
]

def cert0067n : CertifiedBoard :=
  ⟨seed0067, by apply FastValid.valid; decide +kernel⟩

def cert0067r : CertifiedBoard :=
  ⟨seed0067.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0068 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [1,2,2,0,2,2,1,0,0,0,2,0,0],
  [1,2,1,2,0,1,2,1,2,1,2,2,1,1,2],
  [2,2,1,1,2,2,2,2,2,0,1,0,1,1,1,0,2],
  [0,2,2,0,0,1,0,0,0,2,0,2,1,0,1,2,0,0,1]
]

def cert0068n : CertifiedBoard :=
  ⟨seed0068, by apply FastValid.valid; decide +kernel⟩

def cert0068r : CertifiedBoard :=
  ⟨seed0068.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0069 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [1,2,2,0,2,2,1,1,1,0,1,0,1],
  [2,2,2,2,0,2,0,0,2,1,2,2,1,0,0],
  [1,2,1,0,2,2,2,1,2,1,2,0,1,2,1,1,2],
  [0,0,0,2,0,0,1,0,0,1,1,2,0,1,2,2,0,0,0]
]

def cert0069n : CertifiedBoard :=
  ⟨seed0069, by apply FastValid.valid; decide +kernel⟩

def cert0069r : CertifiedBoard :=
  ⟨seed0069.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0070 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [1,2,2,0,2,2,1,1,1,0,1,0,1],
  [2,2,2,2,0,2,0,0,2,1,2,2,1,0,0],
  [1,2,1,0,2,2,2,1,2,1,2,0,1,2,1,1,2],
  [0,1,2,2,0,1,0,0,0,1,1,2,0,0,0,2,0,0,1]
]

def cert0070n : CertifiedBoard :=
  ⟨seed0070, by apply FastValid.valid; decide +kernel⟩

def cert0070r : CertifiedBoard :=
  ⟨seed0070.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0071 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [1,2,2,0,2,2,1,1,1,2,1,2,2],
  [1,1,0,2,0,0,0,2,0,0,2,2,0,1,1],
  [2,2,2,1,2,1,1,2,1,2,2,2,2,0,1,0,1],
  [2,2,1,0,0,0,1,2,0,0,1,0,1,2,0,2,1,0,0]
]

def cert0071n : CertifiedBoard :=
  ⟨seed0071, by apply FastValid.valid; decide +kernel⟩

def cert0071r : CertifiedBoard :=
  ⟨seed0071.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0072 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [1,2,2,0,2,2,2,1,2,0,0,0,0],
  [1,2,1,2,1,0,1,0,0,1,1,2,2,1,2],
  [2,2,1,1,2,2,0,1,2,1,1,1,0,2,2,2,2],
  [2,2,0,1,0,1,2,0,2,1,0,0,2,0,0,2,0,0,1]
]

def cert0072n : CertifiedBoard :=
  ⟨seed0072, by apply FastValid.valid; decide +kernel⟩

def cert0072r : CertifiedBoard :=
  ⟨seed0072.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0073 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [1,2,2,0,2,2,2,2,0,0,2,0,1],
  [1,1,2,2,0,2,0,0,2,2,1,2,1,0,1],
  [2,2,2,1,2,0,1,1,2,2,1,1,0,2,1,1,1],
  [0,1,0,0,0,1,2,1,2,1,0,1,2,0,0,1,0,0,0]
]

def cert0073n : CertifiedBoard :=
  ⟨seed0073, by apply FastValid.valid; decide +kernel⟩

def cert0073r : CertifiedBoard :=
  ⟨seed0073.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0074 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [1,2,2,1,2,0,0,2,2,0,0,0,1],
  [2,2,2,2,0,2,2,2,0,1,1,2,1,1,0],
  [1,0,1,2,2,1,2,1,2,0,1,2,1,1,1,2,2],
  [2,2,1,0,1,0,2,0,0,2,0,2,1,0,0,1,0,0,0]
]

def cert0074n : CertifiedBoard :=
  ⟨seed0074, by apply FastValid.valid; decide +kernel⟩

def cert0074r : CertifiedBoard :=
  ⟨seed0074.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0075 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [1,2,2,1,2,1,2,0,2,2,2,1,2],
  [0,2,0,1,1,0,1,2,1,0,2,2,0,0,0],
  [1,2,2,1,1,2,0,2,1,1,1,2,2,2,2,0,1],
  [2,2,0,0,1,0,1,2,1,0,0,0,1,0,0,2,0,0,2]
]

def cert0075n : CertifiedBoard :=
  ⟨seed0075, by apply FastValid.valid; decide +kernel⟩

def cert0075r : CertifiedBoard :=
  ⟨seed0075.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0076 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [1,2,2,1,2,1,2,0,2,2,2,1,2],
  [2,2,0,1,1,0,1,2,1,0,0,0,2,0,0],
  [1,2,2,1,1,2,0,2,1,1,1,2,2,2,2,0,1],
  [0,0,2,2,0,0,1,2,1,0,1,0,0,1,0,2,0,0,0]
]

def cert0076n : CertifiedBoard :=
  ⟨seed0076, by apply FastValid.valid; decide +kernel⟩

def cert0076r : CertifiedBoard :=
  ⟨seed0076.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0077 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [1,2,2,1,2,1,2,0,2,2,2,1,2],
  [2,2,0,1,1,0,1,2,1,0,0,2,0,0,0],
  [1,2,2,1,1,2,0,2,1,1,1,2,2,2,2,0,1],
  [0,2,0,0,1,0,1,2,1,0,0,0,1,0,2,2,0,0,2]
]

def cert0077n : CertifiedBoard :=
  ⟨seed0077, by apply FastValid.valid; decide +kernel⟩

def cert0077r : CertifiedBoard :=
  ⟨seed0077.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0078 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [1,2,2,2,1,2,1,1,1,0,1,0,1],
  [1,2,1,0,2,2,2,0,2,2,0,2,0,1,2],
  [2,0,0,2,1,2,1,2,2,0,1,2,2,1,1,2,0],
  [2,2,2,1,0,0,1,0,0,1,1,2,0,0,0,0,2,0,0]
]

def cert0078n : CertifiedBoard :=
  ⟨seed0078, by apply FastValid.valid; decide +kernel⟩

def cert0078r : CertifiedBoard :=
  ⟨seed0078.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0079 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [1,2,2,2,1,2,1,1,1,0,1,0,1],
  [2,2,2,0,1,1,2,0,0,2,0,2,1,0,0],
  [2,1,0,2,2,0,2,2,1,2,2,2,1,2,1,1,2],
  [1,2,2,0,0,2,0,1,0,0,0,0,1,2,0,0,1,2,1]
]

def cert0079n : CertifiedBoard :=
  ⟨seed0079, by apply FastValid.valid; decide +kernel⟩

def cert0079r : CertifiedBoard :=
  ⟨seed0079.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0080 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [1,2,2,2,1,2,1,1,1,2,0,0,1],
  [2,2,2,0,1,2,1,0,0,0,2,2,0,2,0],
  [1,2,2,2,1,1,0,2,1,2,2,1,2,0,1,1,2],
  [2,0,2,0,0,2,2,0,0,0,1,0,1,2,1,0,1,0,0]
]

def cert0080n : CertifiedBoard :=
  ⟨seed0080, by apply FastValid.valid; decide +kernel⟩

def cert0080r : CertifiedBoard :=
  ⟨seed0080.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0081 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [1,2,2,2,1,2,2,2,0,2,0,0,1],
  [2,2,2,0,0,2,1,0,2,0,2,2,1,1,2],
  [1,2,2,1,1,2,1,2,1,2,1,0,1,1,1,0,0],
  [0,1,2,0,1,0,0,0,1,0,1,2,0,0,0,2,2,0,1]
]

def cert0081n : CertifiedBoard :=
  ⟨seed0081, by apply FastValid.valid; decide +kernel⟩

def cert0081r : CertifiedBoard :=
  ⟨seed0081.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0082 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [1,2,2,2,1,2,2,2,0,2,0,0,1],
  [2,2,2,0,0,2,1,0,2,0,2,2,1,1,2],
  [1,2,2,1,1,2,1,2,1,2,1,0,1,1,1,0,0],
  [0,1,2,0,1,0,1,0,0,0,1,2,0,0,0,2,2,0,1]
]

def cert0082n : CertifiedBoard :=
  ⟨seed0082, by apply FastValid.valid; decide +kernel⟩

def cert0082r : CertifiedBoard :=
  ⟨seed0082.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0083 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [1,2,2,2,2,0,1,0,0,0,1,2,2],
  [2,2,1,0,1,2,1,1,1,2,2,0,0,0,1],
  [2,2,1,2,1,0,1,1,2,0,2,2,2,1,2,1,2],
  [1,2,0,1,0,2,0,0,2,2,0,2,0,0,2,1,1,0,0]
]

def cert0083n : CertifiedBoard :=
  ⟨seed0083, by apply FastValid.valid; decide +kernel⟩

def cert0083r : CertifiedBoard :=
  ⟨seed0083.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0084 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [1,2,2,2,2,0,1,1,1,0,1,0,1],
  [1,2,1,0,2,2,0,0,1,2,0,2,2,0,2],
  [2,2,1,1,2,2,2,1,2,1,2,2,1,2,1,0,0],
  [0,2,0,0,2,0,1,2,0,0,0,0,1,0,0,2,1,1,2]
]

def cert0084n : CertifiedBoard :=
  ⟨seed0084, by apply FastValid.valid; decide +kernel⟩

def cert0084r : CertifiedBoard :=
  ⟨seed0084.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0085 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [1,2,2,2,2,0,1,1,2,0,2,2,1],
  [0,2,0,1,0,2,2,1,2,1,2,1,0,0,0],
  [2,1,2,1,1,1,2,2,2,1,1,0,1,2,2,0,2],
  [2,2,0,0,0,1,0,0,2,0,0,2,1,0,1,2,0,0,1]
]

def cert0085n : CertifiedBoard :=
  ⟨seed0085, by apply FastValid.valid; decide +kernel⟩

def cert0085r : CertifiedBoard :=
  ⟨seed0085.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0086 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [1,2,2,2,2,0,1,1,2,0,2,2,1],
  [0,2,0,1,0,2,2,1,2,1,2,1,0,0,0],
  [2,1,2,1,1,1,2,2,2,1,1,0,1,2,2,0,2],
  [2,2,0,0,0,1,0,1,2,0,0,2,1,0,0,2,0,0,1]
]

def cert0086n : CertifiedBoard :=
  ⟨seed0086, by apply FastValid.valid; decide +kernel⟩

def cert0086r : CertifiedBoard :=
  ⟨seed0086.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0087 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [2,2,0,0,2,2,2,1,2,2,2,1,2],
  [1,2,1,1,2,2,2,0,1,2,0,0,0,0,1],
  [1,2,1,0,1,0,1,2,2,0,2,2,1,2,1,1,1],
  [1,1,0,2,0,2,1,0,0,2,0,1,0,0,1,1,2,0,0]
]

def cert0087n : CertifiedBoard :=
  ⟨seed0087, by apply FastValid.valid; decide +kernel⟩

def cert0087r : CertifiedBoard :=
  ⟨seed0087.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0088 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [2,2,0,1,2,0,0,0,1,0,0,2,2],
  [1,2,1,1,2,1,2,2,1,1,2,1,2,0,1],
  [2,2,2,1,2,2,0,0,1,1,1,0,2,2,2,2,1],
  [2,1,0,1,0,1,2,2,0,2,0,2,1,0,0,2,0,0,0]
]

def cert0088n : CertifiedBoard :=
  ⟨seed0088, by apply FastValid.valid; decide +kernel⟩

def cert0088r : CertifiedBoard :=
  ⟨seed0088.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0089 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [2,2,0,1,2,1,0,2,1,2,0,0,1],
  [1,2,2,2,0,2,2,2,1,0,1,2,1,1,2],
  [1,2,2,1,2,0,2,0,0,2,2,2,1,1,1,0,1],
  [0,1,0,0,0,1,1,2,1,2,2,0,1,0,0,2,0,0,0]
]

def cert0089n : CertifiedBoard :=
  ⟨seed0089, by apply FastValid.valid; decide +kernel⟩

def cert0089r : CertifiedBoard :=
  ⟨seed0089.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0090 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [2,2,0,1,2,2,1,1,2,0,0,0,2],
  [1,2,2,1,1,0,1,2,1,2,1,2,1,0,0],
  [0,2,1,2,0,2,2,2,2,2,1,0,1,1,1,2,2],
  [2,2,0,0,2,0,2,2,0,1,0,2,0,0,1,0,0,0,1]
]

def cert0090n : CertifiedBoard :=
  ⟨seed0090, by apply FastValid.valid; decide +kernel⟩

def cert0090r : CertifiedBoard :=
  ⟨seed0090.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0091 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [2,2,0,1,2,2,2,0,2,0,0,0,0],
  [2,1,2,1,0,1,0,1,2,2,2,1,2,1,1],
  [1,2,2,1,1,1,2,0,2,1,0,2,2,2,1,2,1],
  [1,1,2,0,1,0,0,2,0,0,2,2,0,0,1,1,0,0,1]
]

def cert0091n : CertifiedBoard :=
  ⟨seed0091, by apply FastValid.valid; decide +kernel⟩

def cert0091r : CertifiedBoard :=
  ⟨seed0091.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0092 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [2,2,0,2,1,2,1,1,0,0,1,0,2],
  [0,2,2,0,1,2,0,1,2,1,2,2,1,0,1],
  [2,2,1,2,2,2,2,1,1,2,0,0,1,1,1,2,2],
  [1,2,1,0,1,0,0,2,0,2,2,2,0,0,0,2,0,0,0]
]

def cert0092n : CertifiedBoard :=
  ⟨seed0092, by apply FastValid.valid; decide +kernel⟩

def cert0092r : CertifiedBoard :=
  ⟨seed0092.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0093 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [2,2,0,2,1,2,1,1,0,0,2,2,1],
  [2,1,2,1,0,1,0,0,1,2,2,1,0,2,0],
  [1,2,2,2,2,1,2,1,1,2,0,1,2,2,2,0,1],
  [2,0,2,0,0,1,0,1,1,1,2,0,0,0,0,2,2,0,0]
]

def cert0093n : CertifiedBoard :=
  ⟨seed0093, by apply FastValid.valid; decide +kernel⟩

def cert0093r : CertifiedBoard :=
  ⟨seed0093.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0094 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [2,2,0,2,1,2,1,1,1,2,0,2,2],
  [2,2,2,0,0,0,1,1,0,1,2,2,1,0,1],
  [2,0,1,2,1,1,2,2,2,1,2,2,1,2,1,0,0],
  [1,2,0,1,0,2,0,0,1,0,0,2,0,0,0,2,2,2,0]
]

def cert0094n : CertifiedBoard :=
  ⟨seed0094, by apply FastValid.valid; decide +kernel⟩

def cert0094r : CertifiedBoard :=
  ⟨seed0094.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0095 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [2,2,0,2,2,1,2,1,2,0,2,1,2],
  [2,2,2,1,0,0,0,1,0,1,2,1,1,2,2],
  [1,2,0,1,1,1,2,2,2,2,0,0,1,2,1,0,1],
  [1,2,2,0,1,0,0,2,0,0,2,2,1,1,0,2,0,0,0]
]

def cert0095n : CertifiedBoard :=
  ⟨seed0095, by apply FastValid.valid; decide +kernel⟩

def cert0095r : CertifiedBoard :=
  ⟨seed0095.map List.reverse, by apply FastValid.valid; decide +kernel⟩

end TBoards.Extended
