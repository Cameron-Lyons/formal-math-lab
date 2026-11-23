import Extended.Batch029

/- Generated from extended_seeds.json. Published seeds 0–4:
   Qiyuan Ma, DOI 10.5281/zenodo.23631079, CC-BY-4.0. -/

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.Extended

def seed1056 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,0,0,2,0,1,1,0,0,2],
  [0,2,1,1,2,1,0,1,2,0,2,0,1,0,2],
  [0,1,1,1,1,0,1,0,0,0,0,2,1,2,2,0,1],
  [2,0,2,1,2,0,0,1,1,0,2,0,0,1,2,0,2,2,0]
]

def cert1056n : CertifiedBoard :=
  ⟨seed1056, by apply FastValid.valid; decide +kernel⟩

def cert1056r : CertifiedBoard :=
  ⟨seed1056.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1057 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,0,0,2,0,1,1,1,0,2],
  [1,2,0,1,2,2,0,0,0,2,0,2,1,0,1],
  [0,1,0,0,1,1,2,0,1,0,0,2,1,1,0,1,2],
  [0,2,2,0,2,0,0,0,1,1,1,0,2,1,2,1,2,0,2]
]

def cert1057n : CertifiedBoard :=
  ⟨seed1057, by apply FastValid.valid; decide +kernel⟩

def cert1057r : CertifiedBoard :=
  ⟨seed1057.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1058 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,0,0,2,0,2,1,1,0,2],
  [1,2,0,1,2,1,0,0,1,1,1,1,0,1,1],
  [0,0,0,0,1,1,2,0,0,2,1,2,2,0,2,0,0],
  [1,1,0,2,2,0,1,2,0,1,0,1,0,0,2,0,2,1,2]
]

def cert1058n : CertifiedBoard :=
  ⟨seed1058, by apply FastValid.valid; decide +kernel⟩

def cert1058r : CertifiedBoard :=
  ⟨seed1058.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1059 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,0,0,2,0,2,1,1,1,2],
  [1,2,0,1,2,2,0,0,2,0,2,0,1,1,0],
  [2,0,0,0,1,0,0,1,0,1,1,0,1,1,1,0,2],
  [1,0,2,1,0,0,0,2,2,0,1,2,0,2,1,2,1,2,0]
]

def cert1059n : CertifiedBoard :=
  ⟨seed1059, by apply FastValid.valid; decide +kernel⟩

def cert1059r : CertifiedBoard :=
  ⟨seed1059.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1060 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,0,0,0,0,1,1,0,0],
  [0,0,2,1,1,0,2,1,0,2,0,1,2,0,2],
  [1,1,0,1,2,1,0,0,2,1,2,0,1,0,1,1,2],
  [1,2,2,0,0,2,0,2,2,0,2,0,1,0,0,1,1,1,1]
]

def cert1060n : CertifiedBoard :=
  ⟨seed1060, by apply FastValid.valid; decide +kernel⟩

def cert1060r : CertifiedBoard :=
  ⟨seed1060.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1061 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,0,0,0,0,1,1,0,1],
  [0,0,2,1,1,0,2,2,0,0,1,2,1,0,0],
  [2,0,1,1,2,2,0,2,0,1,0,1,1,1,1,0,2],
  [0,1,2,0,1,0,0,2,0,2,1,0,0,2,0,2,1,2,0]
]

def cert1061n : CertifiedBoard :=
  ⟨seed1061, by apply FastValid.valid; decide +kernel⟩

def cert1061r : CertifiedBoard :=
  ⟨seed1061.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1062 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,0,0,0,0,1,1,1,0],
  [2,1,0,1,2,1,1,0,0,1,1,1,0,0,2],
  [1,0,0,2,2,0,1,2,2,0,2,0,1,0,1,0,2],
  [0,2,1,2,0,2,0,1,1,2,0,0,2,0,2,1,0,2,1]
]

def cert1062n : CertifiedBoard :=
  ⟨seed1062, by apply FastValid.valid; decide +kernel⟩

def cert1062r : CertifiedBoard :=
  ⟨seed1062.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1063 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,0,0,0,2,0,1,1,1],
  [1,0,2,1,1,1,2,0,2,0,2,2,0,1,0],
  [1,1,0,0,1,2,1,0,1,0,0,1,2,0,0,0,2],
  [0,2,0,2,1,0,0,2,1,2,2,0,1,1,0,1,1,0,2]
]

def cert1063n : CertifiedBoard :=
  ⟨seed1063, by apply FastValid.valid; decide +kernel⟩

def cert1063r : CertifiedBoard :=
  ⟨seed1063.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1064 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,0,0,0,2,1,1,1,0],
  [0,0,1,2,0,2,0,2,0,0,1,1,1,0,0],
  [1,1,0,1,0,1,1,2,0,2,2,0,1,2,1,0,2],
  [1,0,0,0,2,1,2,2,0,1,0,0,2,1,0,2,0,1,1]
]

def cert1064n : CertifiedBoard :=
  ⟨seed1064, by apply FastValid.valid; decide +kernel⟩

def cert1064r : CertifiedBoard :=
  ⟨seed1064.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1065 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,0,0,0,2,1,1,1,0],
  [0,1,0,0,2,0,2,1,0,1,1,1,0,0,2],
  [0,0,1,1,0,0,1,1,2,1,2,2,0,2,2,0,1],
  [1,0,2,0,1,2,0,2,1,0,1,0,2,0,1,2,0,0,0]
]

def cert1065n : CertifiedBoard :=
  ⟨seed1065, by apply FastValid.valid; decide +kernel⟩

def cert1065r : CertifiedBoard :=
  ⟨seed1065.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1066 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,0,0,0,2,1,1,1,2],
  [0,1,0,1,1,0,0,2,2,0,1,2,2,0,2],
  [1,0,0,0,1,1,1,0,1,2,0,1,0,2,0,0,1],
  [1,2,1,2,0,2,0,2,1,0,0,2,0,1,1,0,2,1,0]
]

def cert1066n : CertifiedBoard :=
  ⟨seed1066, by apply FastValid.valid; decide +kernel⟩

def cert1066r : CertifiedBoard :=
  ⟨seed1066.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1067 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,0,0,1,0,0,2,0,2],
  [2,1,2,0,1,1,2,0,0,2,1,0,1,0,2],
  [1,1,0,0,0,1,2,1,1,0,1,1,0,0,0,2,1],
  [0,2,1,0,2,2,0,1,2,2,0,2,0,2,0,1,1,1,1]
]

def cert1067n : CertifiedBoard :=
  ⟨seed1067, by apply FastValid.valid; decide +kernel⟩

def cert1067r : CertifiedBoard :=
  ⟨seed1067.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1068 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,0,0,1,0,1,2,0,2],
  [1,0,1,1,1,1,2,0,0,0,2,0,1,1,0],
  [1,2,2,0,1,1,0,0,0,1,0,0,2,0,2,1,2],
  [2,1,0,2,0,1,2,1,0,2,2,0,2,1,1,0,0,2,1]
]

def cert1068n : CertifiedBoard :=
  ⟨seed1068, by apply FastValid.valid; decide +kernel⟩

def cert1068r : CertifiedBoard :=
  ⟨seed1068.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1069 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,0,0,1,0,2,1,1,1],
  [1,1,0,1,1,0,0,2,2,0,0,0,2,1,0],
  [1,0,0,0,1,2,1,2,0,2,0,1,0,1,2,2,0],
  [2,0,2,1,0,2,0,1,1,0,0,2,0,1,1,1,2,0,2]
]

def cert1069n : CertifiedBoard :=
  ⟨seed1069, by apply FastValid.valid; decide +kernel⟩

def cert1069r : CertifiedBoard :=
  ⟨seed1069.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1070 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,0,0,1,1,1,0,1,2],
  [2,1,0,0,0,0,2,2,0,2,1,0,0,2,1],
  [1,0,2,0,0,1,0,2,0,2,1,1,1,0,1,1,0],
  [1,2,1,2,0,2,0,1,1,2,0,1,2,2,0,1,0,0,2]
]

def cert1070n : CertifiedBoard :=
  ⟨seed1070, by apply FastValid.valid; decide +kernel⟩

def cert1070r : CertifiedBoard :=
  ⟨seed1070.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1071 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,0,0,1,1,1,0,2,1],
  [0,1,0,0,0,0,2,0,2,1,0,0,2,0,2],
  [2,1,2,1,0,0,1,1,2,0,1,0,2,1,1,0,1],
  [1,2,0,1,2,2,0,0,2,0,2,2,0,1,1,1,0,1,2]
]

def cert1071n : CertifiedBoard :=
  ⟨seed1071, by apply FastValid.valid; decide +kernel⟩

def cert1071r : CertifiedBoard :=
  ⟨seed1071.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1072 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,0,0,1,1,1,2,0,1],
  [0,1,0,1,1,1,0,0,1,0,0,2,1,2,2],
  [0,2,2,0,1,2,1,0,2,0,1,1,0,0,0,0,2],
  [2,2,0,2,0,2,1,1,0,1,2,0,2,0,0,2,1,0,2]
]

def cert1072n : CertifiedBoard :=
  ⟨seed1072, by apply FastValid.valid; decide +kernel⟩

def cert1072r : CertifiedBoard :=
  ⟨seed1072.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1073 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,0,0,2,0,2,1,1,1],
  [1,1,0,1,1,0,2,1,0,0,1,2,2,0,2],
  [0,0,0,2,0,1,2,0,1,0,1,1,1,2,0,0,0],
  [0,2,2,0,2,0,1,1,0,2,1,2,1,0,0,1,0,0,2]
]

def cert1073n : CertifiedBoard :=
  ⟨seed1073, by apply FastValid.valid; decide +kernel⟩

def cert1073r : CertifiedBoard :=
  ⟨seed1073.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1074 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,0,0,2,1,1,0,0,0],
  [2,0,1,1,1,0,2,0,0,1,0,0,1,0,2],
  [0,1,2,0,1,2,2,0,2,1,2,1,0,1,1,0,1],
  [0,0,2,0,1,1,1,2,0,2,0,2,1,0,0,0,2,2,0]
]

def cert1074n : CertifiedBoard :=
  ⟨seed1074, by apply FastValid.valid; decide +kernel⟩

def cert1074r : CertifiedBoard :=
  ⟨seed1074.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1075 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,0,0,2,1,1,1,0,1],
  [0,1,1,2,0,2,1,2,0,1,2,1,0,0,2],
  [0,1,0,0,0,0,1,1,0,2,0,1,2,2,0,0,1],
  [2,0,1,0,2,1,0,1,1,1,0,0,2,0,2,0,2,2,0]
]

def cert1075n : CertifiedBoard :=
  ⟨seed1075, by apply FastValid.valid; decide +kernel⟩

def cert1075r : CertifiedBoard :=
  ⟨seed1075.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1076 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,0,1,1,0,2,1,1,1],
  [2,0,1,2,0,0,2,0,2,0,0,1,2,1,0],
  [1,0,0,1,1,0,1,1,2,0,2,1,0,0,0,0,2],
  [1,1,1,0,0,2,1,2,2,0,1,0,1,0,2,2,0,2,0]
]

def cert1076n : CertifiedBoard :=
  ⟨seed1076, by apply FastValid.valid; decide +kernel⟩

def cert1076r : CertifiedBoard :=
  ⟨seed1076.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1077 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,0,1,1,1,0,2,0,2],
  [0,1,0,0,0,0,2,0,2,1,0,2,1,0,1],
  [2,2,0,0,2,1,2,0,1,1,1,0,0,1,0,1,1],
  [1,1,2,0,0,1,2,1,1,0,0,2,0,2,2,0,1,2,2]
]

def cert1077n : CertifiedBoard :=
  ⟨seed1077, by apply FastValid.valid; decide +kernel⟩

def cert1077r : CertifiedBoard :=
  ⟨seed1077.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1078 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,0,1,1,1,0,2,1,1],
  [1,1,0,0,1,2,0,0,2,0,0,1,2,1,0],
  [2,0,2,1,0,0,0,0,2,0,1,0,1,1,2,2,0],
  [1,0,1,1,1,0,2,1,2,0,2,2,0,1,0,0,2,0,2]
]

def cert1078n : CertifiedBoard :=
  ⟨seed1078, by apply FastValid.valid; decide +kernel⟩

def cert1078r : CertifiedBoard :=
  ⟨seed1078.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1079 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,0,1,1,1,0,2,1,1],
  [2,0,0,0,1,2,0,1,0,0,0,1,2,1,0],
  [1,0,1,0,0,2,0,2,0,2,1,0,1,1,2,2,0],
  [1,1,0,2,1,2,0,1,1,1,0,0,2,2,0,0,2,0,2]
]

def cert1079n : CertifiedBoard :=
  ⟨seed1079, by apply FastValid.valid; decide +kernel⟩

def cert1079r : CertifiedBoard :=
  ⟨seed1079.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1080 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,0,1,1,1,1,0,1,2],
  [1,0,2,1,1,0,2,2,0,0,2,0,0,0,1],
  [1,2,2,0,2,1,0,0,0,2,1,0,0,1,0,1,0],
  [0,1,2,0,1,1,2,1,2,0,2,0,2,0,1,1,0,0,2]
]

def cert1080n : CertifiedBoard :=
  ⟨seed1080, by apply FastValid.valid; decide +kernel⟩

def cert1080r : CertifiedBoard :=
  ⟨seed1080.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1081 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,0,1,1,1,1,0,2,0],
  [2,0,2,1,1,0,1,0,0,0,2,1,0,0,2],
  [2,0,1,1,2,1,0,1,1,0,0,1,2,2,0,0,0],
  [0,0,2,2,0,0,1,0,2,0,2,0,1,2,0,2,1,2,0]
]

def cert1081n : CertifiedBoard :=
  ⟨seed1081, by apply FastValid.valid; decide +kernel⟩

def cert1081r : CertifiedBoard :=
  ⟨seed1081.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1082 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,0,1,1,1,1,2,0,1],
  [1,0,2,1,1,0,0,1,2,1,0,0,2,0,2],
  [0,2,0,0,0,2,1,0,0,0,1,1,0,1,2,0,2],
  [0,1,0,2,2,0,2,0,0,2,1,2,2,0,1,0,1,1,0]
]

def cert1082n : CertifiedBoard :=
  ⟨seed1082, by apply FastValid.valid; decide +kernel⟩

def cert1082r : CertifiedBoard :=
  ⟨seed1082.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1083 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,0,1,1,1,1,2,0,2],
  [0,1,1,0,0,0,0,1,2,2,0,2,0,0,1],
  [1,0,0,2,0,2,2,0,1,0,1,2,0,1,0,1,1],
  [1,1,0,2,1,1,0,2,1,2,1,0,0,2,0,0,2,1,0]
]

def cert1083n : CertifiedBoard :=
  ⟨seed1083, by apply FastValid.valid; decide +kernel⟩

def cert1083r : CertifiedBoard :=
  ⟨seed1083.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1084 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,0,1,1,1,1,2,0,2],
  [1,0,2,1,1,0,0,1,2,1,0,0,2,0,1],
  [0,2,0,0,0,2,1,0,0,0,1,1,0,1,2,0,2],
  [0,1,0,2,2,0,2,0,0,2,1,2,2,0,1,0,1,1,0]
]

def cert1084n : CertifiedBoard :=
  ⟨seed1084, by apply FastValid.valid; decide +kernel⟩

def cert1084r : CertifiedBoard :=
  ⟨seed1084.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1085 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,0,1,1,1,2,0,2,0],
  [2,0,0,2,1,0,0,1,1,0,0,1,1,1,0],
  [1,0,1,0,1,2,2,0,1,2,1,2,0,0,0,2,0],
  [2,0,2,2,0,2,1,1,0,2,0,1,0,2,1,0,0,0,2]
]

def cert1085n : CertifiedBoard :=
  ⟨seed1085, by apply FastValid.valid; decide +kernel⟩

def cert1085r : CertifiedBoard :=
  ⟨seed1085.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1086 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,0,1,2,1,1,0,0,0],
  [0,0,1,1,1,1,2,0,0,1,1,0,1,0,2],
  [2,1,0,0,2,1,0,0,2,1,2,2,0,0,0,2,1],
  [1,2,0,2,2,0,2,0,2,0,1,0,2,0,1,1,0,1,2]
]

def cert1086n : CertifiedBoard :=
  ⟨seed1086, by apply FastValid.valid; decide +kernel⟩

def cert1086r : CertifiedBoard :=
  ⟨seed1086.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1087 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,2,0,1,2,1,1,0,0,0],
  [0,1,0,2,1,0,1,1,1,1,0,0,2,1,0],
  [1,0,2,0,0,2,1,2,2,0,0,2,2,0,1,0,1],
  [0,0,0,1,1,0,0,1,1,2,0,2,0,2,0,1,2,0,2]
]

def cert1087n : CertifiedBoard :=
  ⟨seed1087, by apply FastValid.valid; decide +kernel⟩

def cert1087r : CertifiedBoard :=
  ⟨seed1087.map List.reverse, by apply FastValid.valid; decide +kernel⟩

end TBoards.Extended
