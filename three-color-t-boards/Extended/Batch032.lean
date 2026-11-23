import Extended.Batch028

/- Generated from extended_seeds.json. Published seeds 0–4:
   Qiyuan Ma, DOI 10.5281/zenodo.23631079, CC-BY-4.0. -/

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.Extended

def seed1024 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,0,0,0,0,2,1,1,0,0],
  [0,1,1,1,2,1,0,1,0,2,0,1,0,0,2],
  [2,0,1,1,1,0,2,1,2,2,0,2,1,2,0,0,1],
  [0,0,2,0,2,0,0,1,2,0,1,1,0,1,2,0,2,2,0]
]

def cert1024n : CertifiedBoard :=
  ⟨seed1024, by apply FastValid.valid; decide +kernel⟩

def cert1024r : CertifiedBoard :=
  ⟨seed1024.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1025 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,0,0,0,0,2,1,1,0,1],
  [0,1,1,2,0,0,2,1,0,0,1,2,1,2,2],
  [0,2,2,0,2,0,0,1,1,1,0,1,1,1,0,0,2],
  [2,2,0,1,2,0,2,0,2,0,1,0,2,1,2,0,1,0,2]
]

def cert1025n : CertifiedBoard :=
  ⟨seed1025, by apply FastValid.valid; decide +kernel⟩

def cert1025r : CertifiedBoard :=
  ⟨seed1025.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1026 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,0,0,0,0,2,1,1,0,2],
  [0,1,1,1,2,0,0,1,0,1,1,1,0,0,1],
  [0,2,1,2,2,0,2,2,0,0,2,0,1,1,0,2,1],
  [2,1,0,1,0,0,2,0,1,2,0,2,0,1,2,1,2,0,2]
]

def cert1026n : CertifiedBoard :=
  ⟨seed1026, by apply FastValid.valid; decide +kernel⟩

def cert1026r : CertifiedBoard :=
  ⟨seed1026.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1027 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,0,0,0,0,2,1,1,1,0],
  [2,0,0,1,1,1,0,0,1,1,2,2,0,0,2],
  [1,0,2,2,0,2,1,2,0,1,1,0,0,2,1,0,1],
  [0,1,0,2,0,2,0,1,2,0,2,0,1,0,1,2,1,2,0]
]

def cert1027n : CertifiedBoard :=
  ⟨seed1027, by apply FastValid.valid; decide +kernel⟩

def cert1027r : CertifiedBoard :=
  ⟨seed1027.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1028 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,0,0,0,0,2,1,1,2,0],
  [1,1,0,1,2,1,0,1,0,0,1,1,0,0,2],
  [2,0,1,0,2,0,2,1,2,2,0,1,2,0,0,1,1],
  [0,0,2,1,2,0,1,1,1,1,0,2,0,2,0,2,2,0,0]
]

def cert1028n : CertifiedBoard :=
  ⟨seed1028, by apply FastValid.valid; decide +kernel⟩

def cert1028r : CertifiedBoard :=
  ⟨seed1028.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1029 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,0,0,0,0,2,1,1,2,0],
  [2,0,1,1,1,1,0,2,0,0,1,1,0,1,0],
  [1,0,2,2,0,2,0,1,1,0,0,1,2,0,2,1,2],
  [1,2,2,0,1,2,0,2,1,2,1,0,1,0,0,2,0,0,2]
]

def cert1029n : CertifiedBoard :=
  ⟨seed1029, by apply FastValid.valid; decide +kernel⟩

def cert1029r : CertifiedBoard :=
  ⟨seed1029.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1030 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,0,0,0,0,2,1,1,2,0],
  [2,0,1,1,1,1,0,2,2,0,1,1,0,1,0],
  [0,0,2,1,2,2,0,1,1,0,0,1,2,1,2,0,0],
  [1,0,0,2,0,0,1,2,0,2,1,0,1,0,2,0,2,0,2]
]

def cert1030n : CertifiedBoard :=
  ⟨seed1030, by apply FastValid.valid; decide +kernel⟩

def cert1030r : CertifiedBoard :=
  ⟨seed1030.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1031 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,0,0,0,1,0,0,0,2,1],
  [2,1,0,1,1,0,0,2,2,0,0,1,1,1,1],
  [1,1,2,2,0,1,1,0,2,0,2,0,2,0,0,2,1],
  [2,1,2,1,1,0,1,2,0,1,2,0,1,0,2,1,2,0,2]
]

def cert1031n : CertifiedBoard :=
  ⟨seed1031, by apply FastValid.valid; decide +kernel⟩

def cert1031r : CertifiedBoard :=
  ⟨seed1031.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1032 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,0,0,0,1,0,0,0,2,1],
  [2,1,0,1,2,2,0,2,1,2,0,0,1,1,1],
  [1,1,1,0,1,2,0,2,0,1,1,0,0,2,0,0,2],
  [1,2,0,2,1,2,1,1,0,2,2,0,1,0,2,0,1,1,2]
]

def cert1032n : CertifiedBoard :=
  ⟨seed1032, by apply FastValid.valid; decide +kernel⟩

def cert1032r : CertifiedBoard :=
  ⟨seed1032.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1033 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,0,0,0,1,0,0,2,0,2],
  [0,2,1,1,1,0,2,0,2,0,0,2,1,0,2],
  [0,1,1,2,1,2,0,1,2,0,1,0,1,1,1,0,1],
  [2,2,0,1,2,0,0,0,1,1,0,0,2,2,0,2,1,2,2]
]

def cert1033n : CertifiedBoard :=
  ⟨seed1033, by apply FastValid.valid; decide +kernel⟩

def cert1033r : CertifiedBoard :=
  ⟨seed1033.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1034 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,0,0,0,1,0,1,1,2,0],
  [2,0,0,0,2,1,0,0,1,2,0,0,2,1,2],
  [1,1,0,2,2,0,2,0,1,1,0,0,2,1,1,1,1],
  [1,2,2,0,2,0,1,0,2,0,1,1,0,1,2,1,2,0,2]
]

def cert1034n : CertifiedBoard :=
  ⟨seed1034, by apply FastValid.valid; decide +kernel⟩

def cert1034r : CertifiedBoard :=
  ⟨seed1034.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1035 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,0,0,0,1,0,1,2,0,2],
  [0,1,1,0,0,2,2,0,2,1,2,1,1,0,2],
  [0,2,1,2,0,0,1,1,2,0,1,1,1,1,0,0,0],
  [0,0,2,0,2,1,0,2,0,0,2,0,1,2,2,0,1,0,1]
]

def cert1035n : CertifiedBoard :=
  ⟨seed1035, by apply FastValid.valid; decide +kernel⟩

def cert1035r : CertifiedBoard :=
  ⟨seed1035.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1036 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,0,0,0,1,0,2,0,2,1],
  [2,1,0,0,0,2,2,0,1,1,0,1,1,1,0],
  [0,1,2,0,0,2,1,1,0,1,2,1,2,2,0,0,1],
  [1,0,2,0,1,0,0,2,1,2,0,1,1,1,2,0,2,0,2]
]

def cert1036n : CertifiedBoard :=
  ⟨seed1036, by apply FastValid.valid; decide +kernel⟩

def cert1036r : CertifiedBoard :=
  ⟨seed1036.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1037 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,0,0,0,1,0,2,0,2,1],
  [2,1,0,1,2,0,2,0,1,1,0,0,1,1,1],
  [1,1,1,0,1,2,0,0,2,2,0,1,0,0,2,0,2],
  [1,2,1,2,2,0,0,0,2,1,1,0,2,1,2,0,1,1,2]
]

def cert1037n : CertifiedBoard :=
  ⟨seed1037, by apply FastValid.valid; decide +kernel⟩

def cert1037r : CertifiedBoard :=
  ⟨seed1037.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1038 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,0,0,0,1,0,2,1,1,0],
  [1,0,0,0,2,1,2,0,1,1,0,1,2,1,0],
  [2,0,0,1,0,1,2,0,2,1,2,2,0,1,1,0,2],
  [1,0,0,2,0,2,2,0,1,1,1,1,2,0,0,2,0,2,0]
]

def cert1038n : CertifiedBoard :=
  ⟨seed1038, by apply FastValid.valid; decide +kernel⟩

def cert1038r : CertifiedBoard :=
  ⟨seed1038.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1039 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,0,0,0,1,0,2,1,1,2],
  [0,0,1,1,1,0,1,0,2,1,0,1,1,1,0],
  [1,0,0,2,0,0,2,2,0,1,2,2,0,1,2,0,2],
  [1,2,1,2,0,1,1,0,0,2,0,2,0,2,1,2,0,0,0]
]

def cert1039n : CertifiedBoard :=
  ⟨seed1039, by apply FastValid.valid; decide +kernel⟩

def cert1039r : CertifiedBoard :=
  ⟨seed1039.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1040 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,0,0,0,1,0,2,1,1,2],
  [0,0,1,1,1,0,1,0,2,1,0,1,1,1,0],
  [1,0,0,2,0,0,2,2,0,1,2,2,0,1,2,0,2],
  [1,2,1,2,0,1,1,0,0,2,1,2,0,2,0,2,0,0,0]
]

def cert1040n : CertifiedBoard :=
  ⟨seed1040, by apply FastValid.valid; decide +kernel⟩

def cert1040r : CertifiedBoard :=
  ⟨seed1040.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1041 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,0,0,0,1,0,2,1,1,2],
  [2,0,0,0,2,1,0,0,1,2,0,1,1,1,0],
  [1,0,1,0,1,1,1,0,2,2,0,2,1,2,0,2,0],
  [1,2,1,2,2,0,0,2,0,1,2,0,2,0,1,1,0,0,2]
]

def cert1041n : CertifiedBoard :=
  ⟨seed1041, by apply FastValid.valid; decide +kernel⟩

def cert1041r : CertifiedBoard :=
  ⟨seed1041.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1042 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,0,0,0,1,1,1,0,0,2],
  [2,1,2,0,2,1,0,2,0,0,2,0,0,2,1],
  [0,1,1,0,2,1,1,1,0,1,0,0,0,1,1,2,2],
  [2,2,0,1,0,1,2,1,2,0,1,2,0,2,2,0,2,0,1]
]

def cert1042n : CertifiedBoard :=
  ⟨seed1042, by apply FastValid.valid; decide +kernel⟩

def cert1042r : CertifiedBoard :=
  ⟨seed1042.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1043 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,0,0,0,1,1,1,2,0,1],
  [0,1,0,1,1,1,0,0,2,0,1,0,2,0,2],
  [0,1,1,0,2,1,2,1,2,0,2,2,0,2,1,0,0],
  [0,0,1,2,0,0,0,2,0,0,2,1,1,0,1,2,2,0,1]
]

def cert1043n : CertifiedBoard :=
  ⟨seed1043, by apply FastValid.valid; decide +kernel⟩

def cert1043r : CertifiedBoard :=
  ⟨seed1043.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1044 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,0,0,0,1,1,1,2,0,2],
  [2,0,0,0,2,1,2,0,1,2,0,2,1,0,2],
  [0,1,1,0,2,1,1,1,0,1,0,1,0,0,2,0,1],
  [0,2,2,0,0,1,2,1,2,2,0,1,1,0,0,2,0,2,0]
]

def cert1044n : CertifiedBoard :=
  ⟨seed1044, by apply FastValid.valid; decide +kernel⟩

def cert1044r : CertifiedBoard :=
  ⟨seed1044.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1045 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,0,0,0,1,1,2,0,2,0],
  [0,2,1,1,1,0,2,0,2,0,2,1,0,0,2],
  [1,2,0,1,2,0,1,0,1,1,0,1,1,1,0,0,2],
  [2,0,0,0,1,0,2,2,0,0,2,1,2,1,2,2,0,1,2]
]

def cert1045n : CertifiedBoard :=
  ⟨seed1045, by apply FastValid.valid; decide +kernel⟩

def cert1045r : CertifiedBoard :=
  ⟨seed1045.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1046 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,0,0,0,2,0,1,1,0,2],
  [0,1,1,1,2,2,0,0,2,0,2,1,2,0,2],
  [2,0,1,1,1,0,0,1,0,0,0,1,2,1,1,0,1],
  [0,2,1,2,0,1,0,2,0,2,1,0,1,2,0,0,2,2,0]
]

def cert1046n : CertifiedBoard :=
  ⟨seed1046, by apply FastValid.valid; decide +kernel⟩

def cert1046r : CertifiedBoard :=
  ⟨seed1046.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1047 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,0,0,0,2,0,2,1,1,1],
  [2,0,0,1,1,0,2,2,0,1,1,2,2,0,2],
  [1,1,0,0,1,1,1,0,1,2,0,1,0,0,0,2,0],
  [2,0,0,2,1,2,1,2,0,1,2,0,2,1,0,1,0,2,0]
]

def cert1047n : CertifiedBoard :=
  ⟨seed1047, by apply FastValid.valid; decide +kernel⟩

def cert1047r : CertifiedBoard :=
  ⟨seed1047.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1048 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,0,0,0,2,0,2,1,1,2],
  [2,0,0,0,1,0,1,0,2,0,1,2,1,2,0],
  [0,1,1,0,0,2,1,2,2,0,1,1,1,1,0,0,1],
  [1,2,0,0,2,1,0,1,1,0,2,2,0,1,2,0,2,0,2]
]

def cert1048n : CertifiedBoard :=
  ⟨seed1048, by apply FastValid.valid; decide +kernel⟩

def cert1048r : CertifiedBoard :=
  ⟨seed1048.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1049 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,0,0,0,2,1,1,0,0,0],
  [0,0,1,1,2,1,2,0,1,2,0,2,0,0,2],
  [1,1,0,1,1,1,1,0,2,1,2,0,2,1,0,2,0],
  [2,0,0,2,2,0,1,2,2,0,2,0,1,0,1,0,0,1,1]
]

def cert1049n : CertifiedBoard :=
  ⟨seed1049, by apply FastValid.valid; decide +kernel⟩

def cert1049r : CertifiedBoard :=
  ⟨seed1049.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1050 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,0,0,0,2,1,1,0,0,0],
  [1,1,0,1,1,0,2,1,0,2,0,0,2,0,2],
  [1,2,1,2,0,1,0,1,2,2,0,1,0,0,1,1,2],
  [0,0,2,0,2,1,2,0,1,2,0,2,2,0,0,1,1,1,1]
]

def cert1050n : CertifiedBoard :=
  ⟨seed1050, by apply FastValid.valid; decide +kernel⟩

def cert1050r : CertifiedBoard :=
  ⟨seed1050.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1051 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,0,0,0,2,1,1,2,0,2],
  [1,1,0,0,0,2,0,0,1,2,0,2,0,2,1],
  [0,1,1,0,2,1,0,2,2,0,0,1,0,1,1,1,1],
  [2,1,2,1,2,0,1,0,1,1,0,0,2,0,1,2,2,0,1]
]

def cert1051n : CertifiedBoard :=
  ⟨seed1051, by apply FastValid.valid; decide +kernel⟩

def cert1051r : CertifiedBoard :=
  ⟨seed1051.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1052 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,0,0,2,0,0,0,1,1,2],
  [0,2,1,1,1,0,1,1,0,0,2,0,1,0,0],
  [0,0,1,2,1,2,0,1,1,1,0,2,1,2,2,0,2],
  [1,2,0,0,0,2,0,2,2,0,2,1,0,1,2,0,1,0,2]
]

def cert1052n : CertifiedBoard :=
  ⟨seed1052, by apply FastValid.valid; decide +kernel⟩

def cert1052r : CertifiedBoard :=
  ⟨seed1052.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1053 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,0,0,2,0,0,1,1,2,0],
  [1,1,0,1,2,2,0,2,1,0,1,1,0,0,2],
  [0,2,0,1,1,1,1,0,0,0,0,1,2,1,2,0,2],
  [2,0,0,2,0,2,1,2,0,1,0,2,2,0,1,0,2,1,1]
]

def cert1053n : CertifiedBoard :=
  ⟨seed1053, by apply FastValid.valid; decide +kernel⟩

def cert1053r : CertifiedBoard :=
  ⟨seed1053.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1054 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,0,0,2,0,0,1,2,0,2],
  [0,1,0,2,1,2,0,0,2,2,0,1,1,0,1],
  [2,1,2,1,0,0,0,0,1,1,1,0,1,1,0,2,1],
  [1,1,2,0,1,0,0,2,0,1,2,2,0,2,0,2,1,1,1]
]

def cert1054n : CertifiedBoard :=
  ⟨seed1054, by apply FastValid.valid; decide +kernel⟩

def cert1054r : CertifiedBoard :=
  ⟨seed1054.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed1055 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,2,1,0,0,2,0,0,1,2,0,2],
  [0,2,1,1,1,0,1,0,0,2,0,2,1,0,2],
  [0,1,1,2,1,2,0,1,2,0,0,0,1,1,1,0,1],
  [2,1,2,2,0,1,1,0,0,0,2,2,0,2,0,1,0,2,1]
]

def cert1055n : CertifiedBoard :=
  ⟨seed1055, by apply FastValid.valid; decide +kernel⟩

def cert1055r : CertifiedBoard :=
  ⟨seed1055.map List.reverse, by apply FastValid.valid; decide +kernel⟩

end TBoards.Extended
