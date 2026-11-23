import CertifiedFamily

/- Generated from extended_seeds.json. Published seeds 0–4:
   Qiyuan Ma, DOI 10.5281/zenodo.23631079, CC-BY-4.0. -/

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.Extended

def seed0032 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [1,2,0,2,2,2,0,1,2,2,0,0,2],
  [2,1,2,2,1,0,1,1,2,1,2,1,2,2,1],
  [0,2,0,2,2,2,1,1,1,0,2,1,1,2,0,0,1],
  [2,2,2,0,1,0,0,0,0,2,0,0,1,0,1,2,1,0,0]
]

def cert0032n : CertifiedBoard :=
  ⟨seed0032, by apply FastValid.valid; decide +kernel⟩

def cert0032r : CertifiedBoard :=
  ⟨seed0032.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0033 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [1,2,0,2,2,2,2,0,2,1,2,1,2],
  [1,2,2,1,0,2,0,1,2,1,0,0,2,0,0],
  [1,1,2,1,1,1,2,0,0,2,2,1,2,2,2,1,1],
  [2,2,0,0,0,0,1,2,2,0,1,0,1,0,0,1,1,0,1]
]

def cert0033n : CertifiedBoard :=
  ⟨seed0033, by apply FastValid.valid; decide +kernel⟩

def cert0033r : CertifiedBoard :=
  ⟨seed0033.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0034 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [1,2,0,2,2,2,2,0,2,1,2,2,2],
  [1,1,2,2,1,0,1,2,1,0,2,0,1,0,0],
  [2,2,0,0,2,2,1,2,1,1,1,2,0,1,2,1,1],
  [2,2,1,2,2,0,0,0,0,1,0,0,2,0,0,1,1,0,1]
]

def cert0034n : CertifiedBoard :=
  ⟨seed0034, by apply FastValid.valid; decide +kernel⟩

def cert0034r : CertifiedBoard :=
  ⟨seed0034.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0035 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [1,2,0,2,2,2,2,0,2,1,2,2,2],
  [1,1,2,2,1,0,1,2,1,0,2,0,1,0,0],
  [2,2,0,0,2,2,1,2,1,1,1,2,0,1,2,1,1],
  [2,2,1,2,2,0,0,0,1,1,0,0,2,0,0,0,1,0,1]
]

def cert0035n : CertifiedBoard :=
  ⟨seed0035, by apply FastValid.valid; decide +kernel⟩

def cert0035r : CertifiedBoard :=
  ⟨seed0035.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0036 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [1,2,1,0,1,2,1,0,0,2,0,2,2],
  [2,2,1,2,0,1,0,2,1,1,2,0,2,0,1],
  [2,2,2,1,2,1,2,2,1,1,1,2,2,2,0,0,1],
  [0,1,0,1,1,0,0,0,0,2,2,2,0,0,1,2,2,0,0]
]

def cert0036n : CertifiedBoard :=
  ⟨seed0036, by apply FastValid.valid; decide +kernel⟩

def cert0036r : CertifiedBoard :=
  ⟨seed0036.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0037 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [1,2,1,1,1,2,1,1,0,1,0,0,0],
  [2,2,2,0,2,2,0,0,2,1,2,2,2,0,1],
  [2,1,2,2,1,0,1,1,2,2,2,1,0,2,2,1,2],
  [1,2,0,0,1,2,0,0,0,1,0,0,2,0,2,0,1,2,1]
]

def cert0037n : CertifiedBoard :=
  ⟨seed0037, by apply FastValid.valid; decide +kernel⟩

def cert0037r : CertifiedBoard :=
  ⟨seed0037.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0038 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [1,2,1,1,1,2,1,1,0,1,2,0,1],
  [2,0,0,2,0,2,2,1,2,2,2,1,2,2,0],
  [2,2,2,1,2,0,1,2,2,2,0,0,1,0,1,1,2],
  [1,2,1,0,0,2,0,0,1,0,2,2,0,2,1,0,0,0,0]
]

def cert0038n : CertifiedBoard :=
  ⟨seed0038, by apply FastValid.valid; decide +kernel⟩

def cert0038r : CertifiedBoard :=
  ⟨seed0038.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0039 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [1,2,1,1,1,2,1,1,0,1,2,0,1],
  [2,0,2,2,0,0,0,2,1,2,2,2,0,2,0],
  [1,2,1,2,2,2,2,1,0,2,2,1,2,0,1,1,2],
  [2,2,1,0,0,1,0,1,2,2,0,0,0,2,0,0,1,0,0]
]

def cert0039n : CertifiedBoard :=
  ⟨seed0039, by apply FastValid.valid; decide +kernel⟩

def cert0039r : CertifiedBoard :=
  ⟨seed0039.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0040 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [1,2,1,1,1,2,1,1,0,1,2,0,1],
  [2,2,0,0,2,2,2,0,2,1,2,2,1,0,0],
  [0,2,2,2,0,1,0,1,1,2,2,1,2,1,2,2,2],
  [2,2,1,0,2,0,2,0,0,0,1,2,0,0,1,0,0,0,2]
]

def cert0040n : CertifiedBoard :=
  ⟨seed0040, by apply FastValid.valid; decide +kernel⟩

def cert0040r : CertifiedBoard :=
  ⟨seed0040.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0041 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [1,2,1,1,1,2,1,1,0,1,2,0,1],
  [2,2,0,0,2,2,2,0,2,1,2,2,1,0,0],
  [0,2,2,2,2,1,0,1,1,2,2,1,2,1,2,2,0],
  [2,0,1,0,0,0,2,0,0,0,1,2,0,0,1,0,2,0,2]
]

def cert0041n : CertifiedBoard :=
  ⟨seed0041, by apply FastValid.valid; decide +kernel⟩

def cert0041r : CertifiedBoard :=
  ⟨seed0041.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0042 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [1,2,1,1,1,2,1,2,0,0,1,0,1],
  [0,1,2,2,0,2,0,0,2,2,0,2,1,0,1],
  [2,2,2,2,1,1,2,1,2,2,2,0,1,2,2,1,2],
  [1,2,0,1,0,2,2,1,0,0,0,2,0,0,0,1,1,0,0]
]

def cert0042n : CertifiedBoard :=
  ⟨seed0042, by apply FastValid.valid; decide +kernel⟩

def cert0042r : CertifiedBoard :=
  ⟨seed0042.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0043 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [1,2,1,1,1,2,2,0,2,1,2,0,1],
  [2,2,1,2,2,0,0,2,0,2,2,2,1,0,0],
  [1,2,1,0,1,2,2,2,1,1,2,0,0,1,2,1,2],
  [1,1,0,2,0,1,0,1,0,0,2,2,2,0,0,0,0,1,1]
]

def cert0043n : CertifiedBoard :=
  ⟨seed0043, by apply FastValid.valid; decide +kernel⟩

def cert0043r : CertifiedBoard :=
  ⟨seed0043.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0044 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [1,2,1,1,1,2,2,0,2,2,2,1,2],
  [2,0,0,1,0,0,2,2,2,2,1,0,2,0,1],
  [1,2,2,1,2,2,0,1,0,1,2,1,2,1,1,2,0],
  [2,2,0,0,0,0,2,0,2,1,0,1,1,0,0,1,2,0,0]
]

def cert0044n : CertifiedBoard :=
  ⟨seed0044, by apply FastValid.valid; decide +kernel⟩

def cert0044r : CertifiedBoard :=
  ⟨seed0044.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0045 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [1,2,1,1,2,0,0,0,2,0,2,2,0],
  [2,2,1,1,0,1,2,1,2,2,1,0,2,0,1],
  [2,1,2,1,2,2,2,2,2,0,1,1,1,2,0,2,1],
  [2,0,0,0,1,0,1,0,0,2,2,0,0,1,2,2,1,0,0]
]

def cert0045n : CertifiedBoard :=
  ⟨seed0045, by apply FastValid.valid; decide +kernel⟩

def cert0045r : CertifiedBoard :=
  ⟨seed0045.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0046 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [1,2,1,1,2,0,1,1,1,0,0,2,2],
  [2,2,0,0,1,2,2,1,2,2,1,2,1,0,1],
  [2,2,1,2,2,2,2,2,0,2,0,1,0,2,1,0,1],
  [0,1,0,0,0,0,1,2,1,1,2,0,2,0,0,2,2,0,0]
]

def cert0046n : CertifiedBoard :=
  ⟨seed0046, by apply FastValid.valid; decide +kernel⟩

def cert0046r : CertifiedBoard :=
  ⟨seed0046.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0047 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [1,2,1,1,2,0,1,1,1,0,0,2,2],
  [2,2,2,0,2,1,1,2,2,1,2,1,0,0,0],
  [2,2,1,2,1,2,0,0,1,2,2,0,1,2,2,2,1],
  [2,1,0,1,0,2,2,2,0,0,0,2,0,2,0,0,1,0,1]
]

def cert0047n : CertifiedBoard :=
  ⟨seed0047, by apply FastValid.valid; decide +kernel⟩

def cert0047r : CertifiedBoard :=
  ⟨seed0047.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0048 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [1,2,1,1,2,0,1,1,1,0,1,0,2],
  [2,1,2,2,0,2,2,0,0,2,2,2,1,0,1],
  [2,2,2,2,1,1,2,1,2,2,1,0,0,2,0,2,1],
  [0,2,0,0,1,0,0,1,2,2,0,1,2,1,2,0,0,0,0]
]

def cert0048n : CertifiedBoard :=
  ⟨seed0048, by apply FastValid.valid; decide +kernel⟩

def cert0048r : CertifiedBoard :=
  ⟨seed0048.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0049 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [1,2,1,1,2,0,1,1,1,0,1,2,0],
  [2,2,0,0,0,2,2,2,1,2,2,0,2,0,0],
  [1,2,1,1,2,1,0,1,2,2,2,1,2,2,2,1,2],
  [2,0,0,0,1,0,2,0,2,1,0,0,2,2,0,1,0,0,1]
]

def cert0049n : CertifiedBoard :=
  ⟨seed0049, by apply FastValid.valid; decide +kernel⟩

def cert0049r : CertifiedBoard :=
  ⟨seed0049.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0050 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [1,2,1,1,2,0,2,2,0,2,1,2,1],
  [0,1,2,0,0,2,0,1,2,2,0,1,0,0,1],
  [2,2,2,1,1,2,1,2,2,2,2,1,2,2,1,0,1],
  [2,1,0,1,1,1,0,2,2,0,0,1,0,0,0,2,0,0,0]
]

def cert0050n : CertifiedBoard :=
  ⟨seed0050, by apply FastValid.valid; decide +kernel⟩

def cert0050r : CertifiedBoard :=
  ⟨seed0050.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0051 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [1,2,1,1,2,2,1,0,1,0,0,0,0],
  [2,2,1,1,1,0,2,2,0,2,1,2,2,0,1],
  [1,2,2,0,2,2,2,2,2,1,0,1,2,1,2,1,2],
  [2,0,0,1,1,2,0,1,0,0,2,0,0,1,2,0,0,2,0]
]

def cert0051n : CertifiedBoard :=
  ⟨seed0051, by apply FastValid.valid; decide +kernel⟩

def cert0051r : CertifiedBoard :=
  ⟨seed0051.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0052 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [1,2,1,1,2,2,1,1,1,0,1,0,1],
  [1,2,0,0,2,1,0,2,0,2,2,2,1,0,0],
  [2,2,2,2,0,2,2,0,1,2,2,1,2,1,2,1,2],
  [0,0,2,0,1,1,2,2,0,0,1,0,0,0,1,2,0,0,0]
]

def cert0052n : CertifiedBoard :=
  ⟨seed0052, by apply FastValid.valid; decide +kernel⟩

def cert0052r : CertifiedBoard :=
  ⟨seed0052.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0053 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [1,2,1,1,2,2,2,0,0,2,2,0,0],
  [2,2,1,1,1,0,1,2,2,1,0,2,2,0,1],
  [1,2,0,1,0,1,2,2,2,2,1,2,1,2,1,2,0],
  [2,0,2,0,2,0,0,0,1,0,0,2,1,0,0,0,1,1,2]
]

def cert0053n : CertifiedBoard :=
  ⟨seed0053, by apply FastValid.valid; decide +kernel⟩

def cert0053r : CertifiedBoard :=
  ⟨seed0053.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0054 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [1,2,1,1,2,2,2,0,2,2,0,0,1],
  [1,1,0,1,2,0,1,2,0,2,2,2,0,0,0],
  [2,2,1,2,2,2,1,0,1,1,2,1,2,2,1,2,1],
  [2,1,0,0,2,0,0,2,0,1,0,0,0,1,0,2,1,1,1]
]

def cert0054n : CertifiedBoard :=
  ⟨seed0054, by apply FastValid.valid; decide +kernel⟩

def cert0054r : CertifiedBoard :=
  ⟨seed0054.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0055 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [1,2,1,1,2,2,2,2,1,2,0,2,0],
  [2,2,0,0,2,2,1,0,0,1,2,0,1,2,1],
  [2,1,2,2,1,2,1,1,1,2,2,2,0,0,1,0,1],
  [2,0,1,0,1,1,0,2,0,0,0,0,2,2,0,2,1,0,0]
]

def cert0055n : CertifiedBoard :=
  ⟨seed0055, by apply FastValid.valid; decide +kernel⟩

def cert0055r : CertifiedBoard :=
  ⟨seed0055.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0056 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [1,2,1,2,2,0,0,0,0,2,0,2,2],
  [1,1,2,0,0,1,1,2,2,2,1,2,1,0,1],
  [2,2,1,2,2,0,2,2,2,2,1,1,0,2,1,1,1],
  [2,2,0,0,1,2,1,0,0,2,0,1,2,0,1,0,1,0,0]
]

def cert0056n : CertifiedBoard :=
  ⟨seed0056, by apply FastValid.valid; decide +kernel⟩

def cert0056r : CertifiedBoard :=
  ⟨seed0056.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0057 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [1,2,1,2,2,0,0,0,0,2,2,2,2],
  [1,1,2,0,0,1,1,2,2,1,0,2,2,0,1],
  [2,2,1,2,2,2,0,2,1,0,1,2,1,2,1,1,1],
  [2,2,1,1,0,0,2,0,1,2,0,2,0,0,1,0,1,0,0]
]

def cert0057n : CertifiedBoard :=
  ⟨seed0057, by apply FastValid.valid; decide +kernel⟩

def cert0057r : CertifiedBoard :=
  ⟨seed0057.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0058 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [1,2,1,2,2,0,1,1,0,1,2,0,1],
  [2,2,1,0,0,2,0,0,2,0,2,2,2,1,2],
  [1,2,1,1,1,2,1,2,2,2,1,0,1,2,0,2,2],
  [2,2,2,0,0,1,0,0,0,1,0,2,1,1,2,2,0,0,0]
]

def cert0058n : CertifiedBoard :=
  ⟨seed0058, by apply FastValid.valid; decide +kernel⟩

def cert0058r : CertifiedBoard :=
  ⟨seed0058.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0059 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [1,2,1,2,2,2,0,0,2,2,1,2,0],
  [0,2,1,1,0,0,1,1,2,2,2,0,2,0,2],
  [2,2,1,0,1,2,1,1,1,2,1,2,2,2,1,0,1],
  [2,0,1,2,0,1,0,2,0,0,1,0,0,0,2,2,0,0,0]
]

def cert0059n : CertifiedBoard :=
  ⟨seed0059, by apply FastValid.valid; decide +kernel⟩

def cert0059r : CertifiedBoard :=
  ⟨seed0059.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0060 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [1,2,1,2,2,2,1,1,1,0,0,1,2],
  [2,1,2,2,0,1,0,2,0,2,2,0,1,0,1],
  [2,2,0,0,1,1,2,0,2,2,2,2,1,1,2,2,1],
  [1,2,1,2,1,0,1,2,0,0,0,2,0,0,2,1,0,0,0]
]

def cert0060n : CertifiedBoard :=
  ⟨seed0060, by apply FastValid.valid; decide +kernel⟩

def cert0060r : CertifiedBoard :=
  ⟨seed0060.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0061 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [1,2,1,2,2,2,1,1,1,0,0,1,2],
  [2,1,2,2,0,1,0,2,0,2,2,0,1,0,1],
  [2,2,0,0,1,1,2,0,2,2,2,2,1,1,2,2,1],
  [1,2,1,2,1,0,1,2,0,0,2,0,0,0,2,1,0,0,0]
]

def cert0061n : CertifiedBoard :=
  ⟨seed0061, by apply FastValid.valid; decide +kernel⟩

def cert0061r : CertifiedBoard :=
  ⟨seed0061.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0062 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [1,2,1,2,2,2,1,1,1,0,1,0,2],
  [0,2,0,1,2,1,0,0,2,2,0,2,1,0,1],
  [2,2,2,2,0,2,2,1,1,2,2,0,1,1,2,1,2],
  [1,2,0,0,1,2,2,1,2,0,0,2,0,0,0,1,0,0,0]
]

def cert0062n : CertifiedBoard :=
  ⟨seed0062, by apply FastValid.valid; decide +kernel⟩

def cert0062r : CertifiedBoard :=
  ⟨seed0062.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0063 : Board := [
  [0],
  [0,0,0],
  [0,0,1,0,0],
  [0,0,2,0,1,1,0],
  [0,1,2,0,2,1,0,2,2],
  [1,0,1,1,0,2,1,1,1,1,2],
  [1,2,1,2,2,2,2,0,2,2,0,0,1],
  [0,2,1,1,0,2,0,1,2,1,2,1,1,2,0],
  [2,0,1,1,1,2,2,2,1,2,2,1,0,1,2,0,2],
  [2,2,1,0,0,1,0,1,0,0,0,0,2,0,0,2,2,0,0]
]

def cert0063n : CertifiedBoard :=
  ⟨seed0063, by apply FastValid.valid; decide +kernel⟩

def cert0063r : CertifiedBoard :=
  ⟨seed0063.map List.reverse, by apply FastValid.valid; decide +kernel⟩

end TBoards.Extended
