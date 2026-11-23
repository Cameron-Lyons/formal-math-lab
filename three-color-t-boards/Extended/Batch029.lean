import Extended.Batch025

/- Generated from extended_seeds.json. Published seeds 0–4:
   Qiyuan Ma, DOI 10.5281/zenodo.23631079, CC-BY-4.0. -/

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.Extended

def seed0928 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,1,2,1,0,1,0,0,0,2,1],
  [2,1,0,2,1,2,0,1,1,0,1,0,0,1,1],
  [1,1,0,0,1,2,2,1,2,0,2,2,0,0,2,0,0],
  [0,0,0,2,0,2,1,1,1,1,2,0,2,2,0,1,1,0,2]
]

def cert0928n : CertifiedBoard :=
  ⟨seed0928, by apply FastValid.valid; decide +kernel⟩

def cert0928r : CertifiedBoard :=
  ⟨seed0928.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0929 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,1,2,1,0,1,0,0,2,2,1],
  [0,1,1,0,0,0,0,2,0,1,0,2,1,1,1],
  [2,1,2,0,0,2,1,0,1,1,0,0,1,2,2,0,2],
  [1,1,1,0,2,2,0,2,0,2,1,2,0,1,1,2,0,0,1]
]

def cert0929n : CertifiedBoard :=
  ⟨seed0929, by apply FastValid.valid; decide +kernel⟩

def cert0929r : CertifiedBoard :=
  ⟨seed0929.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0930 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,1,2,1,0,2,0,2,1,1,1],
  [2,0,1,2,0,2,2,0,0,0,1,1,0,0,2],
  [1,1,0,0,0,1,1,2,0,2,2,0,1,0,1,0,1],
  [0,1,1,1,0,2,1,2,2,1,0,0,2,0,0,2,1,2,0]
]

def cert0930n : CertifiedBoard :=
  ⟨seed0930, by apply FastValid.valid; decide +kernel⟩

def cert0930r : CertifiedBoard :=
  ⟨seed0930.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0931 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,1,2,1,2,0,0,0,1,1,2],
  [0,1,1,0,0,0,2,0,2,0,0,1,1,1,1],
  [1,2,0,2,1,0,2,1,1,0,2,2,0,1,0,0,2],
  [1,1,0,0,2,1,0,1,2,2,0,2,2,1,2,0,1,0,1]
]

def cert0931n : CertifiedBoard :=
  ⟨seed0931, by apply FastValid.valid; decide +kernel⟩

def cert0931r : CertifiedBoard :=
  ⟨seed0931.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0932 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,1,2,1,2,0,2,1,1,1,0],
  [1,0,0,1,1,1,2,2,1,0,1,0,0,0,2],
  [0,2,1,2,0,1,1,0,0,0,2,1,0,2,0,0,2],
  [1,1,0,2,0,2,2,0,0,1,0,1,2,0,2,2,0,1,1]
]

def cert0932n : CertifiedBoard :=
  ⟨seed0932, by apply FastValid.valid; decide +kernel⟩

def cert0932r : CertifiedBoard :=
  ⟨seed0932.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0933 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,2,0,0,0,0,2,2,1,1,1],
  [1,1,0,1,1,2,0,0,2,0,1,1,1,0,0],
  [0,1,2,2,0,1,1,0,1,0,2,2,0,2,1,0,2],
  [0,0,1,0,0,2,1,2,1,2,0,1,2,0,2,1,0,0,1]
]

def cert0933n : CertifiedBoard :=
  ⟨seed0933, by apply FastValid.valid; decide +kernel⟩

def cert0933r : CertifiedBoard :=
  ⟨seed0933.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0934 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,2,0,0,0,0,2,2,1,1,2],
  [0,1,1,1,0,0,2,0,1,0,1,1,1,0,2],
  [1,0,2,1,2,1,0,1,2,0,2,2,0,1,0,0,1],
  [1,2,2,0,1,1,0,0,1,2,0,0,2,1,2,0,2,1,0]
]

def cert0934n : CertifiedBoard :=
  ⟨seed0934, by apply FastValid.valid; decide +kernel⟩

def cert0934r : CertifiedBoard :=
  ⟨seed0934.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0935 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,2,0,0,0,1,0,2,1,1,0],
  [2,2,0,1,1,1,0,1,0,0,1,1,1,0,0],
  [1,0,1,2,0,1,2,1,2,0,2,0,2,1,0,2,2],
  [0,0,2,1,2,0,1,1,2,2,1,0,0,2,2,0,0,0,2]
]

def cert0935n : CertifiedBoard :=
  ⟨seed0935, by apply FastValid.valid; decide +kernel⟩

def cert0935r : CertifiedBoard :=
  ⟨seed0935.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0936 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,2,0,0,0,1,0,2,2,1,1],
  [2,0,0,0,2,1,0,0,1,1,0,1,2,2,0],
  [1,1,2,0,1,0,0,2,1,2,0,1,1,1,1,0,2],
  [1,1,0,0,2,0,2,2,0,1,2,0,2,1,2,1,0,1,1]
]

def cert0936n : CertifiedBoard :=
  ⟨seed0936, by apply FastValid.valid; decide +kernel⟩

def cert0936r : CertifiedBoard :=
  ⟨seed0936.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0937 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,2,0,0,0,1,1,1,2,0,1],
  [2,0,2,1,0,2,0,1,1,0,0,2,2,0,2],
  [1,1,0,1,1,1,0,0,2,1,2,0,0,0,2,1,1],
  [0,1,2,1,2,0,1,0,2,2,1,0,1,0,0,1,2,2,0]
]

def cert0937n : CertifiedBoard :=
  ⟨seed0937, by apply FastValid.valid; decide +kernel⟩

def cert0937r : CertifiedBoard :=
  ⟨seed0937.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0938 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,2,0,0,0,2,1,1,1,0,1],
  [1,2,0,1,0,0,2,0,0,1,0,0,2,1,2],
  [1,2,2,1,2,1,0,0,0,1,1,1,0,2,1,0,2],
  [0,1,1,2,0,2,2,0,2,2,0,1,2,0,1,1,0,1,2]
]

def cert0938n : CertifiedBoard :=
  ⟨seed0938, by apply FastValid.valid; decide +kernel⟩

def cert0938r : CertifiedBoard :=
  ⟨seed0938.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0939 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,2,0,0,2,1,0,2,2,1,1],
  [0,2,0,1,1,2,0,1,2,1,0,0,1,2,0],
  [1,1,0,1,0,0,0,0,1,1,1,0,2,1,2,0,2],
  [2,0,2,1,2,2,0,0,2,2,0,1,0,1,1,1,0,0,2]
]

def cert0939n : CertifiedBoard :=
  ⟨seed0939, by apply FastValid.valid; decide +kernel⟩

def cert0939r : CertifiedBoard :=
  ⟨seed0939.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0940 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,2,0,1,0,0,0,1,1,0,2],
  [1,0,0,0,1,2,0,2,0,2,1,2,1,2,0],
  [0,1,1,0,2,2,0,1,0,1,1,1,1,2,2,1,0],
  [2,0,1,2,0,0,2,2,0,0,2,1,0,0,2,1,1,0,1]
]

def cert0940n : CertifiedBoard :=
  ⟨seed0940, by apply FastValid.valid; decide +kernel⟩

def cert0940r : CertifiedBoard :=
  ⟨seed0940.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0941 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,2,0,1,0,0,0,1,1,2,0],
  [2,0,0,0,2,1,2,0,2,0,1,1,1,0,2],
  [2,1,1,0,1,1,1,0,1,0,2,1,0,0,2,2,1],
  [2,0,1,2,2,0,2,1,2,0,0,1,2,1,0,0,2,2,0]
]

def cert0941n : CertifiedBoard :=
  ⟨seed0941, by apply FastValid.valid; decide +kernel⟩

def cert0941r : CertifiedBoard :=
  ⟨seed0941.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0942 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,2,0,1,0,0,0,2,2,1,1],
  [1,0,0,0,1,1,0,0,2,0,0,1,2,1,2],
  [1,2,2,0,2,2,0,2,1,0,1,0,1,1,1,1,0],
  [1,1,0,2,1,2,0,1,1,2,0,1,2,0,0,2,1,0,2]
]

def cert0942n : CertifiedBoard :=
  ⟨seed0942, by apply FastValid.valid; decide +kernel⟩

def cert0942r : CertifiedBoard :=
  ⟨seed0942.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0943 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,2,0,1,0,0,2,2,1,1,1],
  [2,0,2,1,0,2,1,0,2,0,1,2,1,2,0],
  [1,1,0,0,2,1,2,0,0,1,1,0,0,0,0,1,1],
  [1,1,1,0,1,0,1,1,2,0,1,2,2,0,0,2,2,0,2]
]

def cert0943n : CertifiedBoard :=
  ⟨seed0943, by apply FastValid.valid; decide +kernel⟩

def cert0943r : CertifiedBoard :=
  ⟨seed0943.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0944 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,2,0,1,0,1,1,0,0,2,2],
  [0,1,0,2,0,1,1,0,1,2,1,0,2,1,1],
  [1,1,0,0,1,2,0,2,1,2,2,1,0,0,0,0,2],
  [2,2,0,0,2,1,2,0,1,1,1,1,2,0,2,2,0,0,1]
]

def cert0944n : CertifiedBoard :=
  ⟨seed0944, by apply FastValid.valid; decide +kernel⟩

def cert0944r : CertifiedBoard :=
  ⟨seed0944.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0945 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,2,0,1,0,1,1,2,0,1,1],
  [1,1,0,2,2,1,2,1,0,0,2,2,0,0,0],
  [0,2,1,0,2,1,1,1,1,0,1,0,0,0,2,0,2],
  [0,0,1,2,0,0,1,2,2,0,2,1,2,0,1,1,0,0,2]
]

def cert0945n : CertifiedBoard :=
  ⟨seed0945, by apply FastValid.valid; decide +kernel⟩

def cert0945r : CertifiedBoard :=
  ⟨seed0945.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0946 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,2,0,1,1,0,0,0,1,2,0],
  [2,0,0,2,2,1,2,2,0,2,0,1,0,0,2],
  [0,1,1,0,2,1,1,1,1,2,0,1,1,0,1,0,1],
  [0,0,1,2,1,0,2,1,2,0,2,2,0,0,2,1,0,0,0]
]

def cert0946n : CertifiedBoard :=
  ⟨seed0946, by apply FastValid.valid; decide +kernel⟩

def cert0946r : CertifiedBoard :=
  ⟨seed0946.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0947 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,2,0,1,1,1,0,0,0,2,1],
  [1,1,0,1,1,0,1,0,0,0,2,0,1,1,1],
  [2,1,2,2,0,2,1,2,0,0,1,0,2,2,0,0,2],
  [0,1,2,1,1,2,0,1,2,0,2,1,0,2,2,1,0,0,1]
]

def cert0947n : CertifiedBoard :=
  ⟨seed0947, by apply FastValid.valid; decide +kernel⟩

def cert0947r : CertifiedBoard :=
  ⟨seed0947.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0948 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,2,0,1,1,1,0,0,1,1,0],
  [0,1,0,2,2,1,2,2,0,2,0,1,2,0,2],
  [0,0,1,0,1,2,0,0,2,1,0,1,1,1,2,0,1],
  [1,0,2,1,0,0,2,2,0,0,0,0,2,1,2,1,1,0,0]
]

def cert0948n : CertifiedBoard :=
  ⟨seed0948, by apply FastValid.valid; decide +kernel⟩

def cert0948r : CertifiedBoard :=
  ⟨seed0948.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0949 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,2,0,1,1,2,1,1,0,0,1],
  [2,1,2,0,0,2,2,0,0,0,0,2,0,1,2],
  [0,1,1,1,1,0,2,2,1,0,0,1,0,1,1,0,2],
  [1,2,0,2,1,2,2,0,1,2,0,2,1,0,1,0,0,2,1]
]

def cert0949n : CertifiedBoard :=
  ⟨seed0949, by apply FastValid.valid; decide +kernel⟩

def cert0949r : CertifiedBoard :=
  ⟨seed0949.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0950 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,2,0,1,1,2,2,1,1,0,0],
  [1,1,0,1,0,2,1,0,0,1,1,1,0,2,0],
  [2,0,0,0,1,0,1,2,0,0,2,1,2,1,2,0,2],
  [0,0,2,2,0,1,2,0,2,1,0,0,0,2,2,0,1,1,1]
]

def cert0950n : CertifiedBoard :=
  ⟨seed0950, by apply FastValid.valid; decide +kernel⟩

def cert0950r : CertifiedBoard :=
  ⟨seed0950.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0951 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,2,0,1,1,2,2,1,1,0,1],
  [1,0,0,1,0,0,1,2,0,1,2,1,2,0,2],
  [0,1,0,1,1,0,2,1,0,2,0,0,0,2,1,2,0],
  [2,0,2,1,0,0,0,2,2,0,0,2,2,0,1,1,1,1,0]
]

def cert0951n : CertifiedBoard :=
  ⟨seed0951, by apply FastValid.valid; decide +kernel⟩

def cert0951r : CertifiedBoard :=
  ⟨seed0951.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0952 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,2,0,1,1,2,2,1,1,0,2],
  [2,1,2,0,1,2,0,0,0,2,2,0,2,0,1],
  [0,1,1,0,1,1,1,1,0,1,0,0,0,2,1,0,0],
  [0,0,1,2,0,2,1,2,1,0,0,2,2,0,0,1,0,2,1]
]

def cert0952n : CertifiedBoard :=
  ⟨seed0952, by apply FastValid.valid; decide +kernel⟩

def cert0952r : CertifiedBoard :=
  ⟨seed0952.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0953 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,2,0,1,1,2,2,1,1,1,0],
  [2,1,0,1,0,2,2,0,0,1,2,1,0,0,2],
  [1,0,0,0,1,0,0,0,2,1,2,0,1,2,0,1,1],
  [1,1,1,0,1,1,0,2,0,2,1,2,0,0,2,2,0,2,1]
]

def cert0953n : CertifiedBoard :=
  ⟨seed0953, by apply FastValid.valid; decide +kernel⟩

def cert0953r : CertifiedBoard :=
  ⟨seed0953.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0954 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,2,0,1,2,0,2,2,1,1,1],
  [1,0,1,1,0,2,0,0,1,0,0,0,2,1,2],
  [1,2,1,0,0,0,1,2,0,1,0,2,2,0,1,1,0],
  [1,1,1,2,0,0,2,1,0,1,1,0,0,2,1,2,2,0,2]
]

def cert0954n : CertifiedBoard :=
  ⟨seed0954, by apply FastValid.valid; decide +kernel⟩

def cert0954r : CertifiedBoard :=
  ⟨seed0954.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0955 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,2,0,2,1,1,0,0,0,1,1],
  [1,1,0,1,1,0,1,2,0,1,0,2,0,0,2],
  [0,1,2,1,2,2,0,1,0,2,1,0,0,2,2,0,1],
  [0,0,1,1,1,1,2,0,0,0,2,1,2,0,2,2,1,0,0]
]

def cert0955n : CertifiedBoard :=
  ⟨seed0955, by apply FastValid.valid; decide +kernel⟩

def cert0955r : CertifiedBoard :=
  ⟨seed0955.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0956 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,2,0,2,1,1,0,1,2,0,1],
  [0,1,1,0,0,0,2,1,2,1,0,0,2,1,0],
  [1,0,1,2,0,2,0,1,1,1,2,2,0,0,1,0,2],
  [0,0,0,1,1,1,0,2,2,0,0,2,2,1,2,0,1,0,0]
]

def cert0956n : CertifiedBoard :=
  ⟨seed0956, by apply FastValid.valid; decide +kernel⟩

def cert0956r : CertifiedBoard :=
  ⟨seed0956.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0957 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,2,0,2,1,1,1,0,1,1,1],
  [1,1,0,0,2,2,0,1,0,0,2,2,0,1,1],
  [2,0,0,0,1,0,2,1,2,1,0,0,0,2,1,2,0],
  [1,1,2,0,1,1,0,1,2,2,1,0,2,0,0,1,2,0,2]
]

def cert0957n : CertifiedBoard :=
  ⟨seed0957, by apply FastValid.valid; decide +kernel⟩

def cert0957r : CertifiedBoard :=
  ⟨seed0957.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0958 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,2,0,2,1,1,1,1,0,0,0],
  [2,1,2,0,1,2,0,1,2,0,1,1,0,0,2],
  [1,0,1,0,2,0,0,1,0,0,2,1,2,1,0,2,1],
  [0,0,2,2,0,2,2,0,0,0,1,1,2,2,1,0,1,1,0]
]

def cert0958n : CertifiedBoard :=
  ⟨seed0958, by apply FastValid.valid; decide +kernel⟩

def cert0958r : CertifiedBoard :=
  ⟨seed0958.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0959 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,2,0,2,0,2,1,1,1,1,0,0,2],
  [2,0,2,1,0,1,1,2,1,0,0,2,0,0,1],
  [1,2,0,1,1,0,1,2,0,1,1,0,0,0,2,2,0],
  [0,1,0,2,1,2,2,0,1,2,0,0,0,1,0,2,2,1,2]
]

def cert0959n : CertifiedBoard :=
  ⟨seed0959, by apply FastValid.valid; decide +kernel⟩

def cert0959r : CertifiedBoard :=
  ⟨seed0959.map List.reverse, by apply FastValid.valid; decide +kernel⟩

end TBoards.Extended
