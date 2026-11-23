import Extended.Batch021

/- Generated from extended_seeds.json. Published seeds 0–4:
   Qiyuan Ma, DOI 10.5281/zenodo.23631079, CC-BY-4.0. -/

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.Extended

def seed0800 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,1,0,0,0,0,2,1,1,2],
  [1,0,2,0,2,1,2,0,0,2,0,1,1,0,1],
  [1,2,1,0,2,2,1,0,0,1,1,0,0,2,1,2,0],
  [2,0,2,2,0,1,1,1,1,0,1,2,2,0,2,0,0,1,0]
]

def cert0800n : CertifiedBoard :=
  ⟨seed0800, by apply FastValid.valid; decide +kernel⟩

def cert0800r : CertifiedBoard :=
  ⟨seed0800.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0801 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,1,0,0,0,2,2,1,1,0],
  [2,0,0,0,2,0,2,1,0,0,1,1,1,0,1],
  [1,0,0,2,2,0,1,0,1,1,0,2,1,2,1,2,2],
  [2,2,0,1,1,1,2,0,0,1,2,0,2,1,0,2,0,2,0]
]

def cert0801n : CertifiedBoard :=
  ⟨seed0801, by apply FastValid.valid; decide +kernel⟩

def cert0801r : CertifiedBoard :=
  ⟨seed0801.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0802 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,1,0,0,1,1,0,0,2,2],
  [2,0,0,2,1,2,0,2,0,2,1,0,2,0,1],
  [1,1,1,0,1,1,1,2,0,2,1,1,0,0,0,2,0],
  [2,2,0,0,0,1,2,1,0,2,2,1,2,2,0,1,0,1,1]
]

def cert0802n : CertifiedBoard :=
  ⟨seed0802, by apply FastValid.valid; decide +kernel⟩

def cert0802r : CertifiedBoard :=
  ⟨seed0802.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0803 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,1,0,0,1,1,0,2,1,1],
  [0,0,2,0,1,1,1,0,0,0,2,2,1,2,2],
  [2,2,0,2,0,1,2,1,0,2,1,0,1,1,0,0,0],
  [1,1,1,2,0,2,0,2,2,0,0,2,1,2,0,0,1,0,1]
]

def cert0803n : CertifiedBoard :=
  ⟨seed0803, by apply FastValid.valid; decide +kernel⟩

def cert0803r : CertifiedBoard :=
  ⟨seed0803.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0804 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,1,0,0,1,1,0,2,2,1],
  [2,1,2,0,2,2,0,0,1,2,2,0,1,1,1],
  [1,1,1,0,0,2,1,1,0,0,0,0,2,0,0,2,0],
  [2,0,2,1,0,1,1,2,1,2,0,2,1,0,1,0,2,0,1]
]

def cert0804n : CertifiedBoard :=
  ⟨seed0804, by apply FastValid.valid; decide +kernel⟩

def cert0804r : CertifiedBoard :=
  ⟨seed0804.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0805 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,1,0,0,2,0,2,1,1,0],
  [1,0,0,0,1,1,0,2,2,1,0,2,1,0,1],
  [2,2,0,2,1,2,0,0,1,1,1,1,0,0,2,0,2],
  [0,2,0,1,0,1,1,2,0,1,2,1,2,2,0,0,0,2,2]
]

def cert0805n : CertifiedBoard :=
  ⟨seed0805, by apply FastValid.valid; decide +kernel⟩

def cert0805r : CertifiedBoard :=
  ⟨seed0805.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0806 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,1,0,0,2,0,2,1,1,1],
  [1,0,0,0,1,1,1,0,2,2,0,1,2,2,0],
  [2,0,0,2,0,2,1,2,1,0,2,0,1,1,0,1,0],
  [1,1,2,0,0,0,1,1,0,0,2,2,1,2,0,2,1,0,1]
]

def cert0806n : CertifiedBoard :=
  ⟨seed0806, by apply FastValid.valid; decide +kernel⟩

def cert0806r : CertifiedBoard :=
  ⟨seed0806.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0807 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,1,0,0,2,1,1,1,0,0],
  [1,0,2,0,1,1,1,0,0,1,2,1,2,0,0],
  [0,0,2,2,1,2,2,0,2,0,1,1,2,0,2,1,0],
  [0,0,1,0,1,1,0,2,0,2,2,0,0,0,0,2,1,0,1]
]

def cert0807n : CertifiedBoard :=
  ⟨seed0807, by apply FastValid.valid; decide +kernel⟩

def cert0807r : CertifiedBoard :=
  ⟨seed0807.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0808 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,1,0,0,2,1,1,1,0,2],
  [0,2,0,0,0,2,0,2,2,1,2,1,0,0,1],
  [2,1,0,0,1,0,2,2,0,1,1,1,2,0,1,1,0],
  [1,0,1,1,0,1,2,0,2,1,2,2,0,2,0,0,0,2,1]
]

def cert0808n : CertifiedBoard :=
  ⟨seed0808, by apply FastValid.valid; decide +kernel⟩

def cert0808r : CertifiedBoard :=
  ⟨seed0808.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0809 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,1,1,0,1,0,0,2,0,2],
  [0,2,0,2,1,2,1,0,1,2,0,2,2,0,1],
  [0,2,2,1,0,2,1,1,1,0,0,1,1,1,0,0,0],
  [0,0,1,1,2,0,0,0,2,0,0,2,1,2,2,0,1,0,2]
]

def cert0809n : CertifiedBoard :=
  ⟨seed0809, by apply FastValid.valid; decide +kernel⟩

def cert0809r : CertifiedBoard :=
  ⟨seed0809.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0810 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,1,1,0,1,0,0,2,0,2],
  [1,0,0,2,1,2,2,0,2,1,0,2,2,0,1],
  [0,0,0,2,1,1,1,0,2,2,1,0,1,1,1,0,0],
  [0,2,0,1,1,2,1,2,0,0,0,1,2,0,2,0,0,1,0]
]

def cert0810n : CertifiedBoard :=
  ⟨seed0810, by apply FastValid.valid; decide +kernel⟩

def cert0810r : CertifiedBoard :=
  ⟨seed0810.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0811 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,1,1,0,2,0,1,1,1,0],
  [1,0,0,0,2,0,0,2,2,1,2,1,0,0,1],
  [2,0,2,1,0,2,2,0,2,0,2,1,1,1,0,1,0],
  [1,0,1,1,2,0,0,0,1,0,0,2,1,2,2,0,1,2,0]
]

def cert0811n : CertifiedBoard :=
  ⟨seed0811, by apply FastValid.valid; decide +kernel⟩

def cert0811r : CertifiedBoard :=
  ⟨seed0811.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0812 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,1,1,0,2,0,1,1,1,0],
  [1,0,0,2,1,2,2,0,0,0,2,1,2,1,0],
  [1,2,0,1,0,0,0,2,2,0,2,2,1,0,1,0,1],
  [1,0,0,1,1,1,0,2,1,1,2,0,2,0,2,0,0,1,2]
]

def cert0812n : CertifiedBoard :=
  ⟨seed0812, by apply FastValid.valid; decide +kernel⟩

def cert0812r : CertifiedBoard :=
  ⟨seed0812.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0813 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,1,1,0,2,0,1,1,1,0],
  [1,0,1,0,1,0,0,2,0,2,1,2,2,0,1],
  [2,1,0,0,0,1,2,0,0,0,2,0,2,2,1,2,1],
  [1,1,2,0,2,2,0,0,1,1,0,2,1,0,0,2,1,1,1]
]

def cert0813n : CertifiedBoard :=
  ⟨seed0813, by apply FastValid.valid; decide +kernel⟩

def cert0813r : CertifiedBoard :=
  ⟨seed0813.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0814 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,1,1,0,2,1,1,0,0,1],
  [0,2,1,0,1,0,0,0,2,1,2,1,2,0,0],
  [2,2,0,1,0,0,2,0,0,1,1,1,2,2,1,0,2],
  [0,0,0,2,2,0,1,1,1,0,1,2,0,2,0,2,0,2,2]
]

def cert0814n : CertifiedBoard :=
  ⟨seed0814, by apply FastValid.valid; decide +kernel⟩

def cert0814r : CertifiedBoard :=
  ⟨seed0814.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0815 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,1,1,0,2,1,1,0,0,1],
  [1,0,0,2,1,2,0,0,2,0,2,0,1,0,0],
  [2,1,0,1,1,1,1,2,0,0,2,0,2,2,0,2,1],
  [0,0,0,0,1,2,1,2,2,1,0,2,2,0,1,1,0,1,0]
]

def cert0815n : CertifiedBoard :=
  ⟨seed0815, by apply FastValid.valid; decide +kernel⟩

def cert0815r : CertifiedBoard :=
  ⟨seed0815.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0816 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,1,1,1,0,0,0,1,1,1],
  [1,2,0,0,2,1,2,2,0,2,0,0,0,2,0],
  [1,1,0,0,1,1,2,0,2,2,0,1,0,0,2,1,2],
  [2,0,2,1,0,1,2,1,1,0,2,0,1,0,2,2,1,0,1]
]

def cert0816n : CertifiedBoard :=
  ⟨seed0816, by apply FastValid.valid; decide +kernel⟩

def cert0816r : CertifiedBoard :=
  ⟨seed0816.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0817 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,1,1,1,0,0,1,1,1,2],
  [1,2,0,2,0,1,2,2,0,2,1,2,1,0,1],
  [1,1,0,0,2,2,0,0,0,2,0,2,0,1,0,0,0],
  [0,0,2,1,0,2,1,1,0,1,0,2,2,1,2,0,0,1,1]
]

def cert0817n : CertifiedBoard :=
  ⟨seed0817, by apply FastValid.valid; decide +kernel⟩

def cert0817r : CertifiedBoard :=
  ⟨seed0817.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0818 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,1,1,1,0,0,1,1,1,2],
  [2,0,1,0,2,0,2,0,0,2,1,2,1,0,1],
  [1,0,0,1,2,0,2,2,1,0,0,0,0,2,1,2,0],
  [1,2,2,0,0,2,0,2,1,1,0,1,1,0,2,2,0,1,0]
]

def cert0818n : CertifiedBoard :=
  ⟨seed0818, by apply FastValid.valid; decide +kernel⟩

def cert0818r : CertifiedBoard :=
  ⟨seed0818.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0819 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,1,1,1,0,0,2,2,1,1],
  [1,0,0,0,0,1,2,0,0,2,0,2,0,2,1],
  [2,1,0,2,2,0,0,2,1,2,0,1,1,1,0,1,0],
  [1,1,2,1,0,0,1,0,1,1,0,2,1,2,2,0,2,0,1]
]

def cert0819n : CertifiedBoard :=
  ⟨seed0819, by apply FastValid.valid; decide +kernel⟩

def cert0819r : CertifiedBoard :=
  ⟨seed0819.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0820 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,1,1,1,1,0,0,2,1,1],
  [0,0,2,0,2,1,2,2,0,2,0,0,1,2,0],
  [2,0,1,1,2,0,1,0,1,1,0,2,2,0,0,0,1],
  [1,1,0,0,0,2,0,2,1,2,1,0,2,2,1,0,1,0,0]
]

def cert0820n : CertifiedBoard :=
  ⟨seed0820, by apply FastValid.valid; decide +kernel⟩

def cert0820r : CertifiedBoard :=
  ⟨seed0820.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0821 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,1,1,1,1,0,1,1,0,0],
  [0,1,0,0,2,1,2,2,0,0,1,2,1,0,1],
  [2,0,2,1,2,0,1,0,2,2,0,0,2,1,0,2,0],
  [0,0,1,1,2,0,2,0,2,2,1,1,0,0,0,0,2,0,1]
]

def cert0821n : CertifiedBoard :=
  ⟨seed0821, by apply FastValid.valid; decide +kernel⟩

def cert0821r : CertifiedBoard :=
  ⟨seed0821.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0822 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,1,1,1,1,0,1,1,0,0],
  [1,2,0,2,0,2,1,2,2,0,1,2,1,0,1],
  [0,0,0,2,0,1,1,2,0,2,2,0,0,1,0,2,0],
  [2,0,0,1,0,2,1,0,0,0,2,1,1,0,0,2,2,1,2]
]

def cert0822n : CertifiedBoard :=
  ⟨seed0822, by apply FastValid.valid; decide +kernel⟩

def cert0822r : CertifiedBoard :=
  ⟨seed0822.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0823 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,1,1,1,1,0,1,1,0,2],
  [0,0,2,0,2,2,0,0,2,1,2,1,0,0,1],
  [2,0,2,1,1,0,0,0,1,1,2,2,1,2,0,0,0],
  [0,2,2,0,1,2,0,1,0,1,0,0,2,0,2,1,0,2,0]
]

def cert0823n : CertifiedBoard :=
  ⟨seed0823, by apply FastValid.valid; decide +kernel⟩

def cert0823r : CertifiedBoard :=
  ⟨seed0823.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0824 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,1,1,1,1,0,1,1,0,2],
  [0,2,0,0,2,1,0,0,2,1,2,2,0,2,0],
  [1,0,2,1,0,0,1,0,1,1,2,0,2,2,0,1,0],
  [2,0,2,2,1,2,0,0,0,1,2,1,1,0,0,0,2,0,1]
]

def cert0824n : CertifiedBoard :=
  ⟨seed0824, by apply FastValid.valid; decide +kernel⟩

def cert0824r : CertifiedBoard :=
  ⟨seed0824.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0825 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,1,1,1,1,0,1,1,0,2],
  [2,1,0,0,0,2,1,2,0,2,0,0,2,2,1],
  [1,0,0,0,1,0,2,2,0,1,1,2,0,0,2,1,0],
  [0,2,0,2,1,2,2,0,2,0,1,2,1,1,0,0,1,0,1]
]

def cert0825n : CertifiedBoard :=
  ⟨seed0825, by apply FastValid.valid; decide +kernel⟩

def cert0825r : CertifiedBoard :=
  ⟨seed0825.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0826 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,1,1,1,1,0,2,2,1,1],
  [2,0,0,0,0,2,1,2,1,0,1,1,2,2,0],
  [0,2,1,0,0,1,1,0,0,1,0,2,0,0,2,0,2],
  [1,1,0,0,2,1,2,0,2,0,1,2,0,2,2,0,1,0,1]
]

def cert0826n : CertifiedBoard :=
  ⟨seed0826, by apply FastValid.valid; decide +kernel⟩

def cert0826r : CertifiedBoard :=
  ⟨seed0826.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0827 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,1,1,1,2,0,1,1,1,0],
  [0,2,0,0,1,1,0,0,0,0,1,2,2,0,2],
  [1,0,0,2,1,2,1,2,0,1,0,1,0,2,2,0,2],
  [0,2,1,0,2,0,2,1,0,0,2,0,0,2,2,1,1,0,1]
]

def cert0827n : CertifiedBoard :=
  ⟨seed0827, by apply FastValid.valid; decide +kernel⟩

def cert0827r : CertifiedBoard :=
  ⟨seed0827.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0828 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,1,1,1,2,0,1,1,1,0],
  [0,2,2,0,2,1,0,0,0,0,1,2,1,2,0],
  [1,0,2,2,1,0,2,0,1,1,0,1,0,0,2,0,2],
  [2,0,0,2,1,1,0,0,2,0,2,1,2,2,0,0,1,0,1]
]

def cert0828n : CertifiedBoard :=
  ⟨seed0828, by apply FastValid.valid; decide +kernel⟩

def cert0828r : CertifiedBoard :=
  ⟨seed0828.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0829 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,1,1,1,2,0,1,1,1,0],
  [1,0,1,0,1,1,0,0,0,0,1,2,2,0,1],
  [0,2,0,2,1,2,1,2,0,0,2,0,0,2,2,0,2],
  [1,1,0,2,2,1,0,0,2,1,0,0,1,0,2,0,2,1,1]
]

def cert0829n : CertifiedBoard :=
  ⟨seed0829, by apply FastValid.valid; decide +kernel⟩

def cert0829r : CertifiedBoard :=
  ⟨seed0829.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0830 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,1,1,1,2,1,1,0,0,1],
  [2,2,0,2,0,1,0,0,0,0,2,1,0,2,0],
  [2,0,1,1,0,2,1,2,0,0,1,1,1,0,0,2,2],
  [2,2,1,2,0,0,2,1,0,1,0,1,2,2,0,2,0,2,2]
]

def cert0830n : CertifiedBoard :=
  ⟨seed0830, by apply FastValid.valid; decide +kernel⟩

def cert0830r : CertifiedBoard :=
  ⟨seed0830.map List.reverse, by apply FastValid.valid; decide +kernel⟩

def seed0831 : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,1,1,1,2,1,1,0,0,1],
  [2,2,0,2,0,1,0,0,0,0,2,1,0,2,0],
  [2,0,1,1,0,2,1,2,0,0,1,1,1,0,0,2,2],
  [2,2,1,2,2,0,2,1,0,1,0,1,2,0,0,2,0,2,2]
]

def cert0831n : CertifiedBoard :=
  ⟨seed0831, by apply FastValid.valid; decide +kernel⟩

def cert0831r : CertifiedBoard :=
  ⟨seed0831.map List.reverse, by apply FastValid.valid; decide +kernel⟩

end TBoards.Extended
