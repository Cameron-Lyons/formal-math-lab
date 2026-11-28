module

public import Wall133.LabelledPathCertificate
public import Wall133.FourthResolution
public import Wall133.ShortGirthCertificateData

@[expose] public section

namespace Wall133.FourthCertificate
open SimpleGraph LabelledPathCertificate

private def rules : List Rule := [
  .tip 14, .tip 15, .tip 16,
  .tip 17, .path 4 3 2 1 0 5 8 14, .path 4 3 2 1 0 5 8 15,
  .path 4 3 2 1 0 5 9 16, .path 4 3 2 1 0 5 9 17, .square 0 8 5 15,
  .square 0 9 5 16, .square 0 9 5 17, .transfer 0 14 5,
  .transfer 0 15 5, .transfer 0 16 5, .transfer 0 17 5,
  .transfer 2 14 15, .transfer 2 16 17, .transfer 16 2 4,
  .transfer 16 2 7, .transfer 16 2 10, .transfer 2 17 16,
  .transfer 14 3 8, .transfer 15 3 8, .transfer 16 3 9,
  .transfer 17 3 9, .transfer 5 13 0, .square 5 14 8 9,
  .square 5 15 8 9, .square 5 16 8 9, .square 5 17 8 9,
  .transfer 6 9 0, .transfer 7 8 0, .transfer 10 9 6,
  .transfer 11 9 6, .transfer 10 17 16, .square 14 15 3 8,
  .square 16 17 1 9, .square 16 17 2 9, .square 16 17 3 9,
  .square 0 8 5 6, .square 0 8 5 7, .square 0 8 5 14,
  .square 0 9 5 6, .square 0 9 5 7, .square 0 10 5 6,
  .square 0 10 6 7, .square 0 11 5 6, .square 0 11 6 7,
  .square 0 12 5 7, .square 0 12 6 7, .square 0 13 5 7,
  .square 0 13 6 7, .square 0 14 1 6, .square 0 14 1 7,
  .square 0 14 6 7, .square 0 15 1 6, .square 0 16 1 6,
  .square 0 16 1 7, .square 0 16 6 7, .square 1 8 14 15,
  .square 2 6 10 11, .square 2 8 3 10, .square 2 8 3 11,
  .square 2 9 3 12, .square 2 11 3 8, .square 2 11 3 16,
  .square 2 14 1 8, .square 2 15 1 8, .square 2 16 1 9,
  .square 3 5 8 9, .square 3 6 10 11, .square 3 8 2 10,
  .square 3 8 2 12, .square 3 8 2 13, .square 3 8 2 14,
  .square 3 9 2 10, .square 3 9 2 11, .square 3 9 2 16,
  .square 5 13 8 9, .square 6 9 16 17, .square 7 8 12 13,
  .square 8 9 2 5, .square 10 17 6 9, .square 11 17 6 9,
  .square 12 13 2 7, .transfer 2 14 3, .square 9 11 16 17,
  .path 6 0 1 16 9 17 3 8, .square 0 15 6 7, .path 4 3 2 12 7 0 5 9,
  .path 4 3 2 17 9 5 0 7, .path 4 3 11 16 9 5 0 7, .path 4 3 2 12 9 5 0 6,
  .path 4 3 2 17 9 5 0 6, .transfer 2 15 3, .transfer 11 17 2,
  .path 4 3 2 16 9 5 0 6, .path 4 3 2 16 9 5 0 7, .path 4 3 2 9 5 0 6 10,
  .path 4 3 2 9 5 0 6 11, .path 4 3 2 8 5 0 6 10, .path 4 3 2 8 5 0 6 11,
  .path 4 3 2 8 5 0 7 12, .path 4 3 2 8 5 0 7 13, .path 4 3 11 6 0 5 8 14,
  .path 4 3 12 7 0 5 8 14, .path 4 3 12 7 0 5 8 15, .path 4 3 10 6 0 5 9 16,
  .path 4 3 10 6 0 5 9 17, .path 4 3 10 6 0 5 8 14, .path 4 3 13 7 0 5 8 14,
  .path 4 3 13 7 0 5 8 15, .path 4 3 9 5 8 13 7 12, .path 4 3 2 10 6 0 5 8,
  .path 6 0 1 15 8 14 3 9, .path 7 0 1 15 8 14 3 9, .path 4 3 2 10 8 5 0 7,
  .path 4 3 2 9 11 6 0 7, .path 4 3 2 9 10 6 0 7, .path 4 3 2 14 8 5 0 6,
  .path 4 3 2 14 8 5 0 7, .path 4 3 11 6 0 5 9 16, .path 4 3 11 6 0 5 9 17,
  .path 4 3 2 11 6 0 5 8, .path 4 3 2 15 8 5 0 6, .path 4 3 2 15 8 5 0 7,
  .path 4 3 2 11 8 5 0 7, .path 6 0 1 14 8 15 3 9, .path 7 0 1 14 8 15 3 9,
  .square 0 15 1 7, .square 2 17 1 9, .path 4 3 13 15 8 5 0 6,
  .path 1 0 5 8 14 10 3 4, .path 1 0 5 8 14 13 3 4, .path 4 3 2 8 11 6 0 7,
  .path 4 3 2 8 12 7 0 6, .path 4 3 16 9 10 6 0 7, .path 4 3 16 9 5 0 6 11,
  .path 6 0 1 17 9 16 3 8, .path 7 0 1 17 9 16 3 8, .path 4 3 2 1 17 9 5 8,
  .square 2 17 3 9, .path 7 0 6 16 9 2 3 8, .path 1 0 5 8 14 11 3 4,
  .path 1 0 5 8 14 12 3 4, .path 4 3 2 8 10 6 0 7, .path 4 3 2 8 15 7 0 6,
  .square 0 17 1 6, .path 4 3 8 5 9 17 6 10, .path 4 3 8 5 9 17 6 11,
  .path 4 3 16 9 5 0 6 10, .path 7 0 1 16 9 17 3 8, .square 0 17 6 7,
  .square 9 10 16 17, .path 1 0 5 9 16 10 3 4, .path 1 0 5 9 17 10 3 4,
  .path 4 3 2 9 16 7 0 6, .path 6 0 7 17 9 2 3 8, .square 0 17 1 7,
  .path 4 3 2 1 16 9 5 8, .path 1 0 5 8 15 12 3 4, .path 4 3 2 8 15 6 0 7,
  .path 4 3 11 17 9 5 0 7]

set_option maxRecDepth 32768 in
private theorem bounded : fits 18 inputs rules = true := by decide

set_option maxRecDepth 32768 in
private theorem encoding : formulaOf 18 inputs rules = formula := by rfl

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- The listed local graph facts force an induced path on eight vertices. -/
theorem eight_of_certificate (f : ℕ → V) (h4 : NoFourCycle G)
    (simplicial : ∀ z,G.Adj z (f 4) → z≠f 3 → G.Adj z (f 3))
    (facts : ∀ t∈inputs,Holds G f t) : 8≤G.path := by
  apply eight_of_unsat 18 inputs rules bounded (encoding ▸ formula_unsat) f h4 _ facts
  exact fun i _ => simplicial (f i)

end Wall133.FourthCertificate
