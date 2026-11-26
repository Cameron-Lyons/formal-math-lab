module

public import Wall133.LabelledPathCertificate
public import Wall133.FifthResolution
public import Wall133.ShortGirthFifthData

@[expose] public section

namespace Wall133.FifthCertificate
open SimpleGraph LabelledPathCertificate

private def rules : List Rule := [
  .path 0 1 2 3 4 5 10 18, .path 0 1 2 3 4 5 10 19, .path 5 4 3 2 1 0 6 12,
  .path 5 4 3 2 1 0 6 13, .path 5 4 3 2 1 0 7 14, .path 5 4 3 2 1 0 7 15,
  .path 5 4 3 2 1 0 8 16, .path 5 4 3 2 1 0 8 17, .path 6 0 1 2 3 4 5 10,
  .path 6 0 1 2 3 4 5 11, .path 7 0 1 2 3 4 5 10, .path 8 0 1 2 3 4 5 10,
  .path 8 0 1 2 3 4 5 11, .path 9 0 1 2 3 4 5 10, .path 9 0 1 2 3 4 5 11,
  .square 0 10 6 7, .square 0 10 6 8, .square 0 10 6 9,
  .square 0 11 1 7, .square 0 11 6 8, .square 0 11 6 9,
  .square 0 12 1 6, .square 0 12 6 7, .square 0 12 6 8,
  .square 0 12 6 9, .square 0 13 1 6, .square 0 13 6 7,
  .square 0 13 6 8, .square 0 13 6 9, .square 0 14 1 7,
  .square 0 14 6 7, .square 0 15 1 7, .square 0 15 6 7,
  .square 0 16 1 8, .square 0 16 6 8, .square 0 16 8 9,
  .square 0 17 1 8, .square 0 17 6 8, .square 0 17 8 9,
  .transfer 18 0 10, .transfer 19 0 10, .square 1 10 18 19,
  .transfer 1 12 0, .transfer 1 13 0, .transfer 1 18 19,
  .transfer 19 1 3, .transfer 19 1 6, .square 2 6 12 13,
  .square 2 8 16 17, .transfer 12 2 6, .transfer 13 2 6,
  .transfer 14 2 7, .transfer 15 2 7, .transfer 16 2 8,
  .transfer 17 2 8, .square 3 6 12 13, .transfer 12 3 6,
  .transfer 13 3 6, .transfer 16 3 8, .transfer 18 3 10,
  .transfer 19 3 10, .square 4 10 5 18, .square 4 10 5 19,
  .transfer 12 4 6, .transfer 13 4 6, .transfer 14 4 7,
  .transfer 15 4 7, .transfer 16 4 2, .transfer 16 4 8,
  .transfer 16 4 10, .transfer 17 4 8, .transfer 4 18 5,
  .transfer 4 19 5, .square 5 6 12 13, .transfer 13 5 6,
  .transfer 16 5 8, .transfer 17 5 8, .square 5 18 10 11,
  .square 5 19 10 11, .transfer 6 10 0, .transfer 11 6 5,
  .transfer 6 16 0, .transfer 11 8 5, .transfer 8 12 0,
  .transfer 9 10 0, .transfer 11 9 7, .square 10 11 5 6,
  .transfer 12 10 3, .transfer 10 13 12, .transfer 13 10 4,
  .transfer 11 12 13, .transfer 12 11 2, .transfer 13 11 2,
  .transfer 13 11 4, .transfer 13 11 10, .square 12 13 4 6,
  .square 14 15 2 7, .square 14 15 4 7, .square 14 15 5 7,
  .square 16 17 3 8, .square 16 17 4 8, .square 16 17 5 8,
  .square 18 19 0 10, .square 18 19 2 10, .square 0 3 7 18,
  .square 0 4 7 8, .square 0 10 1 6, .square 0 18 1 7,
  .square 0 18 1 8, .square 1 12 2 10, .square 1 18 0 10,
  .square 1 18 2 10, .square 2 7 3 18, .square 3 8 4 18,
  .square 3 10 2 12, .square 3 10 2 14, .square 3 10 2 16,
  .square 3 12 2 14, .square 4 14 3 5, .square 4 16 3 5,
  .square 4 16 3 8, .square 4 16 5 8, .square 4 16 8 12,
  .square 5 6 10 13, .square 5 16 4 10, .square 6 10 12 13,
  .square 6 11 0 12, .square 6 16 12 13, .square 6 18 12 13,
  .square 7 9 0 4, .square 8 9 0 4, .square 8 11 0 16,
  .square 9 10 5 18, .square 9 11 0 5, .square 10 11 1 5,
  .square 10 12 2 6, .path 5 4 3 2 1 0 6 19, .path 11 0 8 4 3 2 10 13,
  .square 0 10 1 9, .transfer 1 18 0, .transfer 4 16 3,
  .transfer 18 6 10, .transfer 19 6 10, .transfer 18 7 10,
  .transfer 10 13 5, .transfer 15 10 7, .transfer 17 10 8,
  .transfer 13 17 6, .path 0 6 12 3 4 5 10 18, .path 0 6 12 3 4 5 10 19,
  .path 1 2 13 6 11 5 4 8, .path 3 4 5 10 1 0 6 13, .path 7 0 8 4 5 10 2 13,
  .path 8 0 7 3 2 10 5 11, .square 0 10 1 7, .square 0 19 6 7,
  .square 0 19 6 8, .square 2 7 3 10, .square 3 5 4 12,
  .square 3 10 2 17, .square 4 17 3 5, .square 4 17 3 13,
  .square 5 13 4 10, .square 5 13 4 17, .square 5 17 4 10,
  .square 6 11 0 13, .square 8 11 0 17, .square 9 10 5 19,
  .square 10 12 2 5, .square 10 15 5 13, .path 5 4 3 2 16 8 0 6,
  .square 0 10 1 8, .square 3 13 2 4, .path 5 4 3 2 17 8 0 6,
  .path 6 0 1 10 5 4 3 16, .path 1 0 6 12 3 4 5 10, .path 1 0 6 12 3 4 5 17,
  .path 1 0 11 5 4 3 12 19, .path 2 3 4 5 17 8 0 6, .path 2 13 6 0 9 5 4 16,
  .path 5 4 3 2 13 6 0 8, .square 13 17 2 5, .path 2 3 19 10 5 11 0 8,
  .path 5 10 19 3 12 6 0 8, .path 6 0 1 10 16 3 4 17, .path 6 0 11 5 17 2 3 16,
  .path 6 12 3 2 1 10 5 9, .path 8 0 1 10 5 4 3 12, .square 2 16 3 13,
  .path 1 0 8 16 3 4 5 10, .path 8 0 11 5 13 2 3 12, .square 3 5 4 13,
  .path 8 0 1 2 13 5 4 12, .path 2 3 4 5 16 8 0 6, .path 2 3 7 0 11 5 10 18,
  .path 2 3 7 0 11 5 10 19, .path 2 13 6 0 8 16 5 10, .path 6 12 5 10 1 2 3 7,
  .path 8 0 1 2 3 4 5 12, .path 8 0 6 13 3 4 5 10, .square 3 16 4 13,
  .square 10 13 2 6, .path 1 0 8 17 3 4 5 10, .path 1 2 13 6 12 4 5 9,
  .square 0 10 1 19, .path 1 2 12 6 13 4 5 9, .path 3 4 5 10 1 0 6 12,
  .path 3 4 13 6 0 1 10 18, .path 3 4 13 6 0 19 10 18, .path 5 4 3 2 12 6 0 8,
  .path 2 3 18 10 5 11 0 8, .path 6 0 1 2 3 4 5 14, .path 6 0 1 2 16 5 4 17,
  .transfer 12 10 6, .path 1 2 17 8 16 4 13 6, .path 2 17 8 0 6 13 4 5,
  .square 3 19 2 12, .path 1 0 6 13 5 4 3 17, .path 1 2 3 12 6 13 5 9,
  .path 1 2 3 12 6 13 5 11, .path 2 3 7 0 6 13 5 10, .path 2 3 12 10 5 11 0 8,
  .path 6 0 1 10 5 4 3 17, .path 8 0 1 2 3 4 5 13, .path 2 3 13 10 5 9 0 8,
  .path 2 3 13 10 5 11 0 8, .path 2 3 17 10 5 11 0 6, .path 8 0 1 10 13 3 4 12,
  .path 9 0 1 10 13 3 4 16, .square 4 10 5 8, .path 1 0 6 13 3 4 5 10,
  .path 5 4 3 2 12 6 0 9, .path 9 0 6 13 3 4 5 10, .square 11 12 5 6,
  .path 2 10 5 4 13 6 0 7, .path 3 2 16 8 0 6 12 5, .path 1 0 6 13 10 5 4 3,
  .path 1 2 13 6 12 5 4 8, .square 2 5 10 15, .square 3 10 2 13,
  .path 1 0 6 13 3 4 5 15, .square 0 19 1 7, .path 3 2 12 5 9 0 8 16,
  .path 8 0 7 3 2 12 5 10, .square 2 15 3 12, .square 4 15 3 5,
  .path 4 3 2 19 10 18 0 9, .path 7 3 2 12 6 13 5 9, .path 2 19 10 5 4 8 0 7,
  .path 6 0 1 2 3 4 5 15, .square 3 8 4 19, .square 0 13 6 19,
  .path 2 18 10 5 4 8 0 7, .path 4 5 10 18 2 1 0 7, .square 2 7 3 19,
  .path 2 3 7 0 6 10 5 11, .path 1 0 7 15 3 4 5 12, .path 2 1 10 12 6 13 4 8,
  .path 2 3 4 5 12 6 0 7, .path 2 3 13 6 0 9 5 10, .path 5 4 3 2 14 7 0 6,
  .path 1 0 7 15 3 4 5 10, .path 7 0 1 2 10 5 4 12, .path 8 0 9 5 10 2 3 13,
  .path 8 0 11 5 10 2 3 13, .path 5 4 3 2 15 7 0 6, .square 4 11 5 8,
  .path 1 0 6 12 5 4 3 14, .path 1 0 7 14 3 4 5 10, .path 7 0 1 2 10 5 4 13,
  .path 7 0 1 2 12 5 4 13, .square 2 5 10 17, .square 3 10 2 15,
  .path 1 0 8 17 12 3 4 13, .path 2 17 5 4 13 6 0 9, .square 10 13 5 17,
  .path 3 2 10 5 13 6 0 8, .square 5 6 11 13, .path 1 2 13 6 12 4 8 16,
  .path 6 13 10 1 2 3 4 8, .square 1 13 2 10, .path 2 13 16 8 0 11 5 12,
  .path 5 4 3 2 13 6 0 7, .path 0 6 18 10 5 4 3 2, .path 6 0 1 2 14 5 4 15,
  .path 7 0 1 2 13 5 4 12, .path 2 3 4 5 13 6 0 7, .path 2 3 4 5 13 6 0 9]

set_option maxRecDepth 32768 in
private theorem bounded : fits 20 inputs rules = true := by decide

set_option maxRecDepth 32768 in
private theorem encoding : formulaOf 20 inputs rules = formula := by rfl

set_option maxRecDepth 4096 in
private theorem noTip : rules.all (fun r => match r with | .tip _ => false | _ => true) = true := by decide

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- The listed local graph facts force an induced path on eight vertices. -/
theorem eight_of_certificate (f : ℕ → V) (h4 : NoFourCycle G)
    (facts : ∀ t∈inputs,Holds G f t) : 8≤G.path := by
  apply eight_of_unsat 20 inputs rules bounded (encoding ▸ formula_unsat) f h4 _ facts
  intro i hi
  exact False.elim (Bool.noConfusion (List.all_eq_true.mp noTip (.tip i) hi))

end Wall133.FifthCertificate
