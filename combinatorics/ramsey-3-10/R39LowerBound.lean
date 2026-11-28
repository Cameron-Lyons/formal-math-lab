import CertVerify

/-!
# R39LowerBound.lean
Pure-kernel Lean 4 verification of Kalbfleisch's unique `R(3, 9, 35)` circulant
`C_35({1, 7, 11, 16})`, proving `R(3, 9) ≥ 36` via a 159-node clique-cover
certificate tree.
-/

namespace Ramsey310.R39

open Ramsey310.Cert

/-- Kalbfleisch's unique R(3, 9, 35)-graph: circulant `C_35({1, 7, 11, 16})`. -/
def c35Adj (u v : Fin 35) : Bool :=
  let d := (v.val + 35 - u.val) % 35
  d == 1 || d == 7 || d == 11 || d == 16 || d == 19 || d == 24 || d == 28 || d == 34

private theorem c35Adj_shift (shift u v : Fin 35) :
    c35Adj ⟨(u.val + shift.val) % 35, Nat.mod_lt _ (by decide)⟩
           ⟨(v.val + shift.val) % 35, Nat.mod_lt _ (by decide)⟩ = c35Adj u v := by
  simp only [c35Adj]
  have hmod : ((v.val + shift.val) % 35 + 35 - (u.val + shift.val) % 35) % 35 = (v.val + 35 - u.val) % 35 := by
    have hu := u.isLt; have hv := v.isLt; have hs := shift.isLt
    omega
  rw [hmod]

private def c35Cert : CertTree 35 :=
  (.branch 2 (.branch 4 (.branch 6 (.cover [(8,27),(10,29),(12,31),(14,33)] []) (.branch 33 (.cover [(8,27),(10,29),(12,31)] [25]) (.cover [(8,27),(12,31),(14,25),(17,10),(22,29)] []))) (.branch 22 (.branch 31 (.cover [(8,27),(10,17),(14,25)] [5]) (.cover [(5,12),(10,17),(14,25),(20,27),(8,32)] [])) (.branch 5 (.branch 8 (.cover [(10,17),(14,25),(20,31)] [23]) (.branch 31 (.cover [(10,17),(14,25)] [23,27]) (.cover [(10,17),(15,14),(20,27),(25,32)] [23]))) (.branch 31 (.branch 17 (.cover [(8,27),(14,25)] [23,29]) (.cover [(6,25),(8,27),(10,29),(14,33)] [23])) (.branch 8 (.branch 17 (.cover [(12,23),(14,25)] [20,29]) (.cover [(6,25),(10,29),(12,23),(14,33)] [20])) (.branch 14 (.cover [(6,17),(10,29),(12,23),(20,27)] [32]) (.branch 17 (.cover [(12,23),(20,27),(25,32)] [15,29]) (.cover [(6,25),(10,29),(12,23),(20,27),(32,33)] [15])))))))) (.branch 14 (.branch 4 (.branch 10 (.cover [(6,22),(8,27),(12,31)] [18]) (.branch 6 (.cover [(9,8),(12,31),(18,29),(26,27)] []) (.cover [(9,8),(12,31),(17,18),(22,29),(26,27)] []))) (.branch 10 (.branch 12 (.cover [(6,22),(20,27),(8,32)] [18]) (.branch 6 (.branch 8 (.cover [(20,31)] [18,23]) (.cover [(27,20),(31,32)] [18,23])) (.branch 8 (.cover [(20,31),(22,23)] [5,18]) (.cover [(22,23),(27,20),(31,32)] [5,18])))) (.branch 5 (.branch 8 (.cover [(17,18),(20,31),(22,23)] [26]) (.cover [(9,20),(17,18),(22,23),(26,27),(31,32)] [])) (.branch 8 (.branch 22 (.cover [(12,31),(17,18)] [26,20]) (.cover [(6,17),(18,29),(20,31),(12,23)] [26])) (.branch 20 (.branch 22 (.cover [(17,18)] [12,26,32]) (.cover [(6,17),(12,23),(18,29)] [26,32])) (.branch 22 (.cover [(12,31),(17,18),(26,27)] [9,32]) (.cover [(6,17),(18,29),(23,12),(26,27),(31,32)] [9]))))))) (.branch 22 (.branch 20 (.branch 25 (.cover [(5,12),(10,17)] [8,30]) (.cover [(5,12),(8,32),(18,17),(10,26)] [30])) (.branch 32 (.cover [(5,12),(9,10),(17,18),(26,27)] [30]) (.branch 9 (.cover [(4,5),(13,12),(17,18),(26,27),(30,31)] []) (.branch 12 (.branch 26 (.cover [(17,18)] [4,8,30]) (.cover [(8,27),(10,17),(18,25)] [4,30])) (.branch 26 (.cover [(4,5),(17,18),(30,31)] [8,13]) (.cover [(4,5),(8,27),(10,17),(18,25),(30,31)] [13])))))) (.branch 32 (.branch 10 (.branch 5 (.cover [(20,27),(23,30)] [15,18]) (.cover [(6,30),(12,23),(20,27)] [15,18])) (.branch 5 (.cover [(3,27),(9,20),(15,26),(17,18),(23,30)] []) (.branch 27 (.branch 30 (.cover [(17,18)] [9,12,15]) (.cover [(6,17),(12,23),(18,29)] [9,15])) (.branch 30 (.cover [(9,20),(15,26),(17,18)] [3,12]) (.cover [(6,17),(9,20),(12,23),(15,26),(18,29)] [3]))))) (.branch 5 (.branch 9 (.branch 31 (.cover [(17,18),(26,27)] [13,23]) (.cover [(3,27),(15,26),(17,18),(23,30)] [13])) (.branch 26 (.cover [(3,31),(13,20),(17,18),(23,30)] [8]) (.branch 31 (.cover [(8,27),(10,17),(18,25)] [13,23]) (.cover [(13,20),(15,8),(23,30),(25,18),(17,10),(3,27)] [])))) (.branch 10 (.branch 20 (.cover [(8,15),(12,23),(18,25),(6,30)] [33]) (.branch 6 (.branch 15 (.cover [(12,23)] [18,27,33]) (.cover [(4,23),(8,27),(12,31)] [18,33])) (.branch 12 (.cover [(4,15),(8,27),(18,25)] [30,33]) (.branch 15 (.cover [(18,25),(23,30)] [13,27,33]) (.cover [(4,23),(8,27),(18,25),(30,31)] [13,33]))))) (.branch 20 (.branch 6 (.cover [(8,15),(12,23),(18,29),(26,33)] [3]) (.branch 18 (.cover [(8,15),(12,23),(26,33)] [3,30]) (.cover [(8,15),(12,23),(17,33),(25,26),(29,30)] [3]))) (.branch 6 (.branch 15 (.cover [(3,27),(9,33),(12,23),(18,29)] [21]) (.branch 3 (.cover [(8,9),(12,23),(18,29),(26,33)] [21]) (.branch 8 (.cover [(4,23),(12,31),(18,29),(26,33)] [21]) (.cover [(4,23),(9,33),(12,31),(18,29),(26,27)] [21])))) (.branch 15 (.branch 18 (.cover [(3,27),(9,33),(13,12),(23,30)] [21]) (.branch 9 (.branch 12 (.cover [(3,27),(29,30)] [17,21]) (.cover [(3,27),(13,29),(23,30)] [17,21])) (.branch 12 (.cover [(3,27),(17,33),(29,30)] [21,25]) (.cover [(3,27),(13,29),(17,33),(23,30)] [21,25])))) (.branch 3 (.branch 9 (.branch 29 (.cover [(12,23)] [17,21,26]) (.cover [(13,12),(17,18),(23,30)] [21,26])) (.branch 18 (.cover [(13,12),(23,30),(26,33)] [8,21]) (.branch 12 (.cover [(17,33),(25,26),(29,30)] [8,21]) (.cover [(13,29),(17,33),(23,30),(25,26)] [8,21])))) (.branch 9 (.branch 12 (.cover [(17,18),(26,27),(29,30)] [4,21]) (.cover [(4,23),(13,29),(17,18),(26,27),(30,31)] [21])) (.branch 12 (.branch 18 (.cover [(8,27),(26,33)] [4,21,30]) (.cover [(8,27),(17,33),(25,26),(29,30)] [4,21])) (.branch 18 (.cover [(4,23),(8,27),(26,33),(30,31)] [13,21]) (.cover [(4,23),(8,27),(13,29),(17,33),(25,26),(30,31)] [21]))))))))))))))

private theorem c35_simple_trifree : checkSimpleTriFree c35Adj = true := by decide

private theorem c35_cert_ok : checkCert c35Adj
    ((List.finRange 35).filter (fun x => x.val != 0 && !(c35Adj ⟨0, by decide⟩ x)))
    8 c35Cert = true := by decide

/-- Pure-kernel proof that `C_35({1, 7, 11, 16})` is a simple, triangle-free 35-vertex graph
    with no independent 9-set (`R(3, 9) ≥ 36`). -/
theorem r39_witness :
    Simple c35Adj ∧ TriangleFree c35Adj ∧
      ∀ s, Independent c35Adj s → orderOf s < 9 :=
  let ⟨hs, htf⟩ := simpleTriFree_of_check c35_simple_trifree
  ⟨hs, htf, orderOf_lt_of_circulant_checkCert (by decide) c35Adj_shift c35Cert c35_cert_ok⟩

end Ramsey310.R39
