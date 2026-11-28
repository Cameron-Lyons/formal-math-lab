module

public import UCBound.CertConst
public import UCBound.Cert1D
public import UCBound.CertCov
public import UCBound.CertF
public import UCBound.CertPolytope

@[expose] public section

/-!
# Main Theorem: Certified Lower Bound `1533 / 4000 = 0.38325` for Frankl's Union-Closed Sets Conjecture

Assembles the ground-set reduction (`unionClosed_to_andClosed`), the 3-vertex single-order
master contradiction (`master_contradiction`), the kernel-certified local 1D/2D/covariance
inequalities (`localInequalities_proof`), and the kernel-certified 2D polytope positivity
bounds (`polytope_G`, `polytope_T`) to prove:

Every finite union-closed family `F` containing a nonempty set has an element belonging to
at least `(1533 / 4000) * |F| = 0.38325 * |F|` sets of `F`.
-/

namespace UCBound

open UCBound.Cert UCBound.Cert2D

/-- Assembled kernel-verified local 1D, 2D, and covariance inequalities. -/
theorem localInequalities_proof : LocalInequalities where
  htau0 := tau_pos
  htau1 := tau_lt_half
  hD0 := DParam_pos
  hD_lt_kappa := DParam_lt_kappa
  hR_nonneg := cert_R_nonneg
  hR_le_phi := cert_R_le_phi
  hSigned := cert_Signed
  hb_mem := cert_b_mem
  hBopp2D := cert_Bopp2D
  hLine1 := cert_Line1
  hSqrtLB := cert_SqrtLB
  hF_R := cert_F_R
  hF_v := cert_F_v
  hF_sim := cert_F_sim
  hCov := cert_Cov cert_R_nonneg

/-- **Main Theorem (Frankl's Union-Closed Sets Conjecture, Certified Bound `1533/4000 = 0.38325`)**:
    In any finite union-closed family `F` containing at least one nonempty set, some element `a`
    appears in at least `(1533 / 4000) * |F|` members of `F`. -/
theorem frankl_union_closed_bound
    {α : Type*} [DecidableEq α]
    (F : Finset (Finset α))
    (hUC : UnionClosed F)
    (hNE : ∃ A ∈ F, A.Nonempty) :
    ∃ a : α, (1533 : ℝ) / 4000 * (F.card : ℝ) ≤ ((F.filter (fun A => a ∈ A)).card : ℝ) := by
  by_contra h
  push Not at h
  have hc_lt : (1533 : ℝ) / 4000 < cStar + epsParam := cStar_add_eps_gt
  have hbad : ∀ a : α, ((F.filter (fun A => a ∈ A)).card : ℝ) < (cStar + epsParam) * (F.card : ℝ) := by
    intro a
    have hF0 : (0 : ℝ) < (F.card : ℝ) := by
      rcases hNE with ⟨A, hAF, _⟩
      exact_mod_cast Finset.card_pos.mpr ⟨A, hAF⟩
    have h1 := h a
    nlinarith
  have hc1 : cStar + epsParam ≤ 1 := by
    have hm_gt : (6 / 10 : ℝ) < mStar := by
      have ht : Iv.mem (Iv.ofRat 6 10) (6 / 10 : ℝ) := by convert Iv.mem_ofRat (p := 6) (q := 10) (by norm_num)
      exact lt_of_hi_lt_lo ht validConstIv.hm_mem (by decide)
    unfold epsParam; linarith [cStar_add_mStar]
  rcases unionClosed_to_andClosed F hUC hNE hc1 hbad with ⟨n, Ω, hΩ2, hAC, hmarg⟩
  have hs_min : ∀ i : Fin n, mStar - epsParam ≤ margProb Ω i := by
    intro i
    have hi := hmarg i
    have heq : 1 - (cStar + epsParam) = mStar - epsParam := by linarith [cStar_add_mStar]
    rw [heq] at hi
    rw [margProb_eq_card_div]
    linarith
  exact master_contradiction Ω hΩ2 hAC hs_min localInequalities_proof polytope_G polytope_T

end UCBound
