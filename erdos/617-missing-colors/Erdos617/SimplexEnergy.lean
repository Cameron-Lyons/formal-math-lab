module

public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Ring

@[expose] public section

namespace Erdos617

open Finset Matrix

private theorem slope_at_zero {a b : ℝ}
    (h : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → 0 ≤ ε*(a+ε*b)) : 0 ≤ a := by
  by_contra! ha
  let ε := min 1 ((-a)/(2*(|b|+1)))
  have den : 0 < 2*(|b|+1) := by positivity
  have hp : 0 < ε := lt_min (by norm_num) (div_pos (neg_pos.mpr ha) den)
  have he := (le_div_iff₀ den).mp (min_le_right (1:ℝ) ((-a)/(2*(|b|+1))))
  change ε*(2*(|b|+1)) ≤ -a at he
  have hab := mul_le_mul_of_nonneg_left (le_abs_self b) hp.le
  have hpos := nonneg_of_mul_nonneg_right (h ε hp (min_le_left ..)) hp
  nlinarith only [he,hab,hpos,ha,mul_nonneg hp.le (abs_nonneg b),hp]

/-- A symmetric quadratic form has a minimum on probability vectors.
Every positive coordinate of a minimizing vector has the same linear potential. -/
theorem simplex_energy_equilibrium {V : Type*} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℝ) (hsymm : Aᵀ=A) (x : V → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hxsum : ∑ i, x i = 1) :
    ∃ w : V → ℝ, (∀ i, 0 ≤ w i) ∧ (∑ i,w i)=1 ∧
      (∀ i, 0 < w i → (A *ᵥ w) i = w ⬝ᵥ (A *ᵥ w)) ∧
      w ⬝ᵥ (A *ᵥ w) ≤ x ⬝ᵥ (A *ᵥ x) := by
  classical
  let S := Set.Icc (0 : V → ℝ) 1 ∩ {y : V → ℝ | ∑ i,y i=1}
  let Q (y : V → ℝ) := y ⬝ᵥ (A *ᵥ y)
  have compact : IsCompact S := isCompact_Icc.inter_right (isClosed_eq (by fun_prop) continuous_const)
  have mem {y : V → ℝ} (hn : ∀ i, 0≤y i) (h1 : ∑ i,y i=1) : y∈S :=
    ⟨⟨hn,fun i => (single_le_sum (fun j _ => hn j) (mem_univ i)).trans h1.le⟩,h1⟩
  have cont : Continuous Q := by
    dsimp [Q, dotProduct, Matrix.mulVec]
    fun_prop
  obtain ⟨w,hw,hmin⟩ := compact.exists_isMinOn ⟨x,mem hx hxsum⟩ cont.continuousOn
  have lower (i : V) : Q w ≤ (A *ᵥ w) i := by
    let v : V → ℝ := Pi.single i 1
    have cross : w ⬝ᵥ (A *ᵥ v) = (A *ᵥ w) i := by
      rw [← hsymm, dotProduct_transpose_mulVec, hsymm]
      exact single_one_dotProduct i (A *ᵥ w)
    have hf : 0 ≤ 2*((A *ᵥ w) i-Q w) := by
      apply slope_at_zero (b:=Q v+Q w-2*(A *ᵥ w) i)
      intro ε he hε
      let y := (1-ε) • w + ε • v
      have ymem : y∈S := by
        apply mem
        · intro j
          change 0 ≤ (1-ε)*w j + ε*v j
          have hv : 0≤v j := by by_cases h : j=i <;> simp [v,h]
          exact add_nonneg (mul_nonneg (sub_nonneg.mpr hε) (hw.1.1 j)) (mul_nonneg he.le hv)
        · change (∑ j, ((1-ε)*w j+ε*v j))=1
          rw [sum_add_distrib,←mul_sum,←mul_sum,hw.2]
          simp [v,Pi.single_apply]
      have minim := hmin ymem
      change Q w ≤ y ⬝ᵥ (A *ᵥ y) at minim
      simp only [y,Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct, dotProduct_add,
        smul_dotProduct, dotProduct_smul, smul_eq_mul, cross] at minim
      change Q w ≤ (1-ε)*((1-ε)*Q w+ε*(Pi.single i 1 ⬝ᵥ (A *ᵥ w))) +
        ε*((1-ε)*(A *ᵥ w) i+ε*Q v) at minim
      rw [single_one_dotProduct] at minim
      nlinarith only [minim]
    linarith
  have per (i : V) (_ : i ∈ univ) : w i*Q w ≤ w i*(A *ᵥ w) i :=
    mul_le_mul_of_nonneg_left (lower i) (hw.1.1 i)
  have sumEq : (∑ i,w i*Q w) = ∑ i,w i*(A *ᵥ w) i := by rw [←sum_mul,hw.2,one_mul]; rfl
  refine ⟨w,hw.1.1,hw.2,?_,hmin (mem hx hxsum)⟩
  intro i hi
  exact (mul_left_cancel₀ hi.ne' ((sum_eq_sum_iff_of_le per).mp sumEq i (mem_univ i))).symm

end Erdos617
