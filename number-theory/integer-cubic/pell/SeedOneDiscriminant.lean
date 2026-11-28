module

public import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Div
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.RingTheory.Polynomial.Resultant.Basic

public section

namespace SmallCubic

open Polynomial Matrix

/-- The derivative of a polynomial determinant is the sum of the determinants
in which one column is differentiated. -/
theorem derivative_det_columns {K ι : Type*} [CommRing K] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι K[X]) :
    A.det.derivative = ∑ j, (A.updateCol j (fun i => (A i j).derivative)).det := by
  simp_rw [Matrix.det_apply', derivative_sum, derivative_intCast_mul, derivative_prod_finset,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j), Matrix.updateCol_self]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  rw [Matrix.updateCol_ne (Finset.ne_of_mem_erase hi)]

private theorem det_updateCol_eq_zero_of_rank_lt {K : Type*} [Field K] {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) K) (h : A.rank < n)
    (j : Fin (n + 1)) (v : Fin (n + 1) → K) :
    (A.updateCol j v).det = 0 := by
  rw [Matrix.det_succ_column _ j]
  apply Finset.sum_eq_zero
  intro i _
  have hm : (A.submatrix i.succAbove j.succAbove).det = 0 := by
    by_contra hn
    have hr := Matrix.rank_of_det_ne_zero hn
    have hb := A.rank_submatrix_le i.succAbove j.succAbove
    rw [Fintype.card_fin] at hr
    omega
  have he : (A.updateCol j v).submatrix i.succAbove j.succAbove =
      A.submatrix i.succAbove j.succAbove := by
    ext a b
    exact Matrix.updateCol_ne (Fin.succAbove_ne j b)
  rw [he, hm, mul_zero]

/-- Corank at least two at a parameter value forces both the determinant
and its formal derivative to vanish at that value. -/
theorem det_and_derivative_vanish_of_corank_two {K : Type*} [Field K] {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) K[X]) (t : K)
    (hr : (A.map (Polynomial.eval t)).rank < n) :
    A.det.eval t = 0 ∧ A.det.derivative.eval t = 0 := by
  have evDet (B : Matrix (Fin (n + 1)) (Fin (n + 1)) K[X]) :
      B.det.eval t = (B.map (Polynomial.eval t)).det :=
    (Polynomial.evalRingHom t).map_det B
  constructor
  · rw [evDet]
    by_contra hn
    have hb := Matrix.rank_of_det_ne_zero hn
    rw [Fintype.card_fin] at hb
    omega
  · rw [derivative_det_columns, Polynomial.eval_finsetSum]
    apply Finset.sum_eq_zero
    intro j _
    rw [evDet, Matrix.map_updateCol]
    exact det_updateCol_eq_zero_of_rank_lt _ hr _ _

/-- The same corank hypothesis makes the parameter a root of multiplicity at
least two, expressed without an assumption that the determinant is nonzero. -/
theorem sq_dvd_det_of_corank_two {K : Type*} [Field K] {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) K[X]) (t : K)
    (hr : (A.map (Polynomial.eval t)).rank < n) :
    (X - C t) ^ 2 ∣ A.det := by
  obtain ⟨h, h'⟩ := det_and_derivative_vanish_of_corank_two A t hr
  obtain ⟨q, hq⟩ := Polynomial.dvd_iff_isRoot.mpr h
  rw [hq] at h'
  have hq' : q.eval t = 0 := by simpa using h'
  obtain ⟨r, hr'⟩ := Polynomial.dvd_iff_isRoot.mpr hq'
  exact ⟨r, by rw [hq, hr', pow_two, mul_assoc]⟩

/-- A common factor of degree d costs at least d in the rank of the
Sylvester matrix, since its image consists entirely of multiples of that factor. -/
theorem sylvester_rank_le_of_common_factor {K : Type*} [Field K] {m n : ℕ}
    (f g D : K[X]) (hf : f.natDegree ≤ m) (hg : g.natDegree ≤ n)
    (hD : D ≠ 0) (hd : D.natDegree ≤ m + n) (hDf : D ∣ f) (hDg : D ∣ g) :
    (f.sylvester g m n).rank ≤ m + n - D.natDegree := by
  let k := m + n - D.natDegree
  let mult : degreeLT K k →ₗ[K] degreeLT K (m + n) :=
    { toFun := fun p => ⟨D * p.val, by
        by_cases hp : p.val = 0
        · simp [hp]
        apply mem_degreeLT.mpr
        apply (natDegree_lt_iff_degree_lt (mul_ne_zero hD hp)).mp
        rw [natDegree_mul hD hp]
        have := (natDegree_lt_iff_degree_lt hp).mpr (mem_degreeLT.mp p.property)
        dsimp [k] at this
        omega⟩
      map_add' := by intro p q; ext1; exact mul_add _ _ _
      map_smul' := by intro c p; ext1; exact mul_smul_comm _ _ _ }
  have hr : LinearMap.range (sylvesterMap f g hf hg) ≤ LinearMap.range mult := by
    rintro v ⟨p, rfl⟩
    have hdiv : D ∣ f * p.2.val + g * p.1.val :=
      dvd_add (dvd_mul_of_dvd_left hDf _) (dvd_mul_of_dvd_left hDg _)
    obtain ⟨w, hw⟩ := hdiv
    have hwdeg : w ∈ degreeLT K k := by
      by_cases hwz : w = 0
      · simp [hwz]
      apply mem_degreeLT.mpr
      apply (natDegree_lt_iff_degree_lt hwz).mp
      have h := mem_degreeLT.mp ((sylvesterMap f g hf hg) p).property
      change (f * p.2.val + g * p.1.val).degree < _ at h
      rw [hw] at h
      have hb := (natDegree_lt_iff_degree_lt (mul_ne_zero hD hwz)).mpr h
      rw [natDegree_mul hD hwz] at hb
      dsimp [k]
      omega
    exact ⟨⟨w, hwdeg⟩, Subtype.ext hw.symm⟩
  rw [← toMatrix_sylvesterMap' f g hf hg, Matrix.rank_eq_finrank_range_toLin _
    (degreeLT.basis K (m + n)) (((degreeLT.basis K m).prod (degreeLT.basis K n)).reindex
      finSumFinEquiv), Matrix.toLin_toMatrix]
  calc
    _ ≤ Module.finrank K (LinearMap.range mult) := Submodule.finrank_mono hr
    _ ≤ Module.finrank K (degreeLT K k) := mult.finrank_range_le
    _ = k := by rw [Module.finrank_eq_card_basis (degreeLT.basis K k), Fintype.card_fin]

/-- If the specialized quintic has a squared quadratic factor, its resultant
with its derivative has a double root in the parameter. -/
theorem quintic_resultant_double_root {K : Type*} [Field K] (F : (K[X])[X])
    (t : K) (D : K[X]) (hd : D.natDegree = 2)
    (hdeg : (F.map (evalRingHom t)).natDegree ≤ 5)
    (hsq : D ^ 2 ∣ F.map (evalRingHom t)) :
    (X - C t) ^ 2 ∣ F.resultant F.derivative 5 4 := by
  let f := F.map (evalRingHom t)
  have hf : f.natDegree ≤ 5 := hdeg
  have hg : f.derivative.natDegree ≤ 4 := by
    have := f.natDegree_derivative_le
    omega
  have hD : D ≠ 0 := by rintro rfl; simp at hd
  have hd' : D.natDegree ≤ 5 + 4 := by omega
  have hdiv : D ∣ f.derivative := by
    simpa [f] using pow_sub_one_dvd_derivative_of_pow_dvd hsq
  have h := sylvester_rank_le_of_common_factor f f.derivative D hf hg hD hd'
    ((dvd_pow_self D (by decide : 2 ≠ 0)).trans hsq) hdiv
  change (X - C t) ^ 2 ∣ (F.sylvester F.derivative 5 4).det
  apply sq_dvd_det_of_corank_two (n := 8)
  have he : (F.sylvester F.derivative 5 4).map (eval t) =
      (f.sylvester f.derivative 5 4) := by
    rw [show f.derivative = F.derivative.map (evalRingHom t) from derivative_map _ _]
    exact (sylvester_map_map F F.derivative 5 4 (evalRingHom t)).symm
  rw [he]
  rw [hd] at h
  omega

end SmallCubic
