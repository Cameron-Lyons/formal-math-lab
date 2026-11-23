module

public import ArctanDeterminant

public section

namespace Arxiv.«2607.05739»

private theorem exp_quadratic {z : ℝ} (hz : |z| ≤ 1) :
    ∃ v : ℝ, |v| ≤ 1 ∧ Real.exp z = 1+z+z^2/2+v*z^3 := by
  by_cases hz0 : z = 0
  · subst z; exact ⟨0, by norm_num, by norm_num⟩
  have hb := Real.exp_bound hz (n := 3) (by decide)
  norm_num [Finset.sum_range_succ, Nat.factorial] at hb
  refine ⟨(Real.exp z-(1+z+z^2/2))/z^3, ?_, ?_⟩
  · rw [abs_div, abs_pow, div_le_one (pow_pos (abs_pos.mpr hz0) _)]
    linarith [pow_nonneg (abs_nonneg z) 3]
  · field_simp; ring

/-- Cubic coefficient in exp(w*(5/24+w*(-19/192+d*w))). -/
private noncomputable def cubicCoeff (w d v : ℝ) :=
  let t := -19/192 + d*w
  let s := 5/24 + w*t
  d + (5/24)*t + w*t^2/2 + v*s^3

private noncomputable def ratioModel (w u : ℝ) :=
  1+w*(5/24+w*(-19/192+(5/24)^2/2+w*u))

/-- Clearing the denominator of the inverse formula makes the remaining
error a polynomial in the scale and the cubic Taylor coefficient. -/
private noncomputable def inverseRemainder (w u : ℝ) :=
  let v := -19/192 + (5/24)^2/2 + w*u
  let t := 5/24 + w*v
  (-(1+w*t)^2) * (2*u+(6*(t+5/24)+2*inverseCoeffOne)*v +
    6*t^3+inverseCoeffOne*t^2+2*w*t^4)

private theorem remainder_identity (w u : ℝ) :
    let r := ratioModel w u
    r^2*(2*r^3-2*r^4-inverseCoeffOne*w*r^2-inverseCoeffThree*w^2)
      = inverseRemainder w u*w^3 := by
  dsimp [ratioModel, inverseRemainder, inverseCoeffOne, inverseCoeffThree]
  ring

/-- Invert the centered phase expansion uniformly when its input differs from
the desired phase by at most K/h⁶. -/
theorem inverse_phase_estimate (K : ℝ) (hK : 0 ≤ K) :
    ∃ E : ℝ, 0 ≤ E ∧ ∃ H₀ : ℝ, 1 ≤ H₀ ∧ ∀ {h y : ℝ}, H₀ ≤ h → 0 < y →
      |Real.log (y/h) - (5/24)/h^2 + (19/192)/h^4| ≤ K/h^6 →
      h ≤ Real.exp 1*y ∧ y ≤ Real.exp 1*h ∧ InversePhaseApprox E y (2*h) := by
  let box := Set.Icc (0:ℝ) 1 ×ˢ (Set.Icc (-K) K ×ˢ Set.Icc (-1:ℝ) 1)
  have hc : IsCompact box := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hf : Continuous (fun p : ℝ × ℝ × ℝ =>
      inverseRemainder p.1 (cubicCoeff p.1 p.2.1 p.2.2)) := by
    unfold inverseRemainder cubicCoeff; fun_prop
  obtain ⟨E,hE⟩ := hc.exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max E 0, le_max_right .., K+2, by linarith, ?_⟩
  intro h y hlarge hy happ
  have hh : 1 ≤ h := by linarith
  have hh0 : 0 < h := by linarith
  let w := 1/h^2
  let z := Real.log (y/h)
  let d := (z - (5/24)/h^2 + (19/192)/h^4)*h^6
  have hd : |d| ≤ K := by
    dsimp [d,z]; rw [abs_mul, abs_of_pos (pow_pos hh0 _)]
    exact (le_div_iff₀ (pow_pos hh0 _)).mp happ
  have hw : 0 < w := by dsimp [w]; positivity
  have hw₁ : w ≤ 1 := (div_le_one (pow_pos hh0 2)).mpr (one_le_pow₀ hh)
  have hwK : (K+2)*w ≤ 1 := by
    dsimp [w]; field_simp; nlinarith [mul_nonneg (sub_nonneg.mpr hh) hh0.le]
  have hz : z = w*(5/24 + w*(-19/192 + d*w)) := by dsimp [w,d]; field_simp; ring
  have hwabs : |w| ≤ 1 := by rwa [abs_of_pos hw]
  have ht : |(-19/192 : ℝ)+d*w| ≤ 1+K := calc
    _ ≤ |(-19/192 : ℝ)| + |d| *|w| := by rw [← abs_mul]; exact abs_add_le ..
    _ ≤ 1+K*1 := by gcongr; norm_num
    _ = _ := by ring
  have hz₁ : |z| ≤ 1 := calc
    _ ≤ w*(|(5/24:ℝ)| + |w| *|(-19/192:ℝ)+d*w|) := by
      rw [hz, abs_mul, abs_of_pos hw]
      apply mul_le_mul_of_nonneg_left _ hw.le
      simpa only [abs_mul, abs_of_pos hw] using (abs_add_le (5/24:ℝ) (w*(-19/192+d*w)))
    _ ≤ w*(1+1*(1+K)) := by gcongr; norm_num
    _ = (K+2)*w := by ring
    _ ≤ 1 := hwK
  have hyh : Real.exp z = y/h := Real.exp_log (div_pos hy hh0)
  have hneg : Real.exp (-z) = h/y := by rw [Real.exp_neg, hyh, inv_div]
  refine ⟨(div_le_iff₀ hy).mp (hneg ▸ Real.exp_le_exp.mpr (by linarith [(abs_le.mp hz₁).1])),
    (div_le_iff₀ hh0).mp (hyh ▸ Real.exp_le_exp.mpr (abs_le.mp hz₁).2), ?_⟩
  obtain ⟨v,hv,htaylor⟩ := exp_quadratic hz₁
  let u := cubicCoeff w d v
  have hr : y/h = ratioModel w u := by
    rw [← hyh, htaylor, hz]; unfold ratioModel u cubicCoeff; ring
  have hid : (2*h-(2*y+inverseCoeffOne/y+inverseCoeffThree/y^3))*y^5 = inverseRemainder w u := calc
    _ = ((y/h)^2*(2*(y/h)^3-2*(y/h)^4-inverseCoeffOne*w*(y/h)^2-inverseCoeffThree*w^2))/w^3 := by
      dsimp [w]; field_simp; ring
    _ = _ := by rw [hr,remainder_identity]; field_simp
  have he := hE (w,d,v) ⟨⟨hw.le,hw₁⟩, abs_le.mp hd, abs_le.mp hv⟩
  unfold InversePhaseApprox
  rw [le_div_iff₀ (pow_pos hy _), ← abs_of_pos (pow_pos hy 5), ← abs_mul, hid]
  exact (show |inverseRemainder w u| ≤ E from he).trans (le_max_left ..)

end Arxiv.«2607.05739»
