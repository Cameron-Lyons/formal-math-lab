module

public import PaletteMinima
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Nat.Log
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp

/-! A transfer from intervals to odd cycles and a tensor-power bound imply
the existence of the logarithmic growth exponent. The abstract limit theorem is then applied
to the minima of the actual interval and cyclic palettes. -/
public section

namespace Erdos160
open Filter Topology
open scoped Topology

/-- The available exponents from odd cyclic bases of size at least three. -/
def cyclicRatios (H : ℕ → ℕ) : Set ℝ :=
  {r | ∃ m : ℕ, 3 ≤ m ∧ m % 2 = 1 ∧ r = Real.log (H m) / Real.log m}

noncomputable def growthExponent (H : ℕ → ℕ) : ℝ := sInf (cyclicRatios H)

private theorem ratios_nonempty (H : ℕ → ℕ) : (cyclicRatios H).Nonempty :=
  ⟨_, 3, by decide, by decide, rfl⟩

private theorem ratio_nonneg {H : ℕ → ℕ} {r : ℝ} (hr : r ∈ cyclicRatios H) : 0 ≤ r := by
  obtain ⟨m, _, _, rfl⟩ := hr
  exact div_nonneg (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _)

theorem growthExponent_nonneg (H : ℕ → ℕ) : 0 ≤ growthExponent H :=
  le_csInf (ratios_nonempty H) fun _ hr => ratio_nonneg hr

theorem growthExponent_le_base (H : ℕ → ℕ) {m : ℕ} (hm : 3≤m) (odd : m%2=1) :
    growthExponent H ≤ Real.log (H m) / Real.log m :=
  csInf_le (show BddBelow (cyclicRatios H) from ⟨0, fun _ hr => ratio_nonneg hr⟩)
    ⟨m, hm, odd, rfl⟩

/-- Existence of the common exponent from the finite transfer and power bounds. -/
theorem tendsto_growthExponent (h H : ℕ → ℕ) (mono : Monotone h)
    (pos : ∀ N, 0 < N → 0 < h N)
    (transfer : ∀ m, 3 ≤ m → m % 2 = 1 → H m ≤ 12 * h m)
    (powers : ∀ m, 3 ≤ m → m % 2 = 1 → ∀ t N, N ≤ m^t → h N ≤ (H m)^t) :
    Tendsto (fun N : ℕ => Real.log (h N) / Real.log N) atTop (𝓝 (growthExponent H)) := by
  let α := growthExponent H
  have A0 : 0 ≤ α := growthExponent_nonneg H
  have Hpos (m : ℕ) (hm : 3≤m) (odd : m%2=1) : 0 < H m := by
    have p := powers m hm odd 1 1 (by simpa using (show 1≤m by omega))
    simpa using lt_of_lt_of_le (pos 1 (by decide)) p
  have logAtTop : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have lower (N : ℕ) (hN : 3 ≤ N) :
      α - (α*Real.log 2 + Real.log 12) / Real.log N ≤ Real.log (h N) / Real.log N := by
    let m := 2*((N-1)/2)+1
    have hm : 3≤m := by dsimp [m]; omega
    have odd : m%2=1 := by dsimp [m]; omega
    have sm : m ≤ N := by dsimp [m]; omega
    have dbl : N ≤ 2*m := by dsimp [m]; omega
    have mpos : (0:ℝ) < m := by exact_mod_cast (show 0<m by omega)
    have hNm : (0:ℝ) < N := by exact_mod_cast (show 0<N by omega)
    have ml : 0 < Real.log m := Real.log_pos (by exact_mod_cast (show 1<m by omega))
    have nl : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1<N by omega))
    have alpha_m : α * Real.log m ≤ Real.log (H m) :=
      (le_div_iff₀ ml).mp (growthExponent_le_base H hm odd)
    have m_large : Real.log N ≤ Real.log 2 + Real.log m := by
      rw [← Real.log_mul (by norm_num) mpos.ne']
      exact Real.log_le_log hNm (by exact_mod_cast dbl)
    have h_small : Real.log (H m) ≤ Real.log 12 + Real.log (h N) := by
      have hp := pos N (by omega)
      rw [← Real.log_mul (by norm_num) (by exact_mod_cast (Nat.ne_of_gt hp))]
      apply Real.log_le_log (by exact_mod_cast Hpos m hm odd)
      exact_mod_cast (transfer m hm odd).trans (Nat.mul_le_mul_left 12 (mono sm))
    apply (le_div_iff₀ nl).2
    rw [sub_mul, div_mul_cancel₀ _ nl.ne']
    have scale := mul_le_mul_of_nonneg_left m_large A0
    linarith
  have upper (m : ℕ) (hm : 3≤m) (odd : m%2=1) (N : ℕ) (hN : 2≤N) :
      Real.log (h N) / Real.log N ≤ Real.log (H m) / Real.log m + Real.log (H m) / Real.log N := by
    let l := Nat.log m N
    have ml : 0 < Real.log m := Real.log_pos (by exact_mod_cast (show 1<m by omega))
    have nl : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1<N by omega))
    have lp : (l:ℝ) * Real.log m ≤ Real.log N := by
      rw [← Real.log_pow]
      apply Real.log_le_log (pow_pos (by exact_mod_cast (show 0<m by omega)) _)
      exact_mod_cast Nat.pow_log_le_self m (show N≠0 by omega)
    have p : h N ≤ (H m)^(l+1) := powers m hm odd _ N
      (Nat.le_of_lt (Nat.lt_pow_succ_log_self (by omega : 1<m) N))
    have hp : Real.log (h N) ≤ ((l:ℝ)+1) * Real.log (H m) := by
      have hp' := Real.log_le_log (show (0:ℝ)<h N by exact_mod_cast (pos N (by omega)))
        (show (h N:ℝ) ≤ (H m:ℝ)^(l+1) by exact_mod_cast p)
      simpa [Real.log_pow] using hp'
    let r := Real.log (H m) / Real.log m
    have rp : 0≤r := div_nonneg (Real.log_natCast_nonneg _) ml.le
    have eq : r*Real.log m = Real.log (H m) := div_mul_cancel₀ _ ml.ne'
    have sc : (l:ℝ)*Real.log (H m) ≤ r*Real.log N := by
      calc
        _ = r * ((l:ℝ)*Real.log m) := by rw [← eq]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left lp rp
    apply (div_le_iff₀ nl).2
    change Real.log (h N) ≤ (r + _) * Real.log N
    rw [add_mul, div_mul_cancel₀ _ nl.ne']
    linarith
  apply tendsto_order.mpr
  constructor
  · intro a ha
    have conv : Tendsto (fun N : ℕ => α - (α*Real.log 2+Real.log 12)/Real.log N) atTop (𝓝 α) := by
      simpa using tendsto_const_nhds.sub (logAtTop.const_div_atTop (α*Real.log 2+Real.log 12))
    filter_upwards [(tendsto_order.mp conv).1 a ha, eventually_ge_atTop 3] with N hlow hN
    exact lt_of_lt_of_le hlow (lower N hN)
  · intro b hb
    obtain ⟨r, hr, rb⟩ := exists_lt_of_csInf_lt (ratios_nonempty H) hb
    obtain ⟨m, hm, odd, rfl⟩ := hr
    let r := Real.log (H m) / Real.log m
    have conv : Tendsto (fun N : ℕ => r+Real.log (H m)/Real.log N) atTop (𝓝 r) := by
      simpa using tendsto_const_nhds.add (logAtTop.const_div_atTop (Real.log (H m)))
    filter_upwards [(tendsto_order.mp conv).2 b rb, eventually_ge_atTop 2] with N hup hN
    exact lt_of_le_of_lt (upper m hm odd N hN) hup

end Erdos160
#print axioms Erdos160.tendsto_growthExponent

namespace Erdos160
open Filter Topology

/-- The interval minimum has a logarithmic growth exponent. It is exactly the
infimum of the ratios of log palette size to log modulus over odd cyclic bases. -/
theorem intervalPaletteMinimum_growth :
    Tendsto (fun N : ℕ => Real.log (intervalPaletteMinimum N) / Real.log N)
      atTop (𝓝 (growthExponent cyclicPaletteMinimum)) :=
  tendsto_growthExponent intervalPaletteMinimum cyclicPaletteMinimum
    intervalPaletteMinimum_mono intervalPaletteMinimum_pos
    (fun _ _ odd => cyclicPaletteMinimum_le_twelve odd)
    (fun _ _ odd => intervalPaletteMinimum_le_power odd)

end Erdos160
#print axioms Erdos160.intervalPaletteMinimum_growth

namespace Erdos160

/-- The limiting power is a lower bound at each odd cyclic base. -/
theorem growthPower_le_cyclic {m : ℕ} (size : 3 ≤ m) (odd : m % 2 = 1) :
    (m : ℝ) ^ growthExponent cyclicPaletteMinimum ≤ cyclicPaletteMinimum m := by
  have lm : 0 < Real.log m := Real.log_pos (by exact_mod_cast (show 1 < m by omega))
  have hm : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hc : (0 : ℝ) < cyclicPaletteMinimum m := by exact_mod_cast cyclicPaletteMinimum_pos odd
  apply (Real.log_le_log_iff (Real.rpow_pos_of_pos hm _) hc).mp
  rw [Real.log_rpow hm]
  exact (le_div_iff₀ lm).mp (growthExponent_le_base cyclicPaletteMinimum size odd)

/-- A lower bound for every interval length at least two, with explicit constant. -/
theorem intervalPaletteMinimum_lower {N : ℕ} (size : 2 ≤ N) :
    ((N : ℝ) - 1) ^ growthExponent cyclicPaletteMinimum / 12 ≤ intervalPaletteMinimum N := by
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 12)).mpr
  by_cases hN : 3 ≤ N
  · let m := 2*((N-1)/2)+1
    have hm : 3 ≤ m := by dsimp [m]; omega
    have odd : m%2=1 := by dsimp [m]; omega
    have leN : m ≤ N := by dsimp [m]; omega
    have near : N ≤ m+1 := by dsimp [m]; omega
    have L : (N:ℝ) - 1 ≤ m := by
      have : (N : ℝ) ≤ (m : ℝ) + 1 := by exact_mod_cast near
      linarith
    have nn : 0 ≤ (N:ℝ) - 1 := by
      have : (2:ℝ) ≤ N := by exact_mod_cast size
      linarith
    calc
      _ ≤ (m:ℝ) ^ growthExponent cyclicPaletteMinimum :=
        Real.rpow_le_rpow nn L (growthExponent_nonneg _)
      _ ≤ cyclicPaletteMinimum m := growthPower_le_cyclic hm odd
      _ ≤ _ := by
        have bound := (cyclicPaletteMinimum_le_twelve odd).trans
          (Nat.mul_le_mul_left 12 (intervalPaletteMinimum_mono leN))
        rw [mul_comm]
        exact_mod_cast bound
  · obtain rfl : N = 2 := by omega
    have hp : (1:ℝ) ≤ intervalPaletteMinimum 2 := by
      exact_mod_cast intervalPaletteMinimum_pos 2 (by decide)
    norm_num
    linarith

end Erdos160
#print axioms Erdos160.intervalPaletteMinimum_lower
