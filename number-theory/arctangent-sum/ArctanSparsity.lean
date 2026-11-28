module

public import ArctanLabelGeometry
public import ArctanEventLabels
public import ArctanInverse
public import ArctanRate
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Counting integer values of the arctangent sum

Write aₙ = ∑ arctan(1/k). If xₙ is an integer, aₙ is within n⁻¹⁰ of a
multiple jπ/2. Distinct integer events have distinct labels j, and j = O(log n).

At an event put u(j) = 2n+1. Inverting the expansion of aₙ gives
u(j) = 2y − 5/(12y) + 13/(192y³) + O(y⁻⁵), where y = c exp(jπ/2).
For four labels j, j+d, j+e, j+d+e, form the integer
u(j) u(j+d+e) − u(j+d) u(j+e). The leading y² terms cancel. For fixed
d and e the constant term is the same at every start, and the next term
is a positive multiple of y⁻². On a sufficiently late block [J, 2J),
two such determinants at distinct starts would have distance strictly
between 0 and 1. Since both are integers, each pair of positive gaps d, e
can occur at most once in this pattern.

To count the labels S in the block, fix d and put S_d = {j ∈ S : j+d ∈ S}.
Every positive difference in S_d occurs at most once, so choose(|S_d|, 2) ≤ J.
All pairs of labels in S are counted once by their gap d. Consequently
choose(|S|, 2) = ∑_d |S_d| = O(J^(3/2)) and |S| = O(J^(3/4)).
Summing over dyadic blocks up to O(log N) gives the stated bound.
-/

public section

open Filter Asymptotics
open scoped Classical

namespace Arxiv.«2607.05739»

/-- Apply the inverse expansion at y = exp(−C) exp(jπ/2), using 2n+1 as its integer witness. -/
private theorem event_model {E : Set ℕ} {label : ℕ → ℕ}
    (herror : ∀ n ∈ E, |reciprocalAngle n - (label n : ℝ)*(Real.pi/2)| < 1/(n : ℝ)^10) :
    ∃ c t H : ℝ, 0 < c ∧ 2 ≤ t ∧ 0 ≤ H ∧
      ∀ᶠ n : ℕ in atTop, n ∈ E → label n ∈ modelLabels c t H := by
  obtain ⟨C, K, hK, hphase⟩ := reciprocalAngle_expansion
  obtain ⟨E₀, he, H₀, _, hinv⟩ := inverse_phase_estimate (K + 64) (by positivity)
  refine ⟨Real.exp (-C), Real.exp (Real.pi/2), E₀, Real.exp_pos _, ?_, he, ?_⟩
  · linarith [Real.add_one_le_exp (Real.pi/2), Real.pi_gt_three]
  filter_upwards [hphase, tendsto_natCast_atTop_atTop.eventually_ge_atTop (max 1 H₀)]
    with n hph hnScale
  intro hn
  have hnR : 1 ≤ (n : ℝ) := (le_max_left _ _).trans hnScale
  let h := (n : ℝ) + 1/2
  let y := Real.exp (-C) * Real.exp (Real.pi/2)^label n
  have hy : 0 < y := by dsimp [y]; positivity
  have hh : 0 < h := by dsimp [h]; linarith
  have hh₂ : h ≤ 2*(n : ℝ) := by dsimp [h]; linarith
  have hscale : H₀ ≤ h := by dsimp [h]; linarith [(le_max_right 1 H₀).trans hnScale]
  have hlog : Real.log (y/h) = -C + (label n : ℝ)*(Real.pi/2) - Real.log h := by
    rw [Real.log_div hy.ne' hh.ne']
    simp [y, ← Real.exp_nat_mul, ← Real.exp_add]
  have hsmall : 1/(n : ℝ)^10 ≤ 64/h^6 := by
    apply (div_le_div_iff₀ (by positivity) (pow_pos hh 6)).mpr
    have hpow := pow_le_pow_left₀ hh.le hh₂ 6
    have hpow' := pow_le_pow_right₀ hnR (by decide : 6 ≤ 10)
    calc
      _ ≤ (2*(n : ℝ))^6 := by simpa using hpow
      _ = 64*(n : ℝ)^6 := by ring
      _ ≤ _ := by linarith
  have hevent := (herror n hn).le.trans hsmall
  change |reciprocalAngle n - (Real.log h + C + (5/24)/h^2 - (19/192)/h^4)| ≤ K/h^6 at hph
  have hclose : |Real.log (y/h) - (5/24)/h^2 + (19/192)/h^4| ≤ (K+64)/h^6 := by
    rw [hlog, add_div]
    rw [abs_le] at hevent hph ⊢
    constructor <;> linarith [hevent.1, hevent.2, hph.1, hph.2]
  obtain ⟨_, _, happrox⟩ := hinv hscale hy hclose
  refine ⟨2 * (n : ℤ) + 1, ?_⟩
  convert happrox using 1
  push_cast
  dsimp [h]
  ring

/-- Uniform determinant separation on large dyadic blocks, transferred back
from labels to the indices they represent. -/
theorem fourth_bound_of_event_labels {E : Set ℕ} {label : ℕ → ℕ}
    (herror : ∀ n ∈ E, |reciprocalAngle n - (label n : ℝ)*(Real.pi/2)| < 1/(n : ℝ)^10)
    (hinj : Set.InjOn label E) (hlog : ∀ n ∈ E, (label n : ℝ) ≤ 2*(1+Real.log n)) :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N → ((labelPrefix E N).card : ℝ)^4 ≤ C*(1+Real.log N)^3 := by
  obtain ⟨c,t,H,hc,ht,hH,hevent⟩ := event_model herror
  obtain ⟨N₀, hmem⟩ := eventually_atTop.mp hevent
  obtain ⟨J₀, hJ⟩ := modelLabels_dyadic hc ht hH
  obtain ⟨K, hK⟩ := labelPrefix_card_fourth_of_dyads (S := modelLabels c t H) (C := 208) (J₀ := J₀) hJ
  exact event_count_fourth_of_labels (N₀ := N₀) hK (hinj.mono Set.inter_subset_left)
    (fun n hn hN => hmem n hN hn)
    (by norm_num : (0 : ℝ) ≤ 2) (fun n hn _ => hlog n hn)

/-- A fourth-power bound on the number of integer events with 5 ≤ n < N. -/
theorem integer_event_count_fourth :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      ((labelPrefix integerEvents N).card : ℝ)^4 ≤ C*(1+Real.log N)^3 :=
  fourth_bound_of_event_labels (label := poleLabel)
    (fun _ hn => event_label_error hn) event_labels_injective (fun _ hn => event_label_le hn)

/-- The inclusive count of indices in the range of the conjecture. -/
@[expose] noncomputable def integerCount (N : ℕ) : ℕ :=
  ((Finset.Icc 5 N).filter IsIntegerValue).card

theorem integerCount_eq_prefix (N : ℕ) :
    integerCount N = (labelPrefix integerEvents (N+1)).card := by
  unfold integerCount labelPrefix
  congr 1
  ext i
  rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
  change (5 ≤ i ∧ i ≤ N) ∧ IsIntegerValue i ↔ i < N+1 ∧ 5 ≤ i ∧ IsIntegerValue i
  rw [Nat.lt_succ_iff]
  tauto

/-- The number of integer events with 5 ≤ n ≤ N is O((log N)^(3/4)). -/
theorem integer_event_count_isBigO :
    (fun N : ℕ => (integerCount N : ℝ)) =O[atTop]
      (fun N : ℕ => (Real.log N)^(3/4 : ℝ)) := by
  simpa only [integerCount_eq_prefix] using
    event_count_isBigO_log_three_quarters integer_event_count_fourth

end Arxiv.«2607.05739»
