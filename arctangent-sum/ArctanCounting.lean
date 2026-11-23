module

public import ArctanLabelDensity
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Asymptotics.Lemmas

public section

open Finset
open scoped Classical

namespace Arxiv.«2607.05739»

@[expose] noncomputable def labelPrefix (S : Set ℕ) (M : ℕ) :=
  (range M).filter fun j => j ∈ S

@[expose] noncomputable def labelDyad (S : Set ℕ) (J : ℕ) :=
  (Ico J (2*J)).filter fun j => j ∈ S

/-- The finite difference bound applied to labels in [J,2J). -/
theorem labelDyad_card_fourth {S : Set ℕ} {J : ℕ}
    (h : ∀ d e : ℕ, 0 < d → 0 < e →
      (labelPairs (labelPairs (labelDyad S J) d) e).card ≤ 1) :
    (labelDyad S J).card ^ 4 ≤ 208*(J+1)^3 := by
  have hsub : labelDyad S J ⊆ range (2*J) :=
    fun _ hj => mem_range.mpr (mem_Ico.mp (mem_filter.mp hj).1).2
  have hJ : 2*J+1 ≤ 2*(J+1) := by omega
  calc
    _ ≤ 26*(2*J+1)^3 := card_fourth_le_of_unique_parallelograms hsub h
    _ ≤ 26*(2*(J+1))^3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hJ _)
    _ = _ := by ring

/-- The coefficient 6 is less than eight, allowing absorption as the interval doubles. -/
private theorem fourth_sum_bound (x y : ℕ) : (x+y)^4 ≤ 6*x^4 + 81*y^4 := by
  by_cases h : 2*y ≤ x
  · have := Nat.pow_le_pow_left (by omega : 2*(x+y) ≤ 3*x) 4
    simp only [mul_pow] at this
    norm_num1 at this
    omega
  · have := Nat.pow_le_pow_left (by omega : x+y ≤ 3*y) 4
    simp only [mul_pow] at this
    norm_num1 at this
    omega

private theorem prefix_double (S : Set ℕ) (J : ℕ) :
    (labelPrefix S (2*J)).card ≤ (labelPrefix S J).card + (labelDyad S J).card := by
  apply (card_le_card ?_).trans (card_union_le _ _)
  intro a ha
  obtain ⟨hlt,hs⟩ := mem_filter.mp ha
  by_cases h : a < J
  · exact mem_union_left _ (mem_filter.mpr ⟨mem_range.mpr h, hs⟩)
  · exact mem_union_right _ (mem_filter.mpr ⟨mem_Ico.mpr ⟨by omega,mem_range.mp hlt⟩,hs⟩)

/-- An eventual quartic bound on dyadic intervals gives a quartic bound on every prefix. -/
theorem labelPrefix_card_fourth_of_dyads {S : Set ℕ} {C J₀ : ℕ}
    (h : ∀ J ≥ J₀, (labelDyad S J).card ^ 4 ≤ C*(J+1)^3) :
    ∃ K : ℕ, ∀ M : ℕ, (labelPrefix S M).card ^ 4 ≤ K*(M+1)^3 := by
  -- The induction step needs 6K + 648C ≤ 8K when the interval doubles.
  let K := 2*J₀ + 324*C + 1
  have trivial_bound (M : ℕ) : (labelPrefix S M).card ≤ M := by
    simpa [labelPrefix] using card_filter_le (range M) (fun j => j ∈ S)
  have hprefix (i : ℕ) : (labelPrefix S (2^i)).card ^ 4 ≤ K*(2^i)^3 := by
    induction i with
    | zero => simpa [K] using (Nat.pow_le_pow_left (trivial_bound 1) 4).trans (by simp)
    | succ i ih =>
      let J := 2^i
      rw [show 2^(i+1) = 2*J from pow_succ' _ _]
      by_cases hJ : J < J₀
      · -- Before the threshold, counting all indices suffices.
        calc
          _ ≤ (2*J)^4 := Nat.pow_le_pow_left (trivial_bound _) _
          _ = (2*J)*(2*J)^3 := by ring
          _ ≤ _ := Nat.mul_le_mul_right _ (by dsimp [K]; omega)
      · -- The prefix doubles by adding one block to the previous prefix.
        have hpos : 0 < J := by dsimp [J]; positivity
        have hblock := (h J (by omega)).trans
          (Nat.mul_le_mul_left C (Nat.pow_le_pow_left (by omega : J+1 ≤ 2*J) 3))
        calc
          _ ≤ ((labelPrefix S J).card + (labelDyad S J).card)^4 :=
            Nat.pow_le_pow_left (prefix_double S J) _
          _ ≤ _ := fourth_sum_bound _ _
          _ ≤ 6*(K*J^3) + 81*(C*(2*J)^3) :=
            Nat.add_le_add (Nat.mul_le_mul_left _ ih) (Nat.mul_le_mul_left _ hblock)
          _ = (6*K+648*C)*J^3 := by ring
          _ ≤ (8*K)*J^3 := Nat.mul_le_mul_right _ (by dsimp [K]; omega)
          _ = _ := by ring
  refine ⟨8*K, fun M => ?_⟩
  by_cases hm : M = 0
  · simp [hm,labelPrefix]
  have hm₀ := Nat.log2_self_le hm
  have hsub : labelPrefix S M ⊆ labelPrefix S (2^(M.log2+1)) :=
    filter_subset_filter _ (range_mono (Nat.lt_log2_self.le))
  calc
    _ ≤ _ := Nat.pow_le_pow_left (card_le_card hsub) 4
    _ ≤ _ := hprefix (M.log2+1)
    _ = (8*K)*(2^M.log2)^3 := by rw [pow_succ]; ring
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)

/-- Transfer a label count to events with eventually injective, logarithmically
bounded labels. All analytic information about the events is given explicitly. -/
theorem event_count_fourth_of_labels {E S : Set ℕ} {label : ℕ → ℕ} {N₀ K : ℕ} {A : ℝ}
    (hK : ∀ M, (labelPrefix S M).card ^ 4 ≤ K*(M+1)^3)
    (hinj : Set.InjOn label (E ∩ Set.Ici N₀))
    (hmem : ∀ n ∈ E, N₀ ≤ n → label n ∈ S)
    (hA : 0 ≤ A) (hgrowth : ∀ n ∈ E, N₀ ≤ n → (label n : ℝ) ≤ A*(1+Real.log n)) :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      ((labelPrefix E N).card : ℝ)^4 ≤ C*(1+Real.log N)^3 := by
  refine ⟨6*(N₀:ℝ)^4 + 81*(K:ℝ)*(A+2)^3, fun N hN => ?_⟩
  let X := 1 + Real.log N
  have hX : 1 ≤ X := by dsimp [X]; linarith [Real.log_natCast_nonneg N]
  let b := ⌊A*X⌋₊
  let late := (labelPrefix E N).filter (fun n => N₀ ≤ n)
  have hcnt : (labelPrefix E N).card ≤ N₀ + late.card := by
    have hsub : labelPrefix E N ⊆ range N₀ ∪ late := by
      intro a ha
      by_cases h : a < N₀
      · exact mem_union_left _ (mem_range.mpr h)
      · exact mem_union_right _ (mem_filter.mpr ⟨ha, by omega⟩)
    simpa using (card_le_card hsub).trans (card_union_le _ _)
  have hlate : late.card ≤ (labelPrefix S (b+1)).card := by
    apply card_le_card_of_injOn label
    · intro n hnl
      obtain ⟨hn, hn₀⟩ := mem_filter.mp hnl
      obtain ⟨hlt, hE⟩ := mem_filter.mp hn
      have hltN := mem_range.mp hlt
      have hlog : Real.log n ≤ Real.log N := by
        by_cases hnz : n = 0
        · simpa [hnz] using Real.log_natCast_nonneg N
        · exact Real.log_le_log (by positivity : 0 < (n:ℝ)) (by exact_mod_cast hltN.le)
      have hb : label n ≤ b := Nat.le_floor ((hgrowth n hE hn₀).trans
        (mul_le_mul_of_nonneg_left (by dsimp [X]; linarith) hA))
      exact mem_filter.mpr ⟨mem_range.mpr (by omega), hmem n hE hn₀⟩
    · apply hinj.mono
      intro n hn
      exact ⟨(mem_filter.mp (mem_filter.mp hn).1).2, (mem_filter.mp hn).2⟩
  have htotal : (labelPrefix E N).card^4 ≤ 6*N₀^4 + 81*(K*((b+1)+1)^3) := calc
    _ ≤ (N₀+(labelPrefix S (b+1)).card)^4 := Nat.pow_le_pow_left
      (hcnt.trans (Nat.add_le_add_left hlate _)) _
    _ ≤ _ := fourth_sum_bound _ _
    _ ≤ _ := Nat.add_le_add_left (Nat.mul_le_mul_left _ (hK (b+1))) _
  have hreal : ((labelPrefix E N).card : ℝ)^4 ≤ 6*(N₀:ℝ)^4 + 81*((K:ℝ)*((b:ℝ)+2)^3) := by
    have he := (Nat.cast_le (α := ℝ)).mpr htotal
    push_cast at he
    convert he using 1; ring
  have hb : (b:ℝ)+2 ≤ (A+2)*X := by
    have := Nat.floor_le (mul_nonneg hA (by linarith : 0 ≤ X))
    change (b : ℝ) ≤ A*X at this
    linarith
  have hb3 := pow_le_pow_left₀ (by positivity : 0 ≤ (b:ℝ)+2) hb 3
  have hX3 : 1 ≤ X^3 := one_le_pow₀ hX
  calc
    _ ≤ _ := hreal
    _ ≤ 6*(N₀:ℝ)^4*X^3 + 81*((K:ℝ)*((A+2)*X)^3) := by
      apply add_le_add
      · simpa using mul_le_mul_of_nonneg_left hX3 (by positivity : 0 ≤ 6*(N₀:ℝ)^4)
      · gcongr
    _ = _ := by dsimp [X]; ring

open Filter Asymptotics in
/-- The logarithmic cubic upper bound for the fourth power makes the event
count little-o of the logarithm. -/
theorem event_count_isLittleO_log_of_fourth {E : Set ℕ}
    (h : ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      ((labelPrefix E N).card : ℝ)^4 ≤ C*(1+Real.log N)^3) :
    (fun N : ℕ => ((labelPrefix E N).card : ℝ)) =o[atTop] (fun N : ℕ => Real.log N) := by
  obtain ⟨C, hC⟩ := h
  let D := max C 1
  have hD : 0 ≤ D := (by dsimp [D]; positivity)
  rw [isLittleO_iff]
  intro ε hε
  have he : 0 < ε^4 := by positivity
  have ht : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually_ge_atTop (max 1 (8*D/ε^4)), eventually_ge_atTop (1:ℕ)] with N hN hpos
  let x := Real.log N
  have hx : 1 ≤ x := (le_max_left _ _).trans hN
  have hDx : 8*D ≤ ε^4*x := by
    rw [mul_comm (ε^4), ← div_le_iff₀ he]
    exact (le_max_right _ _).trans hN
  have hx0 : 0 ≤ x := by linarith
  simp only [Real.norm_eq_abs, Nat.abs_cast, abs_of_nonneg (Real.log_natCast_nonneg N)]
  apply (pow_le_pow_iff_left₀ (Nat.cast_nonneg _) (mul_nonneg hε.le hx0) (by decide : 4 ≠ 0)).mp
  calc
    _ ≤ C*(1+x)^3 := hC N hpos
    _ ≤ D*(2*x)^3 := mul_le_mul (le_max_left _ _) (pow_le_pow_left₀ (by positivity) (by linarith) _) (by positivity) hD
    _ = (8*D)*x^3 := by ring
    _ ≤ (ε^4*x)*x^3 := mul_le_mul_of_nonneg_right hDx (by positivity)
    _ = _ := by ring

end Arxiv.«2607.05739»
