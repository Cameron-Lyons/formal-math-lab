module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Data.Nat.Choose.Sum
public import UCBound.Basic
public import UCBound.Entropy
public import UCBound.Protocols

@[expose] public section

/-!
# Peeling, Beta-Density Subset Averaging, 3-Vertex Triangle Lemma, and Master Reduction

Formalizes our 3-Vertex Single-Order Master Proof:
1. Peeling into `(G, ordT)` with `e_i ≥ z` on `G` and `e_i < z` on `T`.
2. Subset-averaged entropy `gH(t)`, `deltaH(t)`, `CH(t) = deltaH(t) - t * deltaH'(t)`,
   and exact Beta-density integration by parts:
   `κ E[CH(Θ)] - D E[deltaH(Θ)] = W deltaH(a0)`.
3. Uniform permutation coupling over `π : Equiv.Perm (Fin d)` with `Bin(d, 1 - Θ)`,
   exact sums `∑ w_j = η d`, `∑ ω_j = 0`, and the **3-Vertex Triangle Lemma**:
   `w_j ≤ 1`, `ω_j ≤ a0`, `w_j + ω_j ≥ a0`.
4. `ValidPoint` extraction from the 1D and 2D local inequalities.
5. `master_contradiction`: reduces `frankl_union_closed_bound` cleanly to the local
   1D/2D inequalities and the 2D polytope positivity bounds at the 3 `G`-vertices and on `T`.
-/

noncomputable section

namespace UCBound

open scoped BigOperators
open Finset

/-! ### Master Proof Parameters (Exact Rationals + Derived Constants) -/

def epsParam : ℝ := 365 / 1000000
def zParam : ℝ := 21 / 50
def a0Param : ℝ := 3 / 8
def kappaParam : ℝ := 39 / 100
def CcovParam : ℝ := 13 / 25
def CtotParam : ℝ := 1 + CcovParam
def muUParam : ℝ := 33 / 10
def mugParam : ℝ := 27
def nu1Param : ℝ := 1933 / 10000
def nu2Param : ℝ := -(3 / 125)

def betaParam : ℝ := 1 - DParam / kappaParam
def b0Param : ℝ := a0Param ^ betaParam
def WParam : ℝ := (kappaParam - DParam) / (1 - b0Param)
def etaParam : ℝ := ((kappaParam - DParam) / DParam) * (b0Param - a0Param) / (1 - b0Param)

lemma a0Param_pos : 0 < a0Param := by unfold a0Param; norm_num
lemma a0Param_lt_one : a0Param < 1 := by unfold a0Param; norm_num
lemma kappaParam_pos : 0 < kappaParam := by unfold kappaParam; norm_num
lemma muUParam_nonneg : 0 ≤ muUParam := by unfold muUParam; norm_num
lemma mugParam_nonneg : 0 ≤ mugParam := by unfold mugParam; norm_num

lemma betaParam_pos {hD : DParam < kappaParam} : 0 < betaParam := by
  unfold betaParam
  have : DParam / kappaParam < 1 := (div_lt_one kappaParam_pos).mpr hD
  linarith

lemma betaParam_lt_one {hD0 : 0 < DParam} : betaParam < 1 := by
  unfold betaParam
  have : 0 < DParam / kappaParam := div_pos hD0 kappaParam_pos
  linarith

lemma b0Param_pos : 0 < b0Param := Real.rpow_pos_of_pos a0Param_pos _

lemma b0Param_lt_one {hD : DParam < kappaParam} : b0Param < 1 :=
  Real.rpow_lt_one (le_of_lt a0Param_pos) a0Param_lt_one (betaParam_pos (hD := hD))

/-! ### Peeling Algorithm -/

/-- Peeling induction on a subset `B ⊆ Fin n`:
    repeatedly removes `i ∈ B` with `H(A_i | A_{B \ {i}}) < z`, returning `(G, ordT)`
    with `G ∪ ordT.toFinset = B`, `e_i ≥ z` on `G`, and `e_k < z` along `ordT`. -/
lemma peel_subset {n : ℕ} (Ω : Finset (Fin n → Bool)) (z : ℝ) :
    ∀ (k : ℕ) (B : Finset (Fin n)), B.card = k →
      ∃ (G : Finset (Fin n)) (ordT : List (Fin n)),
        ordT.Nodup ∧ (∀ i ∈ ordT, i ∉ G) ∧ G ∪ ordT.toFinset = B ∧
        (∀ i ∈ G, z ≤ coordCondEnt Ω (unifW Ω) id i (G.erase i)) ∧
        (∀ j : Fin ordT.length,
          coordCondEnt Ω (unifW Ω) id (ordT[j]) (G ∪ (ordT.take j).toFinset) < z) := by
  intro k
  induction k with
  | zero =>
    intro B hcard
    have hB : B = ∅ := Finset.card_eq_zero.mp hcard
    subst hB
    exact ⟨∅, [], List.nodup_nil, by simp, by simp, by simp, fun j => Fin.elim0 j⟩
  | succ k ih =>
    intro B hcard
    by_cases hall : ∀ i ∈ B, z ≤ coordCondEnt Ω (unifW Ω) id i (B.erase i)
    · exact ⟨B, [], List.nodup_nil, by simp, by simp, hall, fun j => Fin.elim0 j⟩
    · push Not at hall
      rcases hall with ⟨i0, hi0B, hi0lt⟩
      have hcard' : (B.erase i0).card = k := by
        rw [Finset.card_erase_of_mem hi0B, hcard]; simp
      rcases ih (B.erase i0) hcard' with ⟨G, ordT', hnd', hdisj', hcov', hG', hT'⟩
      have hi0_not_G : i0 ∉ G := by
        intro hmem
        have : i0 ∈ G ∪ ordT'.toFinset := Finset.mem_union_left _ hmem
        rw [hcov'] at this
        exact (Finset.mem_erase.mp this).1 rfl
      have hi0_not_T' : i0 ∉ ordT' := by
        intro hmem
        have : i0 ∈ G ∪ ordT'.toFinset := Finset.mem_union_right _ (List.mem_toFinset.mpr hmem)
        rw [hcov'] at this
        exact (Finset.mem_erase.mp this).1 rfl
      refine ⟨G, ordT' ++ [i0], ?_, ?_, ?_, hG', ?_⟩
      · rw [List.nodup_append]
        exact ⟨hnd', List.nodup_singleton i0, fun a ha b hb hab => by
          simp only [List.mem_singleton] at hb; subst hb; subst hab; exact hi0_not_T' ha⟩
      · intro i hi
        rcases List.mem_append.mp hi with h1 | h2
        · exact hdisj' i h1
        · simp only [List.mem_singleton] at h2; subst h2; exact hi0_not_G
      · rw [List.toFinset_append, List.toFinset_cons, List.toFinset_nil, insert_empty_eq]
        ext x
        have hx := congr_arg (fun S => x ∈ S) hcov'
        simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_erase] at hx ⊢
        by_cases hxi : x = i0
        · subst hxi; simp [hi0B]
        · simp only [hxi, or_false, ne_eq, not_false_eq_true, true_and] at hx ⊢
          exact eq_iff_iff.mp hx
      · intro j
        have hlen : (ordT' ++ [i0]).length = ordT'.length + 1 := by simp
        by_cases hj : (j : ℕ) < ordT'.length
        · have hget : (ordT' ++ [i0])[j] = ordT'[j]'hj := List.getElem_append_left hj
          have htake : (ordT' ++ [i0]).take j = ordT'.take j := List.take_append_of_le_length (le_of_lt hj)
          rw [hget, htake]
          exact hT' ⟨j, hj⟩
        · have hjeq : (j : ℕ) = ordT'.length := by have := j.isLt; omega
          have hget : (ordT' ++ [i0])[j] = i0 := by
            change (ordT' ++ [i0])[j.1]'j.isLt = i0
            rw [List.getElem_append_right (le_of_eq hjeq.symm)]
            simp [hjeq]
          have htake : (ordT' ++ [i0]).take j = ordT' := by
            rw [hjeq, List.take_left]
          rw [hget, htake, hcov']
          exact hi0lt

lemma peel_coords {n : ℕ} (Ω : Finset (Fin n → Bool)) (z : ℝ) :
    ∃ (G : Finset (Fin n)) (ordT : List (Fin n)),
      ordT.Nodup ∧ (∀ i ∈ ordT, i ∉ G) ∧ G ∪ ordT.toFinset = Finset.univ ∧
      (∀ i ∈ G, z ≤ coordCondEnt Ω (unifW Ω) id i (G.erase i)) ∧
      (∀ j : Fin ordT.length,
        coordCondEnt Ω (unifW Ω) id (ordT[j]) (G ∪ (ordT.take j).toFinset) < z) :=
  peel_subset Ω z (Finset.univ : Finset (Fin n)).card Finset.univ rfl

/-! ### Subset-Averaged Entropy & Beta-Density Integration by Parts -/

def subsetWeight {n : ℕ} (G : Finset (Fin n)) (t : ℝ) (S : Finset (Fin n)) : ℝ :=
  (1 - t) ^ S.card * t ^ (G.card - S.card)

def gH {n : ℕ} (Ω : Finset (Fin n → Bool)) (G : Finset (Fin n)) (t : ℝ) : ℝ :=
  ∑ S ∈ G.powerset, subsetWeight G t S * subEnt Ω (unifW Ω) id S

def deltaH {n : ℕ} (Ω : Finset (Fin n → Bool)) (G : Finset (Fin n)) (t : ℝ) : ℝ :=
  gH Ω G t - (1 - t) * subEnt Ω (unifW Ω) id G

def CH {n : ℕ} (Ω : Finset (Fin n → Bool)) (G : Finset (Fin n)) (t : ℝ) : ℝ :=
  ∑ S ∈ G.powerset, subsetWeight G t S * totalCorr Ω (unifW Ω) id G S

/-- Binomial sum of `subsetWeight` over `G.powerset` equals `1`. -/
lemma sum_subsetWeight {n : ℕ} (G : Finset (Fin n)) (t : ℝ) :
    ∑ S ∈ G.powerset, subsetWeight G t S = 1 := by
  have hpow := add_pow (1 - t) t G.card
  rw [sub_add_cancel, one_pow] at hpow
  symm; rw [hpow]
  -- Group S ∈ G.powerset by S.card ∈ range (G.card + 1)!
  rw [← Finset.sum_fiberwise_of_maps_to (g := Finset.card) (t := Finset.range (G.card + 1))
        (fun S hS => Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.card_le_card (Finset.mem_powerset.mp hS))))]
  apply Finset.sum_congr rfl
  intro k hk
  have hfilt : G.powerset.filter (fun S => S.card = k) = G.powersetCard k := by
    ext S; simp [Finset.mem_powersetCard]
  rw [hfilt]
  have hcongr : ∀ S ∈ G.powersetCard k, subsetWeight G t S = (1 - t) ^ k * t ^ (G.card - k) := by
    intro S hS; unfold subsetWeight; rw [(Finset.mem_powersetCard.mp hS).2]
  rw [Finset.sum_congr rfl hcongr, Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul]
  ring

lemma deltaH_one {n : ℕ} (Ω : Finset (Fin n → Bool)) (hΩ : Ω.Nonempty) (G : Finset (Fin n)) :
    deltaH Ω G 1 = 0 := by
  unfold deltaH gH
  simp only [sub_self, zero_mul, sub_zero]
  apply Finset.sum_eq_zero
  intro S _
  by_cases hS : S = ∅
  · subst hS
    rw [subEnt_empty Ω (unifW Ω) (sum_unifW hΩ) id, mul_zero]
  · unfold subsetWeight
    have hpos : 0 < S.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hS)
    rw [sub_self, zero_pow (Nat.ne_of_gt hpos), zero_mul, zero_mul]

/-- Exact derivative of `gH Ω G` at every `t : ℝ`. -/
lemma hasDerivAt_gH {n : ℕ} (Ω : Finset (Fin n → Bool)) (G : Finset (Fin n)) (t : ℝ) :
    HasDerivAt (gH Ω G)
      (-∑ i ∈ G, ∑ S ∈ (G.erase i).powerset,
          subsetWeight (G.erase i) t S * coordCondEnt Ω (unifW Ω) id i S) t := by
  -- Differentiate term-by-term in gH:
  have hterm_deriv : ∀ S ∈ G.powerset,
      HasDerivAt (fun u => subsetWeight G u S * subEnt Ω (unifW Ω) id S)
        ((-(S.card : ℝ) * (1 - t) ^ (S.card - 1) * t ^ (G.card - S.card)
          + ((G.card - S.card : ℕ) : ℝ) * (1 - t) ^ S.card * t ^ (G.card - S.card - 1))
          * subEnt Ω (unifW Ω) id S) t := by
    intro S _
    have h1 : HasDerivAt (fun u : ℝ => (1 - u) ^ S.card)
        ((S.card : ℝ) * (1 - t) ^ (S.card - 1) * (-1)) t := by
      have hsub : HasDerivAt (fun u : ℝ => 1 - u) (-1) t := by
        simpa using (hasDerivAt_const t (1 : ℝ)).fun_sub (hasDerivAt_id' t)
      exact (hasDerivAt_pow S.card (1 - t)).comp t hsub
    have h2 : HasDerivAt (fun u : ℝ => u ^ (G.card - S.card))
        (((G.card - S.card : ℕ) : ℝ) * t ^ (G.card - S.card - 1)) t :=
      hasDerivAt_pow (G.card - S.card) t
    have hmul := (h1.fun_mul h2).mul_const (subEnt Ω (unifW Ω) id S)
    exact hmul.congr_deriv (by ring)
  have hsum_deriv : HasDerivAt (gH Ω G)
      (∑ S ∈ G.powerset,
        ((-(S.card : ℝ) * (1 - t) ^ (S.card - 1) * t ^ (G.card - S.card)
          + ((G.card - S.card : ℕ) : ℝ) * (1 - t) ^ S.card * t ^ (G.card - S.card - 1))
          * subEnt Ω (unifW Ω) id S)) t :=
    HasDerivAt.fun_sum hterm_deriv
  apply hsum_deriv.congr_deriv
  -- Re-index both halves using |S| = ∑ i ∈ S, 1 and |G \ S| = ∑ i ∈ G \ S, 1!
  have hsplit : ∑ S ∈ G.powerset,
        ((-(S.card : ℝ) * (1 - t) ^ (S.card - 1) * t ^ (G.card - S.card)
          + ((G.card - S.card : ℕ) : ℝ) * (1 - t) ^ S.card * t ^ (G.card - S.card - 1))
          * subEnt Ω (unifW Ω) id S)
      = -(∑ S ∈ G.powerset, ∑ i ∈ S,
            (1 - t) ^ (S.card - 1) * t ^ (G.card - S.card) * subEnt Ω (unifW Ω) id S)
        + (∑ S ∈ G.powerset, ∑ i ∈ G \ S,
            (1 - t) ^ S.card * t ^ (G.card - S.card - 1) * subEnt Ω (unifW Ω) id S) := by
    have hrew : ∀ S ∈ G.powerset,
        (-(S.card : ℝ) * (1 - t) ^ (S.card - 1) * t ^ (G.card - S.card)
          + ((G.card - S.card : ℕ) : ℝ) * (1 - t) ^ S.card * t ^ (G.card - S.card - 1))
          * subEnt Ω (unifW Ω) id S
        = -(∑ _i ∈ S, (1 - t) ^ (S.card - 1) * t ^ (G.card - S.card) * subEnt Ω (unifW Ω) id S)
          + (∑ _i ∈ G \ S, (1 - t) ^ S.card * t ^ (G.card - S.card - 1) * subEnt Ω (unifW Ω) id S) := by
      intro S hS
      have hcard_sdiff : (G \ S).card = G.card - S.card := by
        rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.mem_powerset.mp hS)]
      rw [Finset.sum_const, nsmul_eq_mul, Finset.sum_const, nsmul_eq_mul, hcard_sdiff]
      ring
    rw [Finset.sum_congr rfl hrew, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  rw [hsplit]
  -- Swap sum over S and i in both sums!
  have hpart1 : ∑ S ∈ G.powerset, ∑ i ∈ S,
        (1 - t) ^ (S.card - 1) * t ^ (G.card - S.card) * subEnt Ω (unifW Ω) id S
      = ∑ i ∈ G, ∑ S' ∈ (G.erase i).powerset,
          subsetWeight (G.erase i) t S' * subEnt Ω (unifW Ω) id (insert i S') := by
    -- Write both sides as sums over pairs (i, S) with i ∈ S ⊆ G
    have hL : ∑ S ∈ G.powerset, ∑ i ∈ S,
          (1 - t) ^ (S.card - 1) * t ^ (G.card - S.card) * subEnt Ω (unifW Ω) id S
        = ∑ i ∈ G, ∑ S ∈ G.powerset.filter (fun S => i ∈ S),
            (1 - t) ^ (S.card - 1) * t ^ (G.card - S.card) * subEnt Ω (unifW Ω) id S := by
      have h1 : ∀ S ∈ G.powerset,
          ∑ i ∈ S, (1 - t) ^ (S.card - 1) * t ^ (G.card - S.card) * subEnt Ω (unifW Ω) id S
          = ∑ i ∈ G, if i ∈ S then (1 - t) ^ (S.card - 1) * t ^ (G.card - S.card) * subEnt Ω (unifW Ω) id S else 0 := by
        intro S hS
        rw [← Finset.sum_filter]
        congr 1; ext i; simp only [Finset.mem_filter]
        exact ⟨fun hi => ⟨Finset.mem_powerset.mp hS hi, hi⟩, fun h => h.2⟩
      rw [Finset.sum_congr rfl h1, Finset.sum_comm]
      apply Finset.sum_congr rfl; intro i _; rw [Finset.sum_filter]
    rw [hL]
    apply Finset.sum_congr rfl; intro i hiG
    symm
    apply Finset.sum_nbij (fun S' => insert i S')
    · intro S' hS'
      rw [Finset.mem_filter, Finset.mem_powerset]
      refine ⟨?_, Finset.mem_insert_self i S'⟩
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx'
      · exact hiG
      · exact (Finset.mem_erase.mp (Finset.mem_powerset.mp hS' hx')).2
    · intro S1 hS1 S2 hS2 heq
      have h1 : i ∉ S1 := fun h => (Finset.mem_erase.mp (Finset.mem_powerset.mp hS1 h)).1 rfl
      have h2 : i ∉ S2 := fun h => (Finset.mem_erase.mp (Finset.mem_powerset.mp hS2 h)).1 rfl
      ext x
      have hx := congr_arg (fun T => x ∈ T) heq
      simp only [Finset.mem_insert] at hx
      by_cases hxi : x = i
      · subst hxi; simp [h1, h2]
      · simpa [hxi] using hx
    · intro S hS
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset] at hS
      refine ⟨S.erase i, Finset.mem_coe.mpr (Finset.mem_powerset.mpr (Finset.erase_subset_erase i hS.1)),
        Finset.insert_erase hS.2⟩
    · intro S' hS'
      have hi_not : i ∉ S' := fun h => (Finset.mem_erase.mp (Finset.mem_powerset.mp hS' h)).1 rfl
      unfold subsetWeight
      rw [Finset.card_insert_of_notMem hi_not, Nat.add_sub_cancel,
          Finset.card_erase_of_mem hiG]
      have hcard_le : S'.card + 1 ≤ G.card := by
        have hle := Finset.card_le_card (Finset.mem_powerset.mp hS')
        rw [Finset.card_erase_of_mem hiG] at hle
        have hpos : 0 < G.card := Finset.card_pos.mpr ⟨i, hiG⟩
        omega
      have hexp : G.card - 1 - S'.card = G.card - (S'.card + 1) := by omega
      rw [hexp]
  have hpart2 : ∑ S ∈ G.powerset, ∑ i ∈ G \ S,
        (1 - t) ^ S.card * t ^ (G.card - S.card - 1) * subEnt Ω (unifW Ω) id S
      = ∑ i ∈ G, ∑ S' ∈ (G.erase i).powerset,
          subsetWeight (G.erase i) t S' * subEnt Ω (unifW Ω) id S' := by
    have h1 : ∀ S ∈ G.powerset,
        ∑ i ∈ G \ S, (1 - t) ^ S.card * t ^ (G.card - S.card - 1) * subEnt Ω (unifW Ω) id S
        = ∑ i ∈ G, if i ∉ S then (1 - t) ^ S.card * t ^ (G.card - S.card - 1) * subEnt Ω (unifW Ω) id S else 0 := by
      intro S _
      rw [← Finset.sum_filter]
      congr 1; ext i; simp [Finset.mem_sdiff, Finset.mem_filter]
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i hiG
    have hfilt : G.powerset.filter (fun S => i ∉ S) = (G.erase i).powerset := by
      ext S; simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_erase]
    rw [← Finset.sum_filter, hfilt]
    apply Finset.sum_congr rfl; intro S' hS'
    unfold subsetWeight
    rw [Finset.card_erase_of_mem hiG]
    have hle := Finset.card_le_card (Finset.mem_powerset.mp hS')
    rw [Finset.card_erase_of_mem hiG] at hle
    have hpos : 0 < G.card := Finset.card_pos.mpr ⟨i, hiG⟩
    have hexp : G.card - S'.card - 1 = G.card - 1 - S'.card := by omega
    rw [hexp]
  rw [hpart1, hpart2, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl; intro i hiG
  rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl; intro S' hS'
  have hi_not : i ∉ S' := fun h => (Finset.mem_erase.mp (Finset.mem_powerset.mp hS' h)).1 rfl
  rw [subEnt_insert Ω (unifW Ω) id hi_not]
  ring

/-- Fundamental differential identity `CH(t) = deltaH(t) - t * deltaH'(t)`. -/
lemma CH_eq_deltaH_sub_mul_deriv {n : ℕ} (Ω : Finset (Fin n → Bool)) (G : Finset (Fin n)) (t : ℝ) :
    let gH' := -∑ i ∈ G, ∑ S ∈ (G.erase i).powerset,
      subsetWeight (G.erase i) t S * coordCondEnt Ω (unifW Ω) id i S
    CH Ω G t = deltaH Ω G t - t * (gH' + subEnt Ω (unifW Ω) id G) := by
  intro gH'
  -- Show -t * gH' = ∑ S ∈ G.powerset, subsetWeight G t S * ∑ i ∈ G \ S, coordCondEnt Ω (unifW Ω) id i S!
  have htg : -t * gH' =
      ∑ S ∈ G.powerset, subsetWeight G t S * ∑ i ∈ G \ S, coordCondEnt Ω (unifW Ω) id i S := by
    dsimp only [gH']
    rw [neg_mul, mul_neg, neg_neg, Finset.mul_sum]
    have h1 : ∀ i ∈ G,
        t * ∑ S ∈ (G.erase i).powerset, subsetWeight (G.erase i) t S * coordCondEnt Ω (unifW Ω) id i S
        = ∑ S ∈ G.powerset, if i ∉ S then subsetWeight G t S * coordCondEnt Ω (unifW Ω) id i S else 0 := by
      intro i hiG
      rw [← Finset.sum_filter]
      have hfilt : G.powerset.filter (fun S => i ∉ S) = (G.erase i).powerset := by
        ext S; simp [Finset.mem_filter, Finset.mem_powerset, Finset.subset_erase]
      rw [hfilt, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro S hS
      unfold subsetWeight
      rw [Finset.card_erase_of_mem hiG]
      have hle := Finset.card_le_card (Finset.mem_powerset.mp hS)
      rw [Finset.card_erase_of_mem hiG] at hle
      have hpos : 0 < G.card := Finset.card_pos.mpr ⟨i, hiG⟩
      have hexp : G.card - S.card = (G.card - 1 - S.card) + 1 := by omega
      rw [hexp, pow_succ]; ring
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
    apply Finset.sum_congr rfl; intro S _
    rw [Finset.mul_sum, ← Finset.sum_filter]
    have hfilt : G.filter (fun i => i ∉ S) = G \ S := by ext i; simp [Finset.mem_sdiff]
    rw [hfilt]
  unfold CH totalCorr deltaH gH
  have hsplit : ∑ S ∈ G.powerset, subsetWeight G t S *
        ((∑ i ∈ G \ S, coordCondEnt Ω (unifW Ω) id i S)
          - (subEnt Ω (unifW Ω) id G - subEnt Ω (unifW Ω) id S))
      = (∑ S ∈ G.powerset, subsetWeight G t S * ∑ i ∈ G \ S, coordCondEnt Ω (unifW Ω) id i S)
        - (∑ S ∈ G.powerset, subsetWeight G t S) * subEnt Ω (unifW Ω) id G
        + (∑ S ∈ G.powerset, subsetWeight G t S * subEnt Ω (unifW Ω) id S) := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro S _; ring
  rw [hsplit, ← htg, sum_subsetWeight G t, one_mul]
  ring

/-- Beta-type probability density `fTheta(t)` on `[a0Param, 1]`. -/
def fTheta (t : ℝ) : ℝ :=
  (betaParam * b0Param / (1 - b0Param)) * t ^ (-betaParam - 1)

lemma fTheta_nonneg {t : ℝ} (ht : 0 < t) (hD : DParam < kappaParam) : 0 ≤ fTheta t := by
  unfold fTheta
  have hbp : 0 < betaParam := betaParam_pos (hD := hD)
  have hb0p : 0 < b0Param := b0Param_pos
  have h1mb0 : 0 < 1 - b0Param := by linarith [b0Param_lt_one (hD := hD)]
  have hrp : 0 ≤ t ^ (-betaParam - 1) := le_of_lt (Real.rpow_pos_of_pos ht _)
  positivity

lemma continuousOn_fTheta : ContinuousOn fTheta (Set.uIcc a0Param 1) := by
  unfold fTheta
  apply ContinuousOn.mul continuousOn_const
  apply ContinuousOn.rpow_const continuousOn_id
  intro t ht
  left
  have ha0 : a0Param ≤ 1 := le_of_lt a0Param_lt_one
  rw [Set.uIcc_of_le ha0] at ht
  exact ne_of_gt (lt_of_lt_of_le a0Param_pos ht.1)

lemma integral_fTheta (hD : DParam < kappaParam) :
    ∫ t in a0Param..1, fTheta t = 1 := by
  have ha0 : a0Param ≤ 1 := le_of_lt a0Param_lt_one
  let F : ℝ → ℝ := fun t => -(b0Param / (1 - b0Param)) * t ^ (-betaParam)
  have hderiv : ∀ t ∈ Set.uIcc a0Param 1, HasDerivAt F (fTheta t) t := by
    intro t ht
    rw [Set.uIcc_of_le ha0] at ht
    have htpos : 0 < t := lt_of_lt_of_le a0Param_pos ht.1
    have hd := (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt htpos)) (p := -betaParam)).const_mul
      (-(b0Param / (1 - b0Param)))
    exact hd.congr_deriv (by unfold fTheta; ring)
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (continuousOn_fTheta.intervalIntegrable)
  rw [hint]
  simp only [F, Real.one_rpow, mul_one]
  have hb0_ne : b0Param ≠ 0 := ne_of_gt b0Param_pos
  have h1mb0_ne : 1 - b0Param ≠ 0 := ne_of_gt (by linarith [b0Param_lt_one (hD := hD)])
  have hprod : b0Param * a0Param ^ (-betaParam) = 1 := by
    unfold b0Param
    rw [← Real.rpow_add a0Param_pos, add_neg_cancel, Real.rpow_zero]
  field_simp [h1mb0_ne]
  linarith [hprod]

lemma integral_mul_fTheta (hD0 : 0 < DParam) (hD : DParam < kappaParam) :
    ∫ t in a0Param..1, t * fTheta t = etaParam := by
  have ha0 : a0Param ≤ 1 := le_of_lt a0Param_lt_one
  have h1mb : 1 - betaParam = DParam / kappaParam := by unfold betaParam; ring
  have h1mb_ne : 1 - betaParam ≠ 0 := by rw [h1mb]; exact ne_of_gt (div_pos hD0 kappaParam_pos)
  let F : ℝ → ℝ := fun t => (betaParam * b0Param / ((1 - b0Param) * (1 - betaParam))) * t ^ (1 - betaParam)
  have hderiv : ∀ t ∈ Set.uIcc a0Param 1, HasDerivAt F (t * fTheta t) t := by
    intro t ht
    rw [Set.uIcc_of_le ha0] at ht
    have htpos : 0 < t := lt_of_lt_of_le a0Param_pos ht.1
    have hd := (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt htpos)) (p := 1 - betaParam)).const_mul
      (betaParam * b0Param / ((1 - b0Param) * (1 - betaParam)))
    apply hd.congr_deriv
    have hpow : t * t ^ (-betaParam - 1) = t ^ (1 - betaParam - 1) := by
      calc t * t ^ (-betaParam - 1)
          = t ^ (1 : ℝ) * t ^ (-betaParam - 1) := by rw [Real.rpow_one]
        _ = t ^ (1 + (-betaParam - 1)) := (Real.rpow_add htpos _ _).symm
        _ = t ^ (1 - betaParam - 1) := by congr 1; ring
    unfold fTheta
    have h1mb0_ne : 1 - b0Param ≠ 0 := ne_of_gt (by linarith [b0Param_lt_one (hD := hD)])
    rw [show t * (betaParam * b0Param / (1 - b0Param) * t ^ (-betaParam - 1))
          = (betaParam * b0Param / (1 - b0Param)) * (t * t ^ (-betaParam - 1)) by ring, hpow]
    field_simp [h1mb_ne, h1mb_ne]
  have hcont : ContinuousOn (fun t => t * fTheta t) (Set.uIcc a0Param 1) :=
    continuousOn_id.mul continuousOn_fTheta
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
  simp only [F, Real.one_rpow, mul_one]
  have hprod : b0Param * a0Param ^ (1 - betaParam) = a0Param := by
    unfold b0Param
    rw [← Real.rpow_add a0Param_pos, show betaParam + (1 - betaParam) = 1 by ring, Real.rpow_one]
  unfold etaParam
  have h1mb0_ne : 1 - b0Param ≠ 0 := ne_of_gt (by linarith [b0Param_lt_one (hD := hD)])
  have hD_ne : DParam ≠ 0 := ne_of_gt hD0
  have hk_ne : kappaParam ≠ 0 := ne_of_gt kappaParam_pos
  have hbeta_ratio : betaParam / (1 - betaParam) = (kappaParam - DParam) / DParam := by
    unfold betaParam; field_simp [hk_ne, hD_ne]; ring
  calc betaParam * b0Param / ((1 - b0Param) * (1 - betaParam))
        - betaParam * b0Param / ((1 - b0Param) * (1 - betaParam)) * a0Param ^ (1 - betaParam)
      = (betaParam / (1 - betaParam)) * (b0Param - b0Param * a0Param ^ (1 - betaParam)) / (1 - b0Param) := by
        field_simp [h1mb0_ne, h1mb_ne]
    _ = ((kappaParam - DParam) / DParam) * (b0Param - a0Param) / (1 - b0Param) := by
        rw [hbeta_ratio, hprod]

/-- **Exact Beta-Density Integration by Parts (`lem:beta`)**:
    `∫_{a0}^1 fTheta(t) * (κ CH(t) - D deltaH(t)) dt = W * deltaH(a0)`. -/
lemma beta_ibp {n : ℕ} (Ω : Finset (Fin n → Bool)) (hΩ : Ω.Nonempty) (G : Finset (Fin n))
    (hD : DParam < kappaParam) :
    ∫ t in a0Param..1, fTheta t * (kappaParam * CH Ω G t - DParam * deltaH Ω G t)
      = WParam * deltaH Ω G a0Param := by
  have ha0 : a0Param ≤ 1 := le_of_lt a0Param_lt_one
  let Ψ : ℝ → ℝ := fun t => -kappaParam * (betaParam * b0Param / (1 - b0Param)) * t ^ (-betaParam) * deltaH Ω G t
  have hderiv : ∀ t ∈ Set.uIcc a0Param 1,
      HasDerivAt Ψ (fTheta t * (kappaParam * CH Ω G t - DParam * deltaH Ω G t)) t := by
    intro t ht
    rw [Set.uIcc_of_le ha0] at ht
    have htpos : 0 < t := lt_of_lt_of_le a0Param_pos ht.1
    have hd_pow : HasDerivAt (fun u : ℝ => u ^ (-betaParam)) (-betaParam * t ^ (-betaParam - 1)) t :=
      Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt htpos))
    have hd_delta : HasDerivAt (deltaH Ω G)
        ((-∑ i ∈ G, ∑ S ∈ (G.erase i).powerset,
            subsetWeight (G.erase i) t S * coordCondEnt Ω (unifW Ω) id i S)
          + subEnt Ω (unifW Ω) id G) t := by
      unfold deltaH
      have h1 := hasDerivAt_gH Ω G t
      have h2 : HasDerivAt (fun u : ℝ => (1 - u) * subEnt Ω (unifW Ω) id G)
          ((-1) * subEnt Ω (unifW Ω) id G) t := by
        have hsub : HasDerivAt (fun u : ℝ => 1 - u) (-1) t := by
          simpa using (hasDerivAt_const t (1 : ℝ)).fun_sub (hasDerivAt_id' t)
        exact hsub.mul_const _
      exact (h1.fun_sub h2).congr_deriv (by ring)
    have hprod := (hd_pow.const_mul (-kappaParam * (betaParam * b0Param / (1 - b0Param)))).fun_mul hd_delta
    have hΨ_eq : Ψ = fun u => (-kappaParam * (betaParam * b0Param / (1 - b0Param)) * u ^ (-betaParam)) * deltaH Ω G u :=
      rfl
    rw [hΨ_eq]
    apply hprod.congr_deriv
    have hCH := CH_eq_deltaH_sub_mul_deriv Ω G t
    dsimp only at hCH
    have hpow_t : t ^ (-betaParam) = t * t ^ (-betaParam - 1) := by
      calc t ^ (-betaParam) = t ^ (1 + (-betaParam - 1)) := by congr 1; ring
        _ = t ^ (1 : ℝ) * t ^ (-betaParam - 1) := Real.rpow_add htpos _ _
        _ = t * t ^ (-betaParam - 1) := by rw [Real.rpow_one]
    have hkbeta : kappaParam * betaParam = kappaParam - DParam := by
      unfold betaParam; field_simp [ne_of_gt kappaParam_pos]
    unfold fTheta
    rw [hCH, hpow_t]
    set d' := (-∑ i ∈ G, ∑ S ∈ (G.erase i).powerset,
      subsetWeight (G.erase i) t S * coordCondEnt Ω (unifW Ω) id i S) + subEnt Ω (unifW Ω) id G
    calc -kappaParam * (betaParam * b0Param / (1 - b0Param)) * (-betaParam * t ^ (-betaParam - 1)) * deltaH Ω G t
          + -kappaParam * (betaParam * b0Param / (1 - b0Param)) * (t * t ^ (-betaParam - 1)) * d'
        = (betaParam * b0Param / (1 - b0Param)) * t ^ (-betaParam - 1)
          * ((kappaParam * betaParam) * deltaH Ω G t - kappaParam * t * d') := by ring
      _ = (betaParam * b0Param / (1 - b0Param)) * t ^ (-betaParam - 1)
          * (kappaParam * (deltaH Ω G t - t * d') - DParam * deltaH Ω G t) := by rw [hkbeta]; ring
  have hcont_gH : Continuous (gH Ω G) := by
    unfold gH subsetWeight; fun_prop
  have hcont_deltaH : Continuous (deltaH Ω G) := by
    unfold deltaH; exact hcont_gH.sub (by fun_prop)
  have hcont_CH : Continuous (CH Ω G) := by
    unfold CH subsetWeight; fun_prop
  have hcont : ContinuousOn (fun t => fTheta t * (kappaParam * CH Ω G t - DParam * deltaH Ω G t))
      (Set.uIcc a0Param 1) :=
    continuousOn_fTheta.mul ((continuousOn_const.mul hcont_CH.continuousOn).sub
      (continuousOn_const.mul hcont_deltaH.continuousOn))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
  simp only [Ψ, deltaH_one Ω hΩ G, mul_zero, neg_zero, zero_sub, neg_mul, neg_neg]
  have hprod : b0Param * a0Param ^ (-betaParam) = 1 := by
    unfold b0Param
    rw [← Real.rpow_add a0Param_pos, add_neg_cancel, Real.rpow_zero]
  have hkbeta : kappaParam * betaParam = kappaParam - DParam := by
    unfold betaParam; field_simp [ne_of_gt kappaParam_pos]
  unfold WParam
  calc kappaParam * (betaParam * b0Param / (1 - b0Param)) * a0Param ^ (-betaParam) * deltaH Ω G a0Param
      = ((kappaParam * betaParam) * (b0Param * a0Param ^ (-betaParam)) / (1 - b0Param)) * deltaH Ω G a0Param := by ring
    _ = (kappaParam - DParam) / (1 - b0Param) * deltaH Ω G a0Param := by rw [hkbeta, hprod, mul_one]

/-! ### Uniform Permutation Coupling & 3-Vertex Triangle Lemma -/

/-- Permuted list of coordinates from `gList` via `π : Equiv.Perm (Fin gList.length)`. -/
def permList {n : ℕ} (gList : List (Fin n)) (π : Equiv.Perm (Fin gList.length)) : List (Fin n) :=
  List.ofFn (fun j : Fin gList.length => gList[π j])

lemma permList_length {n : ℕ} (gList : List (Fin n)) (π : Equiv.Perm (Fin gList.length)) :
    (permList gList π).length = gList.length := by
  simp [permList]

lemma permList_nodup {n : ℕ} {gList : List (Fin n)} (hnd : gList.Nodup)
    (π : Equiv.Perm (Fin gList.length)) : (permList gList π).Nodup := by
  unfold permList
  rw [List.nodup_ofFn]
  intro i j hij
  exact π.injective ((List.nodup_iff_injective_getElem.mp hnd) hij)

lemma permList_toFinset {n : ℕ} (gList : List (Fin n)) (π : Equiv.Perm (Fin gList.length)) :
    (permList gList π).toFinset = gList.toFinset := by
  ext x
  simp only [permList, List.mem_toFinset]
  rw [List.mem_ofFn, List.mem_iff_getElem]
  constructor
  · rintro ⟨j, rfl⟩; exact ⟨(π j).1, (π j).2, rfl⟩
  · rintro ⟨i, hi, rfl⟩; exact ⟨π.symm ⟨i, hi⟩, by simp⟩

/-- Exact counting lemma: for fixed `k ≤ gList.length` and `S ⊆ G` with `|S| = k`,
    the number of permutations `π : Equiv.Perm (Fin gList.length)` with
    `((permList gList π).take k).toFinset = S` equals `k! * (d - k)!`. -/
lemma card_perm_take_eq {n : ℕ} {G : Finset (Fin n)} {gList : List (Fin n)}
    (hnd : gList.Nodup) (hcov : gList.toFinset = G)
    {k : ℕ} (hk : k ≤ gList.length) {S : Finset (Fin n)} (hSG : S ⊆ G) (hScard : S.card = k) :
    (Finset.univ.filter (fun π : Equiv.Perm (Fin gList.length) =>
        ((permList gList π).take k).toFinset = S)).card
      = Nat.factorial k * Nat.factorial (gList.length - k) := by
  set d := gList.length
  -- Pull S back to A : Finset (Fin d) := {j : Fin d | gList[j] ∈ S}
  let A : Finset (Fin d) := Finset.univ.filter (fun j : Fin d => gList[j] ∈ S)
  let K : Finset (Fin d) := Finset.univ.filter (fun j : Fin d => (j : ℕ) < k)
  have hKcard : K.card = k := by
    have hbij : K = Finset.univ.image (fun j : Fin k => Fin.castLE hk j) := by
      ext j; simp only [K, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro hj; exact ⟨⟨j.1, hj⟩, rfl⟩
      · rintro ⟨a, rfl⟩; exact a.isLt
    rw [hbij, Finset.card_image_of_injective _ (Fin.castLE_injective hk), Finset.card_univ, Fintype.card_fin]
  have hAcard : A.card = k := by
    rw [← hScard]
    apply Finset.card_bij (fun j _ => gList[j])
    · intro j hj; exact (Finset.mem_filter.mp hj).2
    · intro j1 _ j2 _ hEq; exact (List.nodup_iff_injective_getElem.mp hnd) hEq
    · intro x hxS
      have hxG : x ∈ gList.toFinset := hcov.symm ▸ hSG hxS
      rcases List.mem_iff_getElem.mp (List.mem_toFinset.mp hxG) with ⟨idx, hidx, rfl⟩
      exact ⟨⟨idx, hidx⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxS⟩, rfl⟩
  have hKc_card : Kᶜ.card = d - k := by
    rw [Finset.card_compl, Fintype.card_fin, hKcard]
  have hAc_card : Aᶜ.card = d - k := by
    rw [Finset.card_compl, Fintype.card_fin, hAcard]
  -- Characterize the filter condition as: ∀ j, j ∈ K ↔ π j ∈ A
  have hchar : ∀ π : Equiv.Perm (Fin d),
      ((permList gList π).take k).toFinset = S ↔ (∀ j : Fin d, j ∈ K ↔ π j ∈ A) := by
    intro π
    have htake_eq : ((permList gList π).take k).toFinset = K.image (fun j => gList[π j]) := by
      ext x
      simp only [permList, K, List.mem_toFinset, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hx
        rcases List.mem_iff_getElem.mp hx with ⟨idx, hidx, rfl⟩
        have hidx_k : idx < k := by simp only [List.length_take, List.length_ofFn] at hidx; omega
        have hidx_d : idx < d := lt_of_lt_of_le hidx_k hk
        refine ⟨⟨idx, hidx_d⟩, hidx_k, ?_⟩
        simp [List.getElem_take]
      · rintro ⟨j, hjk, rfl⟩
        have hidx : (j : ℕ) < ((List.ofFn fun j : Fin d => gList[π j]).take k).length := by
          simp [hjk, j.isLt]
        rw [List.mem_iff_getElem]
        exact ⟨j.1, hidx, by simp [List.getElem_take]⟩
    rw [htake_eq]
    constructor
    · intro hEq j
      have hcard_img : (K.image (fun t => gList[π t])).card = k := by rw [hEq, hScard]
      constructor
      · intro hjK
        have hmem : gList[π j] ∈ S := by
          rw [← hEq]; exact Finset.mem_image_of_mem _ hjK
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmem⟩
      · intro hπjA
        have hmemS : gList[π j] ∈ K.image (fun t => gList[π t]) := by
          rw [hEq]; exact (Finset.mem_filter.mp hπjA).2
        rcases Finset.mem_image.mp hmemS with ⟨t, htK, hteq⟩
        have hπeq : π t = π j := (List.nodup_iff_injective_getElem.mp hnd) hteq
        have htjeq : t = j := π.injective hπeq
        rwa [← htjeq]
    · intro hiff
      ext x
      simp only [Finset.mem_image]
      constructor
      · rintro ⟨j, hjK, rfl⟩
        exact (Finset.mem_filter.mp ((hiff j).mp hjK)).2
      · intro hxS
        have hxG : x ∈ gList.toFinset := hcov.symm ▸ hSG hxS
        rcases List.mem_iff_getElem.mp (List.mem_toFinset.mp hxG) with ⟨idx, hidx, rfl⟩
        let a : Fin d := ⟨idx, hidx⟩
        have haA : a ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxS⟩
        refine ⟨π.symm a, (hiff (π.symm a)).mpr (by simpa using haA), by simp [a]⟩
  -- Build explicit bijection between Equiv.Perm K × Equiv.Perm Kᶜ and the filtered Finset!
  let e1 : {j : Fin d // j ∈ K} ≃ {j : Fin d // j ∈ A} :=
    Fintype.equivOfCardEq (by simp [hKcard, hAcard])
  let e2 : {j : Fin d // j ∈ Kᶜ} ≃ {j : Fin d // j ∈ Aᶜ} :=
    Fintype.equivOfCardEq (by simp [hKcard, hAcard])
  let mkPerm : Equiv.Perm {j : Fin d // j ∈ K} × Equiv.Perm {j : Fin d // j ∈ Kᶜ} → Equiv.Perm (Fin d) :=
    fun p =>
      { toFun := fun j =>
          if h : j ∈ K then (e1 (p.1 ⟨j, h⟩)).1 else (e2 (p.2 ⟨j, Finset.mem_compl.mpr h⟩)).1
        invFun := fun a =>
          if h : a ∈ A then (p.1.symm (e1.symm ⟨a, h⟩)).1 else (p.2.symm (e2.symm ⟨a, Finset.mem_compl.mpr h⟩)).1
        left_inv := fun j => by
          by_cases h : j ∈ K
          · simp [h, (e1 (p.1 ⟨j, h⟩)).2]
          · have hnotA : (e2 (p.2 ⟨j, Finset.mem_compl.mpr h⟩)).1 ∉ A :=
              Finset.mem_compl.mp (e2 (p.2 ⟨j, Finset.mem_compl.mpr h⟩)).2
            simp [h, hnotA]
        right_inv := fun a => by
          by_cases h : a ∈ A
          · simp [h, (p.1.symm (e1.symm ⟨a, h⟩)).2]
          · have hnotK : (p.2.symm (e2.symm ⟨a, Finset.mem_compl.mpr h⟩)).1 ∉ K :=
              Finset.mem_compl.mp (p.2.symm (e2.symm ⟨a, Finset.mem_compl.mpr h⟩)).2
            simp [h, hnotK] }
  have hcard_eq : (Finset.univ : Finset (Equiv.Perm {j : Fin d // j ∈ K} × Equiv.Perm {j : Fin d // j ∈ Kᶜ})).card
      = (Finset.univ.filter (fun π : Equiv.Perm (Fin d) => ((permList gList π).take k).toFinset = S)).card := by
    apply Finset.card_bij (fun p _ => mkPerm p)
    · intro p _
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, (hchar (mkPerm p)).mpr ?_⟩
      intro j
      by_cases hj : j ∈ K
      · simp [mkPerm, hj, (e1 (p.1 ⟨j, hj⟩)).2]
      · have hnotA : (e2 (p.2 ⟨j, Finset.mem_compl.mpr hj⟩)).1 ∉ A :=
          Finset.mem_compl.mp (e2 (p.2 ⟨j, Finset.mem_compl.mpr hj⟩)).2
        simp [mkPerm, hj, hnotA]
    · intro p1 _ p2 _ hEq
      ext ⟨j, hj⟩
      · have h := congr_arg (fun π : Equiv.Perm (Fin d) => π j) hEq
        simp only [mkPerm, Equiv.coe_fn_mk, hj, ↓reduceDIte] at h
        have hsub : e1 (p1.1 ⟨j, hj⟩) = e1 (p2.1 ⟨j, hj⟩) := Subtype.ext h
        exact congr_arg Fin.val (congr_arg Subtype.val (e1.injective hsub))
      · have hnot : j ∉ K := Finset.mem_compl.mp hj
        have h := congr_arg (fun π : Equiv.Perm (Fin d) => π j) hEq
        simp only [mkPerm, Equiv.coe_fn_mk, hnot, ↓reduceDIte] at h
        have hsub : e2 (p1.2 ⟨j, hj⟩) = e2 (p2.2 ⟨j, hj⟩) := Subtype.ext h
        exact congr_arg Fin.val (congr_arg Subtype.val (e2.injective hsub))
    · intro π hπ
      have hiff := (hchar π).mp (Finset.mem_filter.mp hπ).2
      let σ1 : Equiv.Perm {j : Fin d // j ∈ K} :=
        { toFun := fun x => e1.symm ⟨π x.1, (hiff x.1).mp x.2⟩
          invFun := fun y => ⟨π.symm (e1 y).1, (hiff (π.symm (e1 y).1)).mpr (by simp)⟩
          left_inv := fun x => by ext; simp
          right_inv := fun y => by apply e1.injective; ext; simp }
      let σ2 : Equiv.Perm {j : Fin d // j ∈ Kᶜ} :=
        { toFun := fun x => e2.symm ⟨π x.1, Finset.mem_compl.mpr (fun h => Finset.mem_compl.mp x.2 ((hiff x.1).mpr h))⟩
          invFun := fun y => ⟨π.symm (e2 y).1, Finset.mem_compl.mpr (fun h =>
            Finset.mem_compl.mp (e2 y).2 (by simpa using (hiff (π.symm (e2 y).1)).mp h))⟩
          left_inv := fun x => by ext; simp
          right_inv := fun y => by apply e2.injective; ext; simp }
      refine ⟨(σ1, σ2), Finset.mem_univ _, ?_⟩
      ext j
      by_cases hj : j ∈ K
      · simp [mkPerm, σ1, hj]
      · simp [mkPerm, σ2, hj]
  rw [← hcard_eq, Finset.card_univ, Fintype.card_prod, Fintype.card_perm, Fintype.card_perm,
      Fintype.card_coe, Fintype.card_coe, hKcard, hKc_card]

/-- Exact permutation-subset averaging identity:
    averaging `φ(S)` over `S ~ S_t` equals averaging `φ(take_k(π))` over `k ~ Bin(d, 1 - t)`
    and uniformly random `π : Equiv.Perm (Fin d)`. -/
lemma avg_perm_subset {n : ℕ} {G : Finset (Fin n)} {gList : List (Fin n)}
    (hnd : gList.Nodup) (hcov : gList.toFinset = G) (t : ℝ) (φ : Finset (Fin n) → ℝ) :
    ∑ S ∈ G.powerset, subsetWeight G t S * φ S
      = ∑ k ∈ Finset.range (gList.length + 1),
          (Nat.choose gList.length k : ℝ) * (1 - t) ^ k * t ^ (gList.length - k)
            * ((1 / (Nat.factorial gList.length : ℝ))
                * ∑ π : Equiv.Perm (Fin gList.length), φ (((permList gList π).take k).toFinset)) := by
  set d := gList.length
  have hGd : G.card = d := by rw [← hcov, List.toFinset_card_of_nodup hnd]
  -- Group G.powerset by S.card = k
  rw [← Finset.sum_fiberwise_of_maps_to (g := Finset.card) (t := Finset.range (d + 1))
        (fun S hS => Finset.mem_range.mpr (Nat.lt_succ_of_le (by rw [← hGd]; exact Finset.card_le_card (Finset.mem_powerset.mp hS))))]
  apply Finset.sum_congr rfl
  intro k hk
  have hk_le : k ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hfilt : G.powerset.filter (fun S => S.card = k) = G.powersetCard k := by
    ext S; simp [Finset.mem_powersetCard]
  rw [hfilt]
  -- Group ∑_π φ(take_k(π)) by the resulting k-element subset S ∈ G.powersetCard k!
  have hmaps : ∀ π ∈ (Finset.univ : Finset (Equiv.Perm (Fin d))),
      ((permList gList π).take k).toFinset ∈ G.powersetCard k := by
    intro π _
    rw [Finset.mem_powersetCard]
    constructor
    · intro x hx
      rw [← hcov, ← permList_toFinset gList π, List.mem_toFinset]
      exact List.mem_of_mem_take (List.mem_toFinset.mp hx)
    · rw [List.toFinset_card_of_nodup (permList_nodup hnd π).take,
          List.length_take, permList_length, min_eq_left hk_le]
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun π => ((permList gList π).take k).toFinset) hmaps]
  have hfib : ∀ S ∈ G.powersetCard k,
      ∑ π ∈ Finset.univ.filter (fun π : Equiv.Perm (Fin d) => ((permList gList π).take k).toFinset = S),
        φ (((permList gList π).take k).toFinset)
      = ((Nat.factorial k * Nat.factorial (d - k) : ℕ) : ℝ) * φ S := by
    intro S hS
    have hSG := (Finset.mem_powersetCard.mp hS).1
    have hSc := (Finset.mem_powersetCard.mp hS).2
    have hcongr : ∀ π ∈ Finset.univ.filter (fun π : Equiv.Perm (Fin d) => ((permList gList π).take k).toFinset = S),
        φ (((permList gList π).take k).toFinset) = φ S := by
      intro π hπ; rw [(Finset.mem_filter.mp hπ).2]
    rw [Finset.sum_congr rfl hcongr, Finset.sum_const, nsmul_eq_mul,
        card_perm_take_eq hnd hcov hk_le hSG hSc]
  rw [Finset.sum_congr rfl hfib, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  have hSc := (Finset.mem_powersetCard.mp hS).2
  unfold subsetWeight
  rw [hGd, hSc]
  have hfact_id : (Nat.choose d k : ℝ) * ((Nat.factorial k * Nat.factorial (d - k) : ℕ) : ℝ)
      = (Nat.factorial d : ℝ) := by
    have hnat := Nat.choose_mul_factorial_mul_factorial hk_le
    rw [mul_assoc] at hnat
    exact_mod_cast hnat
  have hfact_ne : (Nat.factorial d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero d)
  calc (1 - t) ^ k * t ^ (d - k) * φ S
      = (1 - t) ^ k * t ^ (d - k) * ((Nat.factorial d : ℝ) / (Nat.factorial d : ℝ)) * φ S := by
        rw [div_self hfact_ne, mul_one]
    _ = (1 - t) ^ k * t ^ (d - k)
        * (((Nat.choose d k : ℝ) * ((Nat.factorial k * Nat.factorial (d - k) : ℕ) : ℝ))
            / (Nat.factorial d : ℝ)) * φ S := by rw [← hfact_id]
    _ = (Nat.choose d k : ℝ) * (1 - t) ^ k * t ^ (d - k)
        * (1 / (Nat.factorial d : ℝ) * (((Nat.factorial k * Nat.factorial (d - k) : ℕ) : ℝ) * φ S)) := by ring

/-- Binomial lower tail `P(Bin(d, 1 - t) ≤ j)`. -/
def binLe (d : ℕ) (t : ℝ) (j : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (j + 1), (Nat.choose d k : ℝ) * (1 - t) ^ k * t ^ (d - k)

/-- Exact derivative of `binLe d · j` for `j < d`:
    `d/dt [P(Bin(d, 1 - t) ≤ j)] = (d - j) * choose d j * (1 - t)^j * t^(d - j - 1) ≥ 0`! -/
lemma hasDerivAt_binLe (d : ℕ) {j : ℕ} (hj : j < d) (t : ℝ) :
    HasDerivAt (fun u => binLe d u j)
      (((d - j : ℕ) : ℝ) * (Nat.choose d j : ℝ) * (1 - t) ^ j * t ^ (d - j - 1)) t := by
  have hterm : ∀ k ∈ Finset.range (j + 1),
      HasDerivAt (fun u : ℝ => (Nat.choose d k : ℝ) * (1 - u) ^ k * u ^ (d - k))
        ((Nat.choose d k : ℝ) *
          (-(k : ℝ) * (1 - t) ^ (k - 1) * t ^ (d - k)
            + ((d - k : ℕ) : ℝ) * (1 - t) ^ k * t ^ (d - k - 1))) t := by
    intro k _
    have h1 : HasDerivAt (fun u : ℝ => (1 - u) ^ k) ((k : ℝ) * (1 - t) ^ (k - 1) * (-1)) t := by
      have hsub : HasDerivAt (fun u : ℝ => 1 - u) (-1) t := by
        simpa using (hasDerivAt_const t (1 : ℝ)).fun_sub (hasDerivAt_id' t)
      exact (hasDerivAt_pow k (1 - t)).comp t hsub
    have h2 : HasDerivAt (fun u : ℝ => u ^ (d - k)) (((d - k : ℕ) : ℝ) * t ^ (d - k - 1)) t :=
      hasDerivAt_pow (d - k) t
    have h3 := (h1.const_mul (Nat.choose d k : ℝ)).fun_mul h2
    exact h3.congr_deriv (by ring)
  have hsum : HasDerivAt (fun u => binLe d u j)
      (∑ k ∈ Finset.range (j + 1),
        (Nat.choose d k : ℝ) *
          (-(k : ℝ) * (1 - t) ^ (k - 1) * t ^ (d - k)
            + ((d - k : ℕ) : ℝ) * (1 - t) ^ k * t ^ (d - k - 1))) t :=
    HasDerivAt.fun_sum hterm
  apply hsum.congr_deriv
  -- Prove telescoping sum by induction on j < d!
  clear hterm hsum
  induction j with
  | zero =>
    simp [Nat.choose_zero_right]
  | succ m ih =>
    have hm : m < d := Nat.lt_of_succ_lt hj
    rw [Finset.sum_range_succ, ih hm]
    -- Cancellation: (d - m) * C(d, m) = (m + 1) * C(d, m + 1)!
    have hchoose : ((d - m : ℕ) : ℝ) * (Nat.choose d m : ℝ)
        = ((m + 1 : ℕ) : ℝ) * (Nat.choose d (m + 1) : ℝ) := by
      have hnat : (m + 1) * Nat.choose d (m + 1) = (d - m) * Nat.choose d m := by
        have h3 := Nat.choose_succ_right_eq d m
        linarith
      exact_mod_cast hnat.symm
    have hexp : d - m - 1 = d - (m + 1) := by omega
    rw [Nat.add_sub_cancel, hexp]
    push_cast at hchoose ⊢
    linear_combination (1 - t) ^ m * t ^ (d - (m + 1)) * hchoose

lemma binLe_mono {d j : ℕ} (hj : j < d) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    binLe d a j ≤ binLe d b j := by
  have hmono : MonotoneOn (fun u => binLe d u j) (Set.Icc 0 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
    · unfold binLe; fun_prop
    · intro u _; exact (hasDerivAt_binLe d hj u).differentiableAt.differentiableWithinAt
    · intro u hu; rw [interior_Icc] at hu
      rw [(hasDerivAt_binLe d hj u).deriv]
      have h1 : 0 ≤ 1 - u := by linarith [hu.2]
      have h2 : 0 ≤ u := le_of_lt hu.1
      positivity
  exact hmono ⟨ha, le_trans hab hb⟩ ⟨le_trans ha hab, hb⟩ hab

lemma binLe_le_one {d j : ℕ} (hj : j < d) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    binLe d t j ≤ 1 := by
  have hpow := add_pow (1 - t) t d
  rw [sub_add_cancel, one_pow] at hpow
  have hpow' : ∑ m ∈ Finset.range (d + 1), (1 - t) ^ m * t ^ (d - m) * (Nat.choose d m : ℝ)
      = ∑ k ∈ Finset.range (d + 1), (Nat.choose d k : ℝ) * (1 - t) ^ k * t ^ (d - k) :=
    Finset.sum_congr rfl fun k _ => by ring
  rw [hpow, hpow']
  unfold binLe
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.range_mono (Nat.succ_le_succ (le_of_lt hj))
  · intro k _ _
    have h1 : 0 ≤ 1 - t := by linarith
    positivity

lemma binLe_nonneg (d j : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ binLe d t j := by
  unfold binLe
  apply Finset.sum_nonneg; intro k _
  have h1 : 0 ≤ 1 - t := by linarith
  positivity

/-- Exact identity `∑_{j=0}^{d-1} binLe d t j = d * t`. -/
lemma sum_binLe (d : ℕ) (t : ℝ) :
    ∑ j : Fin d, binLe d t j = (d : ℝ) * t := by
  -- Swap sums: ∑_{j=0}^{d-1} ∑_{k=0}^j P(k) = ∑_{k=0}^d (d - k) P(k)
  unfold binLe
  have hswap : ∑ j : Fin d, ∑ k ∈ Finset.range ((j : ℕ) + 1),
        (Nat.choose d k : ℝ) * (1 - t) ^ k * t ^ (d - k)
      = ∑ k ∈ Finset.range (d + 1),
          ((d - k : ℕ) : ℝ) * ((Nat.choose d k : ℝ) * (1 - t) ^ k * t ^ (d - k)) := by
    have h1 : ∀ j : Fin d,
        ∑ k ∈ Finset.range ((j : ℕ) + 1), (Nat.choose d k : ℝ) * (1 - t) ^ k * t ^ (d - k)
        = ∑ k ∈ Finset.range (d + 1),
            if k ≤ (j : ℕ) then (Nat.choose d k : ℝ) * (1 - t) ^ k * t ^ (d - k) else 0 := by
      intro j
      rw [← Finset.sum_filter]
      congr 1; ext k; simp only [Finset.mem_filter, Finset.mem_range]; omega
    simp_rw [h1]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro k hk
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    congr 1
    have hcard : (Finset.univ.filter (fun j : Fin d => k ≤ (j : ℕ))).card = d - k := by
      have hk_le : k ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have hcompl : (Finset.univ.filter (fun j : Fin d => k ≤ (j : ℕ))).card
          + (Finset.univ.filter (fun j : Fin d => ¬ (k ≤ (j : ℕ)))).card = d := by
        simpa [Fintype.card_fin] using Finset.card_filter_add_card_filter_not
          (s := (Finset.univ : Finset (Fin d))) (p := fun j : Fin d => k ≤ (j : ℕ))
      have hlt_card : (Finset.univ.filter (fun j : Fin d => ¬ (k ≤ (j : ℕ)))).card = k := by
        have hbij : Finset.univ.filter (fun j : Fin d => ¬ (k ≤ (j : ℕ)))
            = Finset.univ.image (fun i : Fin k => Fin.castLE hk_le i) := by
          ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le, Finset.mem_image]
          constructor
          · intro hj; exact ⟨⟨j.1, hj⟩, rfl⟩
          · rintro ⟨i, rfl⟩; exact i.isLt
        rw [hbij, Finset.card_image_of_injective _ (Fin.castLE_injective hk_le), Finset.card_univ, Fintype.card_fin]
      omega
    rw [hcard]
  rw [hswap]
  -- Now evaluate ∑_{k=0}^d (d - k) C(d, k) (1 - t)^k t^(d - k) = d * t * ((1 - t) + t)^(d - 1) = d * t!
  rcases d with _ | d'
  · simp
  · rw [Finset.sum_range_succ]
    simp only [Nat.sub_self, Nat.cast_zero, zero_mul, add_zero]
    have hpow := add_pow (1 - t) t d'
    rw [sub_add_cancel, one_pow] at hpow
    have hterm : ∀ k ∈ Finset.range (d' + 1),
        (((d' + 1) - k : ℕ) : ℝ) * ((Nat.choose (d' + 1) k : ℝ) * (1 - t) ^ k * t ^ ((d' + 1) - k))
        = ((d' + 1 : ℕ) : ℝ) * t * ((1 - t) ^ k * t ^ (d' - k) * (Nat.choose d' k : ℝ)) := by
      intro k hk
      have hk_le : k ≤ d' := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have hnat : (d' + 1 - k) * Nat.choose (d' + 1) k = (d' + 1) * Nat.choose d' k := by
        have h1 := Nat.choose_mul_succ_eq d' (d' - k)
        -- Use symmetry or direct formula: (d'+1-k) * C(d'+1, k) = (d'+1) * C(d', k)
        have h2 : Nat.choose (d' + 1) k * (d' + 1 - k) = (d' + 1) * Nat.choose d' k := by
          have := Nat.choose_succ_right_eq (d' + 1) (d' - k)
          -- Easier: prove via factorials!
          have hf1 := Nat.choose_mul_factorial_mul_factorial (Nat.le_succ_of_le hk_le)
          have hf2 := Nat.choose_mul_factorial_mul_factorial hk_le
          have hsub : d' + 1 - k = (d' - k) + 1 := by omega
          rw [hsub, Nat.factorial_succ] at hf1
          have hfact_ne : 0 < Nat.factorial k * Nat.factorial (d' - k) :=
            Nat.mul_pos (Nat.factorial_pos k) (Nat.factorial_pos (d' - k))
          have hlhs : Nat.choose (d' + 1) k * (d' + 1 - k) * (Nat.factorial k * Nat.factorial (d' - k))
              = (d' + 1) * Nat.choose d' k * (Nat.factorial k * Nat.factorial (d' - k)) := by
            rw [hsub]
            calc Nat.choose (d' + 1) k * (d' - k + 1) * (Nat.factorial k * Nat.factorial (d' - k))
                = Nat.choose (d' + 1) k * Nat.factorial k * ((d' - k + 1) * Nat.factorial (d' - k)) := by ring
              _ = Nat.factorial (d' + 1) := hf1
              _ = (d' + 1) * Nat.factorial d' := Nat.factorial_succ d'
              _ = (d' + 1) * (Nat.choose d' k * Nat.factorial k * Nat.factorial (d' - k)) := by rw [← hf2]
              _ = (d' + 1) * Nat.choose d' k * (Nat.factorial k * Nat.factorial (d' - k)) := by ring
          exact Nat.eq_of_mul_eq_mul_right hfact_ne hlhs
        linarith
      have hcast : (((d' + 1) - k : ℕ) : ℝ) * (Nat.choose (d' + 1) k : ℝ)
          = ((d' + 1 : ℕ) : ℝ) * (Nat.choose d' k : ℝ) := by exact_mod_cast hnat
      have hsub : d' + 1 - k = (d' - k) + 1 := by omega
      rw [hsub, pow_succ]
      rw [hsub] at hcast
      linear_combination (1 - t) ^ k * t ^ (d' - k) * t * hcast
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← hpow, mul_one]

/-- Weights `w_j` and `ω_j` for our 3-Vertex Single-Order Master Theorem. -/
def wWeight (d : ℕ) (j : ℕ) : ℝ :=
  ∫ t in a0Param..1, fTheta t * binLe d t j

def omWeight (d : ℕ) (j : ℕ) : ℝ :=
  a0Param - binLe d a0Param j

lemma sum_wWeight (d : ℕ) (hD0 : 0 < DParam) (hD : DParam < kappaParam) :
    ∑ j : Fin d, wWeight d j = etaParam * d := by
  unfold wWeight
  have hint : ∀ j ∈ (Finset.univ : Finset (Fin d)),
      IntervalIntegrable (fun t => fTheta t * binLe d t j) MeasureTheory.volume a0Param 1 := by
    intro j _
    apply ContinuousOn.intervalIntegrable
    exact continuousOn_fTheta.mul (by unfold binLe; fun_prop)
  rw [← intervalIntegral.integral_finsetSum hint]
  have hsum : ∀ t, ∑ j : Fin d, fTheta t * binLe d t j = (d : ℝ) * (t * fTheta t) := by
    intro t; rw [← Finset.mul_sum, sum_binLe]; ring
  simp_rw [hsum]
  rw [intervalIntegral.integral_const_mul, integral_mul_fTheta hD0 hD]
  ring

lemma sum_omWeight (d : ℕ) :
    ∑ j : Fin d, omWeight d j = 0 := by
  unfold omWeight
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, sum_binLe]
  ring

/-- **3-Vertex Triangle Lemma**:
    For every `j < d`, `(wWeight d j, omWeight d j)` satisfies:
    `w_j ≤ 1`, `ω_j ≤ a0Param`, and `a0Param ≤ w_j + ω_j`. -/
lemma three_vertex_triangle (d : ℕ) {j : ℕ} (hj : j < d) (hD : DParam < kappaParam) :
    wWeight d j ≤ 1 ∧ omWeight d j ≤ a0Param ∧ a0Param ≤ wWeight d j + omWeight d j := by
  have ha0 : a0Param ≤ 1 := le_of_lt a0Param_lt_one
  have hint_w : IntervalIntegrable (fun t => fTheta t * binLe d t j) MeasureTheory.volume a0Param 1 :=
    (continuousOn_fTheta.mul (by unfold binLe; fun_prop)).intervalIntegrable
  refine ⟨?_, ?_, ?_⟩
  · -- w_j ≤ 1
    rw [← integral_fTheta hD]
    apply intervalIntegral.integral_mono_on ha0 hint_w continuousOn_fTheta.intervalIntegrable
    intro t ht
    have hf : 0 ≤ fTheta t := fTheta_nonneg (lt_of_lt_of_le a0Param_pos ht.1) hD
    have hb : binLe d t j ≤ 1 := binLe_le_one hj (le_trans (le_of_lt a0Param_pos) ht.1) ht.2
    nlinarith
  · -- ω_j = a0 - binLe d a0 j ≤ a0
    unfold omWeight
    linarith [binLe_nonneg d j (le_of_lt a0Param_pos) ha0]
  · -- w_j + ω_j ≥ a0  <=>  w_j ≥ binLe d a0 j
    unfold omWeight wWeight
    have hconst : binLe d a0Param j = ∫ t in a0Param..1, fTheta t * binLe d a0Param j := by
      rw [intervalIntegral.integral_mul_const, integral_fTheta hD, one_mul]
    have hle : ∫ t in a0Param..1, fTheta t * binLe d a0Param j ≤ ∫ t in a0Param..1, fTheta t * binLe d t j := by
      apply intervalIntegral.integral_mono_on ha0
        (continuousOn_fTheta.mul continuousOn_const).intervalIntegrable hint_w
      intro t ht
      have hf : 0 ≤ fTheta t := fTheta_nonneg (lt_of_lt_of_le a0Param_pos ht.1) hD
      have hmono := binLe_mono hj (le_of_lt a0Param_pos) ht.1 ht.2
      exact mul_le_mul_of_nonneg_left hmono hf
    linarith

/-- Any affine function in `(w, ω)` that is nonnegative at the 3 vertices
    `(0, a0)`, `(1, a0)`, `(1, a0 - 1)` is nonnegative on the entire triangle
    `w ≤ 1, ω ≤ a0, a0 ≤ w + ω`! -/
lemma affine_ge_zero_of_three_vertices {c0 c1 c2 w om : ℝ}
    (hw : w ≤ 1) (hom : om ≤ a0Param) (hsum : a0Param ≤ w + om)
    (hv1 : 0 ≤ c0 + c1 * 0 + c2 * a0Param)
    (hv2 : 0 ≤ c0 + c1 * 1 + c2 * a0Param)
    (hv3 : 0 ≤ c0 + c1 * 1 + c2 * (a0Param - 1)) :
    0 ≤ c0 + c1 * w + c2 * om := by
  have h1 : 0 ≤ 1 - w := by linarith
  have h2 : 0 ≤ w + om - a0Param := by linarith
  have h3 : 0 ≤ a0Param - om := by linarith
  have hid : c0 + c1 * w + c2 * om
      = (1 - w) * (c0 + c1 * 0 + c2 * a0Param)
        + (w + om - a0Param) * (c0 + c1 * 1 + c2 * a0Param)
        + (a0Param - om) * (c0 + c1 * 1 + c2 * (a0Param - 1)) := by ring
  rw [hid]
  nlinarith

/-- Express `deltaH Ω G a0Param` as the permutation average of `∑_j ω_j (e_{π, j} - eStar)`. -/
lemma deltaH_a0_eq_perm_avg {n : ℕ} (Ω : Finset (Fin n → Bool)) (hΩ : Ω.Nonempty)
    {G : Finset (Fin n)} {gList : List (Fin n)}
    (hnd : gList.Nodup) (hcov : gList.toFinset = G) :
    deltaH Ω G a0Param =
      (1 / (Nat.factorial gList.length : ℝ)) *
        ∑ π : Equiv.Perm (Fin gList.length),
          ∑ j : Fin gList.length,
            omWeight gList.length j *
              (coordCondEnt Ω (unifW Ω) id ((permList gList π)[j]'(by simp [permList]))
                (((permList gList π).take j).toFinset) - eStar) := by
  set d := gList.length
  unfold deltaH gH
  rw [avg_perm_subset hnd hcov a0Param (fun S => subEnt Ω (unifW Ω) id S)]
  -- For each π and k ≤ d, subEnt(take_k(π)) = ∑_{j < k} e_{π, j}!
  have hchain_take : ∀ (π : Equiv.Perm (Fin d)) (k : ℕ), k ≤ d →
      subEnt Ω (unifW Ω) id (((permList gList π).take k).toFinset)
      = ∑ j : Fin d, if (j : ℕ) < k then
          coordCondEnt Ω (unifW Ω) id ((permList gList π)[j]'(by simp [permList, d]))
            (((permList gList π).take j).toFinset)
        else 0 := by
    intro π k hk
    have hnd_take : ((permList gList π).take k).Nodup := (permList_nodup hnd π).take
    have hlen_take : ((permList gList π).take k).length = k := by simp [permList, d, hk]
    have h1 := subEnt_append_list Ω (unifW Ω) id ∅ ((permList gList π).take k) hnd_take (by simp)
    simp only [Finset.empty_union, subEnt_empty Ω (unifW Ω) (sum_unifW hΩ) id, sub_zero] at h1
    rw [h1, ← Finset.sum_filter]
    apply Finset.sum_nbij (fun a : Fin ((permList gList π).take k).length =>
      (⟨a.1, lt_of_lt_of_le (lt_of_lt_of_eq a.isLt hlen_take) hk⟩ : Fin d))
    · intro a _
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_of_lt_of_eq a.isLt hlen_take⟩
    · intro a1 _ a2 _ hEq; ext; simpa using congr_arg Fin.val hEq
    · intro j hj
      have hjk : (j : ℕ) < k := (Finset.mem_filter.mp hj).2
      exact ⟨⟨j.1, by omega⟩, Finset.mem_univ _, by ext; rfl⟩
    · intro a _
      have hak : (a : ℕ) < k := lt_of_lt_of_eq a.isLt hlen_take
      congr 1
      · simp [List.getElem_take]
      · simp [List.take_take, min_eq_left (le_of_lt hak)]
  have hchain_full : ∀ π : Equiv.Perm (Fin d),
      subEnt Ω (unifW Ω) id G =
        ∑ j : Fin d, coordCondEnt Ω (unifW Ω) id ((permList gList π)[j]'(by simp [permList, d]))
          (((permList gList π).take j).toFinset) := by
    intro π
    have h := hchain_take π d le_rfl
    have htake_d : ((permList gList π).take d).toFinset = G := by
      have : (permList gList π).take d = permList gList π := List.take_of_length_le (by simp [permList, d])
      rw [this, permList_toFinset, hcov]
    rw [htake_d] at h
    rw [h]
    apply Finset.sum_congr rfl; intro j _; simp [j.isLt]
  -- Swap sums in gH(a0):
  have hgH_eq : ∑ k ∈ Finset.range (d + 1),
        (Nat.choose d k : ℝ) * (1 - a0Param) ^ k * a0Param ^ (d - k)
          * ((1 / (Nat.factorial d : ℝ))
              * ∑ π : Equiv.Perm (Fin d), subEnt Ω (unifW Ω) id (((permList gList π).take k).toFinset))
      = (1 / (Nat.factorial d : ℝ)) *
          ∑ π : Equiv.Perm (Fin d),
            ∑ j : Fin d,
              (1 - binLe d a0Param j) *
                coordCondEnt Ω (unifW Ω) id ((permList gList π)[j]'(by simp [permList, d]))
                  (((permList gList π).take j).toFinset) := by
    have hrew1 : ∀ k ∈ Finset.range (d + 1),
        (Nat.choose d k : ℝ) * (1 - a0Param) ^ k * a0Param ^ (d - k)
          * ((1 / (Nat.factorial d : ℝ))
              * ∑ π : Equiv.Perm (Fin d), subEnt Ω (unifW Ω) id (((permList gList π).take k).toFinset))
        = (1 / (Nat.factorial d : ℝ)) *
            ∑ π : Equiv.Perm (Fin d),
              ∑ j : Fin d,
                (if (j : ℕ) < k then (Nat.choose d k : ℝ) * (1 - a0Param) ^ k * a0Param ^ (d - k) else 0)
                  * coordCondEnt Ω (unifW Ω) id ((permList gList π)[j]'(by simp [permList, d]))
                      (((permList gList π).take j).toFinset) := by
      intro k hk
      have hk_le : k ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      rw [← mul_assoc, mul_comm ((Nat.choose d k : ℝ) * (1 - a0Param) ^ k * a0Param ^ (d - k)),
          mul_assoc, Finset.mul_sum]
      congr 1; apply Finset.sum_congr rfl; intro π _
      rw [hchain_take π k hk_le, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro j _
      split_ifs <;> ring
    rw [Finset.sum_congr rfl hrew1, ← Finset.mul_sum, Finset.sum_comm]
    congr 1; apply Finset.sum_congr rfl; intro π _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro j _
    rw [← Finset.sum_mul]
    congr 1
    -- ∑_{k=0}^d (if j < k then P(k) else 0) = 1 - binLe d a0 j!
    have hpow := add_pow (1 - a0Param) a0Param d
    rw [sub_add_cancel, one_pow] at hpow
    have hsplit : ∑ k ∈ Finset.range (d + 1),
          (Nat.choose d k : ℝ) * (1 - a0Param) ^ k * a0Param ^ (d - k)
        = (∑ k ∈ Finset.range ((j : ℕ) + 1), (Nat.choose d k : ℝ) * (1 - a0Param) ^ k * a0Param ^ (d - k))
          + (∑ k ∈ Finset.range (d + 1),
              if (j : ℕ) < k then (Nat.choose d k : ℝ) * (1 - a0Param) ^ k * a0Param ^ (d - k) else 0) := by
      have hle_eq : ∑ k ∈ Finset.range ((j : ℕ) + 1), (Nat.choose d k : ℝ) * (1 - a0Param) ^ k * a0Param ^ (d - k)
          = ∑ k ∈ Finset.range (d + 1),
              if ¬((j : ℕ) < k) then (Nat.choose d k : ℝ) * (1 - a0Param) ^ k * a0Param ^ (d - k) else 0 := by
        rw [← Finset.sum_filter]
        congr 1; ext k; simp only [Finset.mem_filter, Finset.mem_range, not_lt]; omega
      rw [hle_eq, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro k _
      by_cases h : (j : ℕ) < k <;> simp [h]
    have htot1 : ∑ k ∈ Finset.range (d + 1),
        (Nat.choose d k : ℝ) * (1 - a0Param) ^ k * a0Param ^ (d - k) = 1 := by
      calc ∑ k ∈ Finset.range (d + 1), (Nat.choose d k : ℝ) * (1 - a0Param) ^ k * a0Param ^ (d - k)
          = ∑ k ∈ Finset.range (d + 1), (1 - a0Param) ^ k * a0Param ^ (d - k) * (Nat.choose d k : ℝ) :=
            Finset.sum_congr rfl fun k _ => by ring
        _ = 1 := hpow.symm
    unfold binLe
    linarith
  -- Also write (1 - a0Param) * subEnt(G) as permutation average of ∑_j (1 - a0Param) * e_{π, j}
  have hfact_ne : (Nat.factorial d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero d)
  have hHG_avg : (1 - a0Param) * subEnt Ω (unifW Ω) id G
      = (1 / (Nat.factorial d : ℝ)) *
          ∑ π : Equiv.Perm (Fin d),
            ∑ j : Fin d,
              (1 - a0Param) *
                coordCondEnt Ω (unifW Ω) id ((permList gList π)[j]'(by simp [permList, d]))
                  (((permList gList π).take j).toFinset) := by
    have h1 : ∀ π : Equiv.Perm (Fin d),
        ∑ j : Fin d, (1 - a0Param) *
            coordCondEnt Ω (unifW Ω) id ((permList gList π)[j]'(by simp [permList, d]))
              (((permList gList π).take j).toFinset)
        = (1 - a0Param) * subEnt Ω (unifW Ω) id G := by
      intro π; rw [← Finset.mul_sum, ← hchain_full π]
    simp_rw [h1, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
    field_simp [hfact_ne]
  rw [hgH_eq, hHG_avg, ← mul_sub, ← Finset.sum_sub_distrib]
  congr 1; apply Finset.sum_congr rfl; intro π _
  rw [← Finset.sum_sub_distrib]
  have hzero : ∑ j : Fin d, omWeight d j * eStar = 0 := by
    rw [← Finset.sum_mul, sum_omWeight, zero_mul]
  have hrew : ∑ j : Fin d, omWeight d j *
        (coordCondEnt Ω (unifW Ω) id ((permList gList π)[j]'(by simp [permList, d]))
          (((permList gList π).take j).toFinset) - eStar)
      = (∑ j : Fin d, omWeight d j *
          coordCondEnt Ω (unifW Ω) id ((permList gList π)[j]'(by simp [permList, d]))
            (((permList gList π).take j).toFinset))
        - (∑ j : Fin d, omWeight d j * eStar) := by
    rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro j _; ring
  rw [hrew, hzero, sub_zero]
  apply Finset.sum_congr rfl; intro j _
  unfold omWeight; ring

/-! ### Abstract Single-Coordinate ValidPoint & Polytope Objectives -/

/-- All single-coordinate inequalities satisfied by any coordinate `(s, e, t, Rbar, Fbar, U, g, sq)`. -/
structure ValidPoint (s e t Rbar Fbar U_val g_val sq_val : ℝ) : Prop where
  hs_lo : mStar - epsParam ≤ s
  hs_hi : s ≤ 1
  he_lo : 0 ≤ e
  he_hi : e ≤ L
  ht_lo : 0 ≤ t
  ht_hi : t ≤ 1
  hline1 : e ≤ 4 / 5 * t + 27 / 400
  hR_lo : 0 ≤ Rbar
  hR_le_t : Rbar ≤ t
  hB_lo : 0 ≤ s - e / pStar - cParam * t
  hB_hi : s - e / pStar - cParam * t ≤ 1
  hF_lo : 0 ≤ Fbar
  hF_R : 2 * (11 / 200) * t * Rbar ≤ Fbar
  hF_v : 2 * (21 / 100) * t * (e - hr * t) ^ 2 ≤ Fbar
  hF_sim : 2 * (3 / 100) * t * Rbar + 2 * (13 / 100) * t * (e - hr * t) ^ 2 ≤ Fbar
  hU_eq : U_val = Fbar + 2 * s * e - qStar * L * t ^ 2
  hU_bopp : (809 / 500) * s * e ≤ U_val
  hF_le_g : Fbar ≤ g_val
  hsq_lo : (max 0 (-(3 / 50) * e + (685 / 1000) * t - (27 / 100) * Rbar)) ^ 2 ≤ sq_val

/-- Single-coordinate objective on `G` at `(w, ω)`. -/
def PhiG (w om s e t Rbar U_val g_val : ℝ) : ℝ :=
  w * ((bm / pStar) * e + bm * cParam * t - CtotParam * Rbar)
  - DParam * etaParam * e
  - WParam * om * (e - eStar)
  - nu1Param * (w - etaParam)
  - nu2Param * om
  + muUParam * (U_val - e)
  + mugParam * (g_val + 2 * (s - mStar) * e)

/-- Single-coordinate objective on `T`. -/
def PhiT (s e _t _Rbar sq_val U_val g_val : ℝ) : ℝ :=
  sq_val - mStar * e
  + muUParam * (U_val - e)
  + mugParam * (g_val + 2 * (s - mStar) * e)

/-- Bundle of all certified analytic/1D/2D local inequalities needed for the master theorem. -/
structure LocalInequalities : Prop where
  htau0 : 0 < tau
  htau1 : tau < 1 / 2
  hD0 : 0 < DParam
  hD_lt_kappa : DParam < kappaParam
  hR_nonneg : ∀ x, 0 ≤ x → x ≤ 1 → 0 ≤ R_fun x
  hR_le_phi : ∀ x, 0 ≤ x → x ≤ 1 → R_fun x ≤ phi x
  hSigned : ∀ x, 0 ≤ x → x ≤ 1 → 0 ≤ (x - rStar) * h x - (hr / pStar) * v_fun x + R_fun x
  hb_mem : ∀ x, 0 ≤ x → x ≤ 1 → 0 ≤ b_fun x ∧ b_fun x ≤ 1
  hBopp2D : ∀ x y, 0 ≤ x → x ≤ 1 → 0 ≤ y → y ≤ 1 → (809 / 1000) * (y * h x + x * h y) ≤ h (x * y)
  hLine1 : ∀ x, 0 ≤ x → x ≤ 1 → h x ≤ 4 / 5 * phi x + 27 / 400
  hSqrtLB : ∀ x, 0 ≤ x → x ≤ 1 → -(3 / 50) * h x + (685 / 1000) * phi x - (27 / 100) * R_fun x ≤ Real.sqrt (x * h x)
  hF_R : ∀ x y, 0 ≤ x → x ≤ 1 → 0 ≤ y → y ≤ 1 → (11 / 200) * (phi x * R_fun y + phi y * R_fun x) ≤ F_fun x y
  hF_v : ∀ x y, 0 ≤ x → x ≤ 1 → 0 ≤ y → y ≤ 1 → (21 / 100) * (v_fun x ^ 2 * phi y + v_fun y ^ 2 * phi x) ≤ F_fun x y
  hF_sim : ∀ x y, 0 ≤ x → x ≤ 1 → 0 ≤ y → y ≤ 1 →
      (3 / 100) * (phi x * R_fun y + phi y * R_fun x)
      + (13 / 100) * (v_fun x ^ 2 * phi y + v_fun y ^ 2 * phi x) ≤ F_fun x y
  hCov : ∀ {ι : Type} (s : Finset ι) (w Y : ι → ℝ),
      (∀ i ∈ s, 0 ≤ w i) → (∑ i ∈ s, w i = 1) → (∀ i ∈ s, 0 ≤ Y i ∧ Y i ≤ 1) →
      let a := ∑ i ∈ s, w i * Y i
      (∑ i ∈ s, w i * (Y i - a) * h (Y i))
        ≤ kappaParam * (h a - ∑ i ∈ s, w i * h (Y i)) + CcovParam * ∑ i ∈ s, w i * R_fun (Y i)

lemma LocalInequalities.hF_nonneg (loc : LocalInequalities) {x y : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) : 0 ≤ F_fun x y := by
  have h1 := loc.hF_R x y hx0 hx1 hy0 hy1
  have hnn : 0 ≤ (11 / 200 : ℝ) * (phi x * R_fun y + phi y * R_fun x) := by
    have := loc.hR_nonneg x hx0 hx1
    have := loc.hR_nonneg y hy0 hy1
    have := phi_nonneg x; have := phi_nonneg y
    positivity
  linarith

/-- Extract `ValidPoint` for coordinate `k` along any complete nodup ordering `ord` of `Ω`. -/
lemma extract_validPoint {n : ℕ} (Ω : Finset (Fin n → Bool)) (hΩ : Ω.Nonempty)
    (hs_min : ∀ i : Fin n, mStar - epsParam ≤ margProb Ω i)
    (ord : List (Fin n)) (hnd : ord.Nodup) (k : Fin ord.length)
    (loc : LocalInequalities) :
    let S := (ord.take k).toFinset
    let i := ord[k]
    let s := margProb Ω i
    let e := coordCondEnt Ω (unifW Ω) id i S
    let t := ∑ v ∈ Ω, unifW Ω v * phi (Qrv Ω S i v)
    let Rbar := ∑ v ∈ Ω, unifW Ω v * R_fun (Qrv Ω S i v)
    let Fbar := ∑ a ∈ Ω, ∑ b ∈ Ω, unifW Ω a * unifW Ω b * F_fun (Qrv Ω S i a) (Qrv Ω S i b)
    let sq_val := (∑ v ∈ Ω, unifW Ω v * Real.sqrt (Qrv Ω S i v * h (Qrv Ω S i v))) ^ 2
    ValidPoint s e t Rbar Fbar (localU Ω ord k) (localG Ω ord k) sq_val := by
  intro S i s e t Rbar Fbar sq_val
  have hu_nn : ∀ v ∈ Ω, 0 ≤ unifW Ω v := fun v _ => unifW_nonneg Ω v
  have hu_sum : ∑ v ∈ Ω, unifW Ω v = 1 := sum_unifW hΩ
  have he_eq : e = ∑ v ∈ Ω, unifW Ω v * h (Qrv Ω S i v) := coordCondEnt_eq_expect_h Ω S i
  have hs_eq : s = ∑ v ∈ Ω, unifW Ω v * Qrv Ω S i v := (expect_Qrv Ω S i).symm
  have hAvg_le : ∀ f g : ℝ → ℝ, (∀ x, 0 ≤ x → x ≤ 1 → f x ≤ g x) →
      ∑ v ∈ Ω, unifW Ω v * f (Qrv Ω S i v) ≤ ∑ v ∈ Ω, unifW Ω v * g (Qrv Ω S i v) := by
    intro f g hfg
    apply Finset.sum_le_sum; intro v hv
    have hq := Qrv_mem_Icc Ω S i v
    exact mul_le_mul_of_nonneg_left (hfg _ hq.1 hq.2) (hu_nn v hv)
  have hSymProd : ∀ f g : ℝ → ℝ,
      2 * (∑ v ∈ Ω, unifW Ω v * f (Qrv Ω S i v)) * (∑ v ∈ Ω, unifW Ω v * g (Qrv Ω S i v))
      = ∑ a ∈ Ω, ∑ b ∈ Ω, unifW Ω a * unifW Ω b *
          (f (Qrv Ω S i a) * g (Qrv Ω S i b) + f (Qrv Ω S i b) * g (Qrv Ω S i a)) := by
    intro f g
    have h1 : ∀ a ∈ Ω, ∀ b ∈ Ω,
        unifW Ω a * unifW Ω b * (f (Qrv Ω S i a) * g (Qrv Ω S i b) + f (Qrv Ω S i b) * g (Qrv Ω S i a))
        = (unifW Ω a * f (Qrv Ω S i a)) * (unifW Ω b * g (Qrv Ω S i b))
          + (unifW Ω a * g (Qrv Ω S i a)) * (unifW Ω b * f (Qrv Ω S i b)) := fun a _ b _ => by ring
    simp_rw [Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => h1 a ha b hb]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]; ring
  have hB_eq : s - e / pStar - cParam * t = ∑ v ∈ Ω, unifW Ω v * b_fun (Qrv Ω S i v) := by
    rw [hs_eq, he_eq]; unfold b_fun; simp_rw [mul_sub, Finset.sum_sub_distrib]
    congr 1
    · congr 1; rw [Finset.sum_div]; apply Finset.sum_congr rfl; intro v _; ring
    · rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro v _; ring
  have hv_sq : (e - hr * t) ^ 2 ≤ ∑ v ∈ Ω, unifW Ω v * (v_fun (Qrv Ω S i v)) ^ 2 := by
    have hv_eq : e - hr * t = ∑ v ∈ Ω, unifW Ω v * v_fun (Qrv Ω S i v) := by
      rw [he_eq]; unfold v_fun; rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro v _; ring
    rw [hv_eq]
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq Ω
      (fun v => Real.sqrt (unifW Ω v)) (fun v => Real.sqrt (unifW Ω v) * v_fun (Qrv Ω S i v))
    have h1 : ∀ v ∈ Ω, Real.sqrt (unifW Ω v) * (Real.sqrt (unifW Ω v) * v_fun (Qrv Ω S i v))
        = unifW Ω v * v_fun (Qrv Ω S i v) := fun v hv => by rw [← mul_assoc, Real.mul_self_sqrt (hu_nn v hv)]
    have h2 : ∀ v ∈ Ω, Real.sqrt (unifW Ω v) ^ 2 = unifW Ω v := fun v hv => Real.sq_sqrt (hu_nn v hv)
    have h3 : ∀ v ∈ Ω, (Real.sqrt (unifW Ω v) * v_fun (Qrv Ω S i v)) ^ 2
        = unifW Ω v * (v_fun (Qrv Ω S i v)) ^ 2 := fun v hv => by rw [mul_pow, Real.sq_sqrt (hu_nn v hv)]
    rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, Finset.sum_congr rfl h3, hu_sum, one_mul] at hcs
    exact hcs
  have hF_lin : ∀ a b : ℝ,
      (∀ x y, 0 ≤ x → x ≤ 1 → 0 ≤ y → y ≤ 1 →
        a * (phi x * R_fun y + phi y * R_fun x) + b * (v_fun x ^ 2 * phi y + v_fun y ^ 2 * phi x) ≤ F_fun x y) →
      0 ≤ b →
      2 * a * t * Rbar + 2 * b * t * (e - hr * t) ^ 2 ≤ Fbar := by
    intro a b hab hb0
    have hsum : 2 * a * t * Rbar + 2 * b * t * (∑ v ∈ Ω, unifW Ω v * (v_fun (Qrv Ω S i v)) ^ 2) ≤ Fbar := by
      have hlhs : 2 * a * t * Rbar + 2 * b * t * (∑ v ∈ Ω, unifW Ω v * (v_fun (Qrv Ω S i v)) ^ 2)
          = ∑ x ∈ Ω, ∑ y ∈ Ω, unifW Ω x * unifW Ω y *
              (a * (phi (Qrv Ω S i x) * R_fun (Qrv Ω S i y) + phi (Qrv Ω S i y) * R_fun (Qrv Ω S i x))
               + b * (v_fun (Qrv Ω S i x) ^ 2 * phi (Qrv Ω S i y) + v_fun (Qrv Ω S i y) ^ 2 * phi (Qrv Ω S i x))) := by
        have h1 := hSymProd phi R_fun
        have h2 := hSymProd (fun x => v_fun x ^ 2) phi
        have h3 : ∀ x ∈ Ω, ∀ y ∈ Ω,
            unifW Ω x * unifW Ω y *
              (a * (phi (Qrv Ω S i x) * R_fun (Qrv Ω S i y) + phi (Qrv Ω S i y) * R_fun (Qrv Ω S i x))
               + b * (v_fun (Qrv Ω S i x) ^ 2 * phi (Qrv Ω S i y) + v_fun (Qrv Ω S i y) ^ 2 * phi (Qrv Ω S i x)))
            = a * (unifW Ω x * unifW Ω y * (phi (Qrv Ω S i x) * R_fun (Qrv Ω S i y) + phi (Qrv Ω S i y) * R_fun (Qrv Ω S i x)))
              + b * (unifW Ω x * unifW Ω y * (v_fun (Qrv Ω S i x) ^ 2 * phi (Qrv Ω S i y) + v_fun (Qrv Ω S i y) ^ 2 * phi (Qrv Ω S i x))) :=
          fun _ _ _ _ => by ring
        simp_rw [Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => h3 x hx y hy,
                 Finset.sum_add_distrib, ← Finset.mul_sum, ← h1, ← h2]
        ring
      rw [hlhs]
      exact Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun y hy =>
        mul_le_mul_of_nonneg_left
          (hab _ _ (Qrv_mem_Icc Ω S i x).1 (Qrv_mem_Icc Ω S i x).2 (Qrv_mem_Icc Ω S i y).1 (Qrv_mem_Icc Ω S i y).2)
          (mul_nonneg (hu_nn x hx) (hu_nn y hy))
    have ht_nn : 0 ≤ t := Finset.sum_nonneg fun v hv => mul_nonneg (hu_nn v hv) (phi_nonneg _)
    have hmul := mul_le_mul_of_nonneg_left hv_sq (show 0 ≤ 2 * b * t by positivity)
    linarith
  refine
    { hs_lo := hs_min i
      hs_hi := by
        rw [hs_eq]
        calc ∑ v ∈ Ω, unifW Ω v * Qrv Ω S i v
            ≤ ∑ v ∈ Ω, unifW Ω v * 1 := hAvg_le id (fun _ => 1) (fun x _ hx1 => hx1)
          _ = 1 := by simp [hu_sum]
      he_lo := by
        rw [he_eq]
        exact Finset.sum_nonneg fun v hv => mul_nonneg (hu_nn v hv) (h_nonneg (Qrv_mem_Icc Ω S i v).1 (Qrv_mem_Icc Ω S i v).2)
      he_hi := by
        rw [he_eq]
        calc ∑ v ∈ Ω, unifW Ω v * h (Qrv Ω S i v)
            ≤ ∑ v ∈ Ω, unifW Ω v * L := hAvg_le h (fun _ => L) (fun x hx0 hx1 => h_le_L hx0 hx1)
          _ = L := by rw [← Finset.sum_mul, hu_sum, one_mul]
      ht_lo := Finset.sum_nonneg fun v hv => mul_nonneg (hu_nn v hv) (phi_nonneg _)
      ht_hi := by
        calc ∑ v ∈ Ω, unifW Ω v * phi (Qrv Ω S i v)
            ≤ ∑ v ∈ Ω, unifW Ω v * 1 := hAvg_le phi (fun _ => 1) (fun x hx0 hx1 =>
                phi_le_one (le_of_lt loc.htau0) (by linarith [loc.htau1]) hx0 hx1)
          _ = 1 := by simp [hu_sum]
      hline1 := by
        rw [he_eq]
        calc ∑ v ∈ Ω, unifW Ω v * h (Qrv Ω S i v)
            ≤ ∑ v ∈ Ω, unifW Ω v * (4 / 5 * phi (Qrv Ω S i v) + 27 / 400) :=
              hAvg_le h (fun x => 4 / 5 * phi x + 27 / 400) loc.hLine1
          _ = 4 / 5 * t + 27 / 400 := by
              simp_rw [mul_add, Finset.sum_add_distrib, ← mul_assoc, ← Finset.sum_mul, hu_sum, one_mul]
              rw [Finset.mul_sum]; congr 1; apply Finset.sum_congr rfl; intro v _; ring
      hR_lo := Finset.sum_nonneg fun v hv =>
        mul_nonneg (hu_nn v hv) (loc.hR_nonneg _ (Qrv_mem_Icc Ω S i v).1 (Qrv_mem_Icc Ω S i v).2)
      hR_le_t := hAvg_le R_fun phi loc.hR_le_phi
      hB_lo := by
        rw [hB_eq]
        exact Finset.sum_nonneg fun v hv =>
          mul_nonneg (hu_nn v hv) (loc.hb_mem _ (Qrv_mem_Icc Ω S i v).1 (Qrv_mem_Icc Ω S i v).2).1
      hB_hi := by
        rw [hB_eq]
        calc ∑ v ∈ Ω, unifW Ω v * b_fun (Qrv Ω S i v)
            ≤ ∑ v ∈ Ω, unifW Ω v * 1 := hAvg_le b_fun (fun _ => 1) (fun x hx0 hx1 => (loc.hb_mem x hx0 hx1).2)
          _ = 1 := by simp [hu_sum]
      hF_lo := Finset.sum_nonneg fun a ha => Finset.sum_nonneg fun b hb =>
        mul_nonneg (mul_nonneg (hu_nn a ha) (hu_nn b hb))
          (loc.hF_nonneg (Qrv_mem_Icc Ω S i a).1 (Qrv_mem_Icc Ω S i a).2
                         (Qrv_mem_Icc Ω S i b).1 (Qrv_mem_Icc Ω S i b).2)
      hF_R := by
        simpa using hF_lin (11 / 200) 0 (fun x y hx0 hx1 hy0 hy1 => by
          simpa using loc.hF_R x y hx0 hx1 hy0 hy1) le_rfl
      hF_v := by
        simpa using hF_lin 0 (21 / 100) (fun x y hx0 hx1 hy0 hy1 => by
          simpa using loc.hF_v x y hx0 hx1 hy0 hy1) (by norm_num)
      hF_sim := hF_lin (3 / 100) (13 / 100) loc.hF_sim (by norm_num)
      hU_eq := by
        have hEF : Fbar = localU Ω ord k + qStar * L * t ^ 2 - 2 * s * e := by
          dsimp only [Fbar]; unfold F_fun localU
          have h1 : ∀ a ∈ Ω, ∀ b ∈ Ω,
              unifW Ω a * unifW Ω b *
                (h (Qrv Ω S i a * Qrv Ω S i b) + qStar * L * phi (Qrv Ω S i a) * phi (Qrv Ω S i b)
                  - Qrv Ω S i b * h (Qrv Ω S i a) - Qrv Ω S i a * h (Qrv Ω S i b))
              = unifW Ω a * unifW Ω b * h (Qrv Ω S i a * Qrv Ω S i b)
                + qStar * L * ((unifW Ω a * phi (Qrv Ω S i a)) * (unifW Ω b * phi (Qrv Ω S i b)))
                - (unifW Ω a * h (Qrv Ω S i a)) * (unifW Ω b * Qrv Ω S i b)
                - (unifW Ω a * Qrv Ω S i a) * (unifW Ω b * h (Qrv Ω S i b)) := fun _ _ _ _ => by ring
          simp_rw [Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => h1 a ha b hb]
          simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
          have hp2 : ∑ a ∈ Ω, ∑ b ∈ Ω, qStar * L * ((unifW Ω a * phi (Qrv Ω S i a)) * (unifW Ω b * phi (Qrv Ω S i b)))
              = qStar * L * t ^ 2 := by simp_rw [← Finset.mul_sum, ← Finset.sum_mul]; ring
          have hse1 : ∑ a ∈ Ω, ∑ b ∈ Ω, (unifW Ω a * h (Qrv Ω S i a)) * (unifW Ω b * Qrv Ω S i b)
              = e * s := by simp_rw [← Finset.mul_sum, ← Finset.sum_mul, ← hs_eq, ← he_eq]
          have hse2 : ∑ a ∈ Ω, ∑ b ∈ Ω, (unifW Ω a * Qrv Ω S i a) * (unifW Ω b * h (Qrv Ω S i b))
              = s * e := by simp_rw [← Finset.mul_sum, ← Finset.sum_mul, ← hs_eq, ← he_eq]
          rw [hp2, hse1, hse2]; ring
        linarith
      hU_bopp := by
        unfold localU
        have hsym := hSymProd h (fun x => x)
        rw [← he_eq, ← hs_eq] at hsym
        calc (809 / 500 : ℝ) * s * e
            = ∑ a ∈ Ω, ∑ b ∈ Ω, unifW Ω a * unifW Ω b *
                ((809 / 1000) * (Qrv Ω S i b * h (Qrv Ω S i a) + Qrv Ω S i a * h (Qrv Ω S i b))) := by
              have h1 : ∀ a ∈ Ω, ∀ b ∈ Ω,
                  unifW Ω a * unifW Ω b * ((809 / 1000) * (Qrv Ω S i b * h (Qrv Ω S i a) + Qrv Ω S i a * h (Qrv Ω S i b)))
                  = (809 / 1000) * (unifW Ω a * unifW Ω b * (h (Qrv Ω S i a) * Qrv Ω S i b + h (Qrv Ω S i b) * Qrv Ω S i a)) :=
                fun _ _ _ _ => by ring
              simp_rw [Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => h1 a ha b hb,
                       ← Finset.mul_sum, ← hsym]; ring
          _ ≤ ∑ a ∈ Ω, ∑ b ∈ Ω, unifW Ω a * unifW Ω b * h (Qrv Ω S i a * Qrv Ω S i b) :=
              Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun b hb =>
                mul_le_mul_of_nonneg_left
                  (loc.hBopp2D _ _ (Qrv_mem_Icc Ω S i a).1 (Qrv_mem_Icc Ω S i a).2
                                   (Qrv_mem_Icc Ω S i b).1 (Qrv_mem_Icc Ω S i b).2)
                  (mul_nonneg (hu_nn a ha) (hu_nn b hb))
      hF_le_g := by
        have hdecomp := localG_decomposition Ω hΩ ord hnd k
        dsimp only at hdecomp
        have hpref_nn : ∀ σ x, 0 ≤ prefWeight Ω ord σ k x := fun σ x => by
          unfold prefWeight; apply Finset.prod_nonneg; intro j _; split_ifs
          · exact stepFactor_nonneg Ω ord (le_of_lt loc.htau0) (by linarith [loc.htau1]) j (σ j) x
          · norm_num
        have h1 : 0 ≤ qStar * (∑ σ : Fin ord.length → Bool,
            ∑ x ∈ Ω.image (restrictVec S), ∑ y ∈ Ω.image (restrictVec S),
              (1 / (2 : ℝ) ^ ord.length) * prefWeight Ω ord σ k x * prefWeight Ω ord σ k y
                * J_fun (condProb Ω S i x) (condProb Ω S i y)) := by
          apply mul_nonneg (le_of_lt qStar_pos)
          apply Finset.sum_nonneg; intro σ _; apply Finset.sum_nonneg; intro x _; apply Finset.sum_nonneg; intro y _
          exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (hpref_nn σ x)) (hpref_nn σ y))
            (J_fun_nonneg_of_tau loc.htau0 loc.htau1
              (condProb_nonneg _ _ _ _) (condProb_le_one _ _ _ _)
              (condProb_nonneg _ _ _ _) (condProb_le_one _ _ _ _))
        have h2 : 0 ≤ qStar * L * (∑ σ : Fin ord.length → Bool, (1 / (2 : ℝ) ^ ord.length) *
            ((∑ x ∈ Ω.image (restrictVec S), prefWeight Ω ord σ k x * phi (condProb Ω S i x)) - t) ^ 2) :=
          mul_nonneg (mul_nonneg (le_of_lt qStar_pos) (le_of_lt L_pos))
            (Finset.sum_nonneg fun σ _ => mul_nonneg (by positivity) (sq_nonneg _))
        change Fbar ≤ localG Ω ord k
        linarith
      hsq_lo := by
        have hlin : -(3 / 50) * e + (685 / 1000) * t - (27 / 100) * Rbar
            ≤ ∑ v ∈ Ω, unifW Ω v * Real.sqrt (Qrv Ω S i v * h (Qrv Ω S i v)) := by
          have h1 : -(3 / 50) * e + (685 / 1000) * t - (27 / 100) * Rbar
              = ∑ v ∈ Ω, unifW Ω v * (-(3 / 50) * h (Qrv Ω S i v) + (685 / 1000) * phi (Qrv Ω S i v) - (27 / 100) * R_fun (Qrv Ω S i v)) := by
            rw [he_eq]; simp_rw [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
            congr 1
            · congr 1
              · rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro v _; ring
              · rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro v _; ring
            · rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro v _; ring
          rw [h1]
          exact hAvg_le (fun x => -(3 / 50) * h x + (685 / 1000) * phi x - (27 / 100) * R_fun x)
            (fun x => Real.sqrt (x * h x)) loc.hSqrtLB
        have hnn : 0 ≤ ∑ v ∈ Ω, unifW Ω v * Real.sqrt (Qrv Ω S i v * h (Qrv Ω S i v)) :=
          Finset.sum_nonneg fun v hv => mul_nonneg (hu_nn v hv) (Real.sqrt_nonneg _)
        exact pow_le_pow_left₀ (le_max_left 0 _) (max_le hnn hlin) 2 }

/-! ### Master Reduction Theorem (`master_contradiction`) -/

/-- When `e = 0` for a valid point, `PhiT ≥ 0` holds trivially. -/
lemma PhiT_nonneg_of_e_zero {s e t Rbar Fbar U_val g_val sq_val : ℝ}
    (hv : ValidPoint s e t Rbar Fbar U_val g_val sq_val) (he0 : e = 0) :
    0 ≤ PhiT s e t Rbar sq_val U_val g_val := by
  unfold PhiT
  rw [he0]
  have hsq : 0 ≤ sq_val := le_trans (sq_nonneg _) hv.hsq_lo
  have hU : 0 ≤ U_val := by
    have := hv.hU_bopp; rw [he0, mul_zero] at this; exact this
  have hg : 0 ≤ g_val := le_trans hv.hF_lo hv.hF_le_g
  have hmuU : 0 ≤ muUParam := muUParam_nonneg
  have hmug : 0 ≤ mugParam := mugParam_nonneg
  nlinarith

set_option maxHeartbeats 800000 in
/-- Helper: conditional fibre lower bound for a coordinate `i` with `S ⊆ P`.
    Combines the signed pointwise inequality and the covariance bound on each `A_S`-fibre! -/
lemma fibre_term_lower_bound {n : ℕ} (Ω : Finset (Fin n → Bool)) (_hΩ : Ω.Nonempty)
    {S P : Finset (Fin n)} (hSP : S ⊆ P) (i : Fin n) (loc : LocalInequalities) :
    let e := coordCondEnt Ω (unifW Ω) id i P
    let t := ∑ v ∈ Ω, unifW Ω v * phi (Qrv Ω P i v)
    let Rbar := ∑ v ∈ Ω, unifW Ω v * R_fun (Qrv Ω P i v)
    (bm / pStar) * e + bm * cParam * t - CtotParam * Rbar
      - DParam * e - kappaParam * (coordCondEnt Ω (unifW Ω) id i S - e)
    ≤ ∑ v ∈ Ω, unifW Ω v * (Qrv Ω S i v - mStar) * h (Qrv Ω P i v) := by
  intro e t Rbar
  -- Split LHS: E[(p - mStar) h(Q)] = E[(Q - mStar) h(Q)] - E[(Q - p) h(Q)]
  have hsplit : ∑ v ∈ Ω, unifW Ω v * (Qrv Ω S i v - mStar) * h (Qrv Ω P i v)
      = (∑ v ∈ Ω, unifW Ω v * (Qrv Ω P i v - mStar) * h (Qrv Ω P i v))
        - (∑ v ∈ Ω, unifW Ω v * (Qrv Ω P i v - Qrv Ω S i v) * h (Qrv Ω P i v)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro v _; ring
  rw [hsplit]
  -- Bound 1: E[(Q - mStar) h(Q)] ≥ -DParam * e + (bm / pStar) * e + bm * cParam * t - Rbar
  have hb1 : -DParam * e + (bm / pStar) * e + bm * cParam * t - Rbar
      ≤ ∑ v ∈ Ω, unifW Ω v * (Qrv Ω P i v - mStar) * h (Qrv Ω P i v) := by
    have hpt : ∀ x : ℝ, 0 ≤ x → x ≤ 1 →
        -DParam * h x + (bm / pStar) * h x + bm * cParam * phi x - R_fun x ≤ (x - mStar) * h x := by
      intro x hx0 hx1
      have hsig := loc.hSigned x hx0 hx1
      have hid := signed_pointwise_identity x
      have hbdef : x - b_fun x = h x / pStar + cParam * phi x := by unfold b_fun; ring
      have hbm : bm * x - bm * b_fun x = (bm / pStar) * h x + bm * cParam * phi x := by
        calc bm * x - bm * b_fun x = bm * (x - b_fun x) := by ring
          _ = bm * (h x / pStar + cParam * phi x) := by rw [hbdef]
          _ = (bm / pStar) * h x + bm * cParam * phi x := by ring
      linarith
    have he_eq : e = ∑ v ∈ Ω, unifW Ω v * h (Qrv Ω P i v) := coordCondEnt_eq_expect_h Ω P i
    have hLHS : -DParam * e + (bm / pStar) * e + bm * cParam * t - Rbar
        = ∑ v ∈ Ω, unifW Ω v * (-DParam * h (Qrv Ω P i v) + (bm / pStar) * h (Qrv Ω P i v)
            + bm * cParam * phi (Qrv Ω P i v) - R_fun (Qrv Ω P i v)) := by
      rw [he_eq]; simp_rw [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
      congr 1
      · congr 1
        · congr 1
          · rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro v _; ring
          · rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro v _; ring
        · rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro v _; ring
    rw [hLHS]
    apply Finset.sum_le_sum; intro v _
    have hq := Qrv_mem_Icc Ω P i v
    have hmul := mul_le_mul_of_nonneg_left (hpt _ hq.1 hq.2) (unifW_nonneg Ω v)
    linarith
  -- Bound 2: E[(Q - p) h(Q)] ≤ kappaParam * (H(A_i | A_S) - e) + CcovParam * Rbar
  have hb2 : ∑ v ∈ Ω, unifW Ω v * (Qrv Ω P i v - Qrv Ω S i v) * h (Qrv Ω P i v)
      ≤ kappaParam * (coordCondEnt Ω (unifW Ω) id i S - e) + CcovParam * Rbar := by
    -- Partition Ω by y = restrictVec S v ∈ Ω.image (restrictVec S)
    set Y := Ω.image (restrictVec S)
    rw [← Finset.sum_fiberwise_of_maps_to (g := restrictVec S) (t := Y)
          (fun v hv => Finset.mem_image_of_mem _ hv)]
    have hRHS_fib : kappaParam * (coordCondEnt Ω (unifW Ω) id i S - e) + CcovParam * Rbar
        = ∑ y ∈ Y, fibreProb Ω S y *
            (kappaParam * (h (condProb Ω S i y)
              - ∑ v ∈ Ω.filter (fun v => restrictVec S v = y), (unifW Ω v / fibreProb Ω S y) * h (Qrv Ω P i v))
            + CcovParam * (∑ v ∈ Ω.filter (fun v => restrictVec S v = y),
                (unifW Ω v / fibreProb Ω S y) * R_fun (Qrv Ω P i v))) := by
      have hterm : ∀ y ∈ Y,
          fibreProb Ω S y *
            (kappaParam * (h (condProb Ω S i y)
              - ∑ v ∈ Ω.filter (fun v => restrictVec S v = y), (unifW Ω v / fibreProb Ω S y) * h (Qrv Ω P i v))
            + CcovParam * (∑ v ∈ Ω.filter (fun v => restrictVec S v = y),
                (unifW Ω v / fibreProb Ω S y) * R_fun (Qrv Ω P i v)))
          = kappaParam * (fibreProb Ω S y * h (condProb Ω S i y)
              - ∑ v ∈ Ω.filter (fun v => restrictVec S v = y), unifW Ω v * h (Qrv Ω P i v))
            + CcovParam * (∑ v ∈ Ω.filter (fun v => restrictVec S v = y), unifW Ω v * R_fun (Qrv Ω P i v)) := by
        intro y hy
        have hpos := ne_of_gt (fibreProb_pos_of_mem_image Ω S hy)
        have hc1 : fibreProb Ω S y * (∑ v ∈ Ω.filter (fun v => restrictVec S v = y),
              (unifW Ω v / fibreProb Ω S y) * h (Qrv Ω P i v))
            = ∑ v ∈ Ω.filter (fun v => restrictVec S v = y), unifW Ω v * h (Qrv Ω P i v) := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro v _; field_simp [hpos]
        have hc2 : fibreProb Ω S y * (∑ v ∈ Ω.filter (fun v => restrictVec S v = y),
              (unifW Ω v / fibreProb Ω S y) * R_fun (Qrv Ω P i v))
            = ∑ v ∈ Ω.filter (fun v => restrictVec S v = y), unifW Ω v * R_fun (Qrv Ω P i v) := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro v _; field_simp [hpos]
        linear_combination -kappaParam * hc1 + CcovParam * hc2
      rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
          Finset.sum_sub_distrib]
      have hS_ent : ∑ y ∈ Y, fibreProb Ω S y * h (condProb Ω S i y) = coordCondEnt Ω (unifW Ω) id i S := by
        rw [coordCondEnt_eq_expect_h]; exact (expect_comp_restrictVec Ω S (fun y => h (condProb Ω S i y))).symm
      have he_fib : ∑ y ∈ Y, ∑ v ∈ Ω.filter (fun v => restrictVec S v = y), unifW Ω v * h (Qrv Ω P i v) = e := by
        rw [Finset.sum_fiberwise_of_maps_to (g := restrictVec S) (t := Y)
              (fun v hv => Finset.mem_image_of_mem _ hv), ← coordCondEnt_eq_expect_h]
      have hR_fib : ∑ y ∈ Y, ∑ v ∈ Ω.filter (fun v => restrictVec S v = y), unifW Ω v * R_fun (Qrv Ω P i v) = Rbar :=
        Finset.sum_fiberwise_of_maps_to (g := restrictVec S) (t := Y) (fun v hv => Finset.mem_image_of_mem _ hv) _
      rw [hS_ent, he_fib, hR_fib]
    rw [hRHS_fib]
    apply Finset.sum_le_sum; intro y hy
    have hpy_pos : 0 < fibreProb Ω S y := fibreProb_pos_of_mem_image Ω S hy
    set Ωy := Ω.filter (fun v => restrictVec S v = y)
    let wy : (Fin n → Bool) → ℝ := fun v => unifW Ω v / fibreProb Ω S y
    have hwy_nn : ∀ v ∈ Ωy, 0 ≤ wy v := fun v _ => div_nonneg (unifW_nonneg Ω v) (le_of_lt hpy_pos)
    have hwy_sum : ∑ v ∈ Ωy, wy v = 1 := by
      simp only [wy, ← Finset.sum_div]
      exact div_self (ne_of_gt hpy_pos)
    have hwy_mean : ∑ v ∈ Ωy, wy v * Qrv Ω P i v = condProb Ω S i y := by
      have h1 : ∑ v ∈ Ωy, wy v * Qrv Ω P i v
          = (∑ v ∈ Ωy, unifW Ω v * Qrv Ω P i v) / fibreProb Ω S y := by
        rw [Finset.sum_div]; apply Finset.sum_congr rfl; intro v _; simp only [wy]; ring
      rw [h1, sum_fibre_Qrv Ω hSP i y, mul_div_cancel_left₀ _ (ne_of_gt hpy_pos)]
    have hY_mem : ∀ v ∈ Ωy, 0 ≤ Qrv Ω P i v ∧ Qrv Ω P i v ≤ 1 := fun v _ => Qrv_mem_Icc Ω P i v
    have hcov := loc.hCov Ωy wy (fun v => Qrv Ω P i v) hwy_nn hwy_sum hY_mem
    dsimp only at hcov
    rw [hwy_mean] at hcov
    have hmul := mul_le_mul_of_nonneg_left hcov (le_of_lt hpy_pos)
    have hLHS_y : fibreProb Ω S y * ∑ v ∈ Ωy, wy v * (Qrv Ω P i v - condProb Ω S i y) * h (Qrv Ω P i v)
        = ∑ v ∈ Ωy, unifW Ω v * (Qrv Ω P i v - Qrv Ω S i v) * h (Qrv Ω P i v) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro v hv
      have hvy : restrictVec S v = y := (Finset.mem_filter.mp hv).2
      have hQS : Qrv Ω S i v = condProb Ω S i y := by unfold Qrv; rw [hvy]
      rw [hQS]; simp only [wy]; field_simp [ne_of_gt hpy_pos]
    rw [hLHS_y] at hmul
    exact hmul
  unfold CtotParam
  linarith

set_option maxHeartbeats 1600000 in
/-- **Master Reduction Theorem**:
    If `LocalInequalities` holds and `PhiG > 0` at the 3 vertices `(0, a0), (1, a0), (1, a0 - 1)`
    for all `ValidPoint` with `e ≥ zParam`, and `PhiT > 0` for all `ValidPoint` with `0 < e ≤ zParam`,
    then NO `AndClosed` family `Ω ⊆ (Fin n → Bool)` with `2 ≤ Ω.card` can have every coordinate
    marginal `≥ mStar - epsParam`! -/
theorem master_contradiction {n : ℕ} (Ω : Finset (Fin n → Bool)) (hΩ2 : 2 ≤ Ω.card)
    (hAC : AndClosed Ω) (hs_min : ∀ i : Fin n, mStar - epsParam ≤ margProb Ω i)
    (loc : LocalInequalities)
    (hPolyG : ∀ wv omv, (wv = 0 ∧ omv = a0Param) ∨ (wv = 1 ∧ omv = a0Param) ∨ (wv = 1 ∧ omv = a0Param - 1) →
      ∀ s e t Rbar Fbar U_val g_val sq_val,
        ValidPoint s e t Rbar Fbar U_val g_val sq_val → zParam ≤ e →
        0 < PhiG wv omv s e t Rbar U_val g_val)
    (hPolyT : ∀ s e t Rbar Fbar U_val g_val sq_val,
      ValidPoint s e t Rbar Fbar U_val g_val sq_val → 0 < e → e ≤ zParam →
      0 < PhiT s e t Rbar sq_val U_val g_val) :
    False := by
  have hΩ : Ω.Nonempty := Finset.card_pos.mp (by omega)
  have hH_pos : 0 < Real.log Ω.card := Real.log_pos (by exact_mod_cast (show 1 < Ω.card by omega))
  -- Step 1: Peel coordinates into (G, ordT)
  rcases peel_coords Ω zParam with ⟨G, ordT, hndT, hdisjT, hcovGT, hG_ent, hT_ent⟩
  -- Case split on G = ∅ vs G.Nonempty!
  by_cases hG_empty : G = ∅
  · -- Case d = 0: ordT is a complete ordering of Fin n, every coordinate has e_k < zParam!
    subst hG_empty
    simp only [Finset.empty_union] at hcovGT hT_ent
    have hfib := fibre_inequality Ω hΩ hAC ∅ ordT hndT (by simp) (by simp [hcovGT])
      loc.htau0 loc.htau1 (fun x y hx0 hx1 hy0 hy1 => loc.hF_nonneg hx0 hx1 hy0 hy1)
    have hU := independent_protocol_bound Ω hΩ hAC ordT hndT hcovGT
    have hgb := global_budget_bound Ω hΩ hAC ordT hndT hcovGT (le_of_lt loc.htau0) (by linarith [loc.htau1])
    have hH := log_card_eq_sum_coordCondEnt Ω hΩ ordT hndT hcovGT
    -- Combine: ∑_k (E[(p_k - mStar) h(Q_k)] + muU*(U_k - e_k) + mug*(g_k + 2(s_k - mStar)e_k)) ≤ 0!
    have hsum_le : ∑ k : Fin ordT.length,
        PhiT (margProb Ω (ordT[k]))
          (coordCondEnt Ω (unifW Ω) id (ordT[k]) ((ordT.take k).toFinset))
          (∑ v ∈ Ω, unifW Ω v * phi (Qrv Ω ((ordT.take k).toFinset) (ordT[k]) v))
          (∑ v ∈ Ω, unifW Ω v * R_fun (Qrv Ω ((ordT.take k).toFinset) (ordT[k]) v))
          ((∑ v ∈ Ω, unifW Ω v * Real.sqrt (Qrv Ω ((ordT.take k).toFinset) (ordT[k]) v
              * h (Qrv Ω ((ordT.take k).toFinset) (ordT[k]) v))) ^ 2)
          (localU Ω ordT k) (localG Ω ordT k) ≤ 0 := by
      have hcs_sum : ∑ k : Fin ordT.length,
          (((∑ v ∈ Ω, unifW Ω v * Real.sqrt (Qrv Ω ((ordT.take k).toFinset) (ordT[k]) v
              * h (Qrv Ω ((ordT.take k).toFinset) (ordT[k]) v))) ^ 2)
            - mStar * coordCondEnt Ω (unifW Ω) id (ordT[k]) ((ordT.take k).toFinset)) ≤ 0 := by
        calc ∑ k : Fin ordT.length, _
            ≤ ∑ k : Fin ordT.length,
                ∑ v ∈ Ω, unifW Ω v * (Qrv Ω ∅ (ordT[k]) v - mStar)
                  * h (Qrv Ω (∅ ∪ (ordT.take k).toFinset) (ordT[k]) v) := by
              apply Finset.sum_le_sum; intro k _
              have hcs := cauchy_schwarz_fibre Ω hΩ (Finset.empty_subset ((ordT.take k).toFinset)) (ordT[k])
              have he := coordCondEnt_eq_expect_h Ω ((ordT.take k).toFinset) (ordT[k])
              simp only [Finset.empty_union]
              have hsub : ∑ v ∈ Ω, unifW Ω v * (Qrv Ω ∅ (ordT[k]) v - mStar)
                    * h (Qrv Ω ((ordT.take k).toFinset) (ordT[k]) v)
                  = (∑ v ∈ Ω, unifW Ω v * Qrv Ω ∅ (ordT[k]) v * h (Qrv Ω ((ordT.take k).toFinset) (ordT[k]) v))
                    - mStar * (∑ v ∈ Ω, unifW Ω v * h (Qrv Ω ((ordT.take k).toFinset) (ordT[k]) v)) := by
                rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
                apply Finset.sum_congr rfl; intro v _; ring
              rw [hsub, ← he]; linarith
          _ ≤ 0 := hfib
      have hU_sum : ∑ k : Fin ordT.length,
          (localU Ω ordT k - coordCondEnt Ω (unifW Ω) id (ordT[k]) ((ordT.take k).toFinset)) ≤ 0 := by
        rw [Finset.sum_sub_distrib, ← hH]; exact sub_nonpos.mpr hU
      have hG_sum : ∑ k : Fin ordT.length,
          (localG Ω ordT k + 2 * (margProb Ω (ordT[k]) - mStar)
            * coordCondEnt Ω (unifW Ω) id (ordT[k]) ((ordT.take k).toFinset)) ≤ 0 := by
        have h2 : ∑ k : Fin ordT.length,
              2 * (margProb Ω (ordT[k]) - mStar)
                * coordCondEnt Ω (unifW Ω) id (ordT[k]) ((ordT.take k).toFinset)
            = 2 * ∑ k : Fin ordT.length,
                (margProb Ω (ordT[k]) - mStar)
                  * coordCondEnt Ω (unifW Ω) id (ordT[k]) ((ordT.take k).toFinset) := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring
        rw [Finset.sum_add_distrib, h2]; exact hgb
      unfold PhiT
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      have hmuU := muUParam_nonneg
      have hmug := mugParam_nonneg
      nlinarith
    -- On the other hand, every term is ≥ 0, and since ∑ e_k = log |Ω| > 0, some term has e_k > 0 hence > 0!
    have hex_pos : ∃ k : Fin ordT.length,
        0 < coordCondEnt Ω (unifW Ω) id (ordT[k]) ((ordT.take k).toFinset) := by
      by_contra hall
      push Not at hall
      have hle0 : ∑ k : Fin ordT.length, coordCondEnt Ω (unifW Ω) id (ordT[k]) ((ordT.take k).toFinset) ≤ 0 :=
        Finset.sum_nonpos fun k _ => hall k
      linarith
    rcases hex_pos with ⟨k0, hk0_pos⟩
    have hall_nn : ∀ k ∈ (Finset.univ : Finset (Fin ordT.length)),
        0 ≤ PhiT (margProb Ω (ordT[k]))
          (coordCondEnt Ω (unifW Ω) id (ordT[k]) ((ordT.take k).toFinset))
          (∑ v ∈ Ω, unifW Ω v * phi (Qrv Ω ((ordT.take k).toFinset) (ordT[k]) v))
          (∑ v ∈ Ω, unifW Ω v * R_fun (Qrv Ω ((ordT.take k).toFinset) (ordT[k]) v))
          ((∑ v ∈ Ω, unifW Ω v * Real.sqrt (Qrv Ω ((ordT.take k).toFinset) (ordT[k]) v
              * h (Qrv Ω ((ordT.take k).toFinset) (ordT[k]) v))) ^ 2)
          (localU Ω ordT k) (localG Ω ordT k) := by
      intro k _
      have hvp := extract_validPoint Ω hΩ hs_min ordT hndT k loc
      rcases hvp.he_lo.eq_or_lt with he0 | he_pos
      · exact PhiT_nonneg_of_e_zero hvp he0.symm
      · exact le_of_lt (hPolyT _ _ _ _ _ _ _ _ hvp he_pos (le_of_lt (hT_ent k)))
    have hk0_strict : 0 < PhiT (margProb Ω (ordT[k0]))
          (coordCondEnt Ω (unifW Ω) id (ordT[k0]) ((ordT.take k0).toFinset))
          (∑ v ∈ Ω, unifW Ω v * phi (Qrv Ω ((ordT.take k0).toFinset) (ordT[k0]) v))
          (∑ v ∈ Ω, unifW Ω v * R_fun (Qrv Ω ((ordT.take k0).toFinset) (ordT[k0]) v))
          ((∑ v ∈ Ω, unifW Ω v * Real.sqrt (Qrv Ω ((ordT.take k0).toFinset) (ordT[k0]) v
              * h (Qrv Ω ((ordT.take k0).toFinset) (ordT[k0]) v))) ^ 2)
          (localU Ω ordT k0) (localG Ω ordT k0) :=
      hPolyT _ _ _ _ _ _ _ _ (extract_validPoint Ω hΩ hs_min ordT hndT k0 loc)
        hk0_pos (le_of_lt (hT_ent k0))
    have hsum_pos : 0 < ∑ k : Fin ordT.length,
        PhiT (margProb Ω (ordT[k]))
          (coordCondEnt Ω (unifW Ω) id (ordT[k]) ((ordT.take k).toFinset))
          (∑ v ∈ Ω, unifW Ω v * phi (Qrv Ω ((ordT.take k).toFinset) (ordT[k]) v))
          (∑ v ∈ Ω, unifW Ω v * R_fun (Qrv Ω ((ordT.take k).toFinset) (ordT[k]) v))
          ((∑ v ∈ Ω, unifW Ω v * Real.sqrt (Qrv Ω ((ordT.take k).toFinset) (ordT[k]) v
              * h (Qrv Ω ((ordT.take k).toFinset) (ordT[k]) v))) ^ 2)
          (localU Ω ordT k) (localG Ω ordT k) :=
      Finset.sum_pos' hall_nn ⟨k0, Finset.mem_univ _, hk0_strict⟩
    linarith
  · -- Case d ≥ 1 (G.Nonempty)!
    have hG_ne : G.Nonempty := Finset.nonempty_iff_ne_empty.mpr hG_empty
    let gList : List (Fin n) := G.toList
    have hndG : gList.Nodup := Finset.nodup_toList G
    have hcovG : gList.toFinset = G := Finset.toList_toFinset G
    set d := gList.length
    have hd_pos : 0 < d := by
      have : G.card = d := by rw [← hcovG, List.toFinset_card_of_nodup hndG]
      rw [← this]; exact hG_ne.card_pos
    have hfact_pos : (0 : ℝ) < Nat.factorial d := Nat.cast_pos.mpr (Nat.factorial_pos d)
    have hfact_ne : (Nat.factorial d : ℝ) ≠ 0 := ne_of_gt hfact_pos
    -- For each permutation π : Equiv.Perm (Fin d), form complete compatible order ord_π := permList gList π ++ ordT!
    let ordP : Equiv.Perm (Fin d) → List (Fin n) := fun π => permList gList π ++ ordT
    have hordP_len : ∀ π, (ordP π).length = d + ordT.length := fun π => by simp [ordP, permList, d]
    have hordP_nd : ∀ π, (ordP π).Nodup := fun π => by
      rw [List.nodup_append]
      refine ⟨permList_nodup hndG π, hndT, ?_⟩
      intro a ha b hb hab; subst hab
      have haG : a ∈ G := by rw [← hcovG, ← permList_toFinset gList π, List.mem_toFinset]; exact ha
      exact hdisjT a hb haG
    have hordP_cov : ∀ π, (ordP π).toFinset = Finset.univ := fun π => by
      simp [ordP, List.toFinset_append, permList_toFinset, hcovG, hcovGT]
    -- Helpers to index into G-part (j : Fin d) and T-part (l : Fin ordT.length) of ordP π:
    let idxG (π : Equiv.Perm (Fin d)) (j : Fin d) : Fin (ordP π).length :=
      ⟨j.1, by rw [hordP_len]; omega⟩
    let idxT (π : Equiv.Perm (Fin d)) (l : Fin ordT.length) : Fin (ordP π).length :=
      ⟨d + l.1, by rw [hordP_len]; omega⟩
    have hgetG : ∀ π (j : Fin d), (ordP π)[idxG π j] = (permList gList π)[j]'(by simp [permList, d]) := by
      intro π j
      simp only [ordP, idxG, Fin.getElem_fin]
      exact List.getElem_append_left (by rw [permList_length]; exact j.isLt)
    have htakeG : ∀ π (j : Fin d), ((ordP π).take (idxG π j)).toFinset = ((permList gList π).take j).toFinset := by
      intro π j
      change ((permList gList π ++ ordT).take j.1).toFinset = _
      rw [List.take_append_of_le_length (by rw [permList_length]; exact le_of_lt j.isLt)]
    have hgetT : ∀ π (l : Fin ordT.length), (ordP π)[idxT π l] = ordT[l] := by
      intro π l
      have hlen : (permList gList π).length = d := permList_length gList π
      simp [ordP, idxT, List.getElem_append_right (by omega : (permList gList π).length ≤ d + l.1), hlen]
    have htakeT : ∀ π (l : Fin ordT.length), ((ordP π).take (idxT π l)).toFinset = G ∪ (ordT.take l).toFinset := by
      intro π l
      have hlen : (permList gList π).length = d := permList_length gList π
      have htk : (permList gList π).take (d + l.1) = permList gList π :=
        List.take_of_length_le (by omega)
      simp only [ordP, idxT, List.take_append, hlen, htk, Nat.add_sub_cancel_left,
        List.toFinset_append, permList_toFinset, hcovG]
    -- STEP A: For EVERY π and EVERY k ∈ {0, ..., d}, apply fibre_inequality to S = take_k(π), ordR = drop_k(π) ++ ordT!
    have hfib_k : ∀ (π : Equiv.Perm (Fin d)) (k : ℕ), k ≤ d →
        (∑ j : Fin d, if k ≤ (j : ℕ) then
            ((bm / pStar) * coordCondEnt Ω (unifW Ω) id ((ordP π)[idxG π j]) (((ordP π).take (idxG π j)).toFinset)
            + bm * cParam * (∑ v ∈ Ω, unifW Ω v * phi (Qrv Ω (((ordP π).take (idxG π j)).toFinset) ((ordP π)[idxG π j]) v))
            - CtotParam * (∑ v ∈ Ω, unifW Ω v * R_fun (Qrv Ω (((ordP π).take (idxG π j)).toFinset) ((ordP π)[idxG π j]) v)))
          else 0)
        - DParam * (subEnt Ω (unifW Ω) id G - subEnt Ω (unifW Ω) id (((permList gList π).take k).toFinset))
        - kappaParam * totalCorr Ω (unifW Ω) id G (((permList gList π).take k).toFinset)
        + ∑ l : Fin ordT.length,
            (((∑ v ∈ Ω, unifW Ω v * Real.sqrt (Qrv Ω (G ∪ (ordT.take l).toFinset) (ordT[l]) v
                * h (Qrv Ω (G ∪ (ordT.take l).toFinset) (ordT[l]) v))) ^ 2)
             - mStar * coordCondEnt Ω (unifW Ω) id (ordT[l]) (G ∪ (ordT.take l).toFinset))
        ≤ 0 := by
      intro π k hk
      set pL := permList gList π
      set S := (pL.take k).toFinset
      set ordR := pL.drop k ++ ordT
      have hnd_pL : pL.Nodup := permList_nodup hndG π
      have hlen_pL : pL.length = d := permList_length gList π
      have htake_drop : pL.take k ++ pL.drop k = pL := List.take_append_drop k pL
      have hnd_take_drop : (pL.take k).Nodup ∧ (pL.drop k).Nodup ∧ ∀ a ∈ pL.take k, ∀ b ∈ pL.drop k, a ≠ b := by
        have := hnd_pL; rw [← htake_drop, List.nodup_append] at this; exact this
      have hndR : ordR.Nodup := by
        rw [List.nodup_append]
        refine ⟨hnd_take_drop.2.1, hndT, ?_⟩
        intro a ha b hb hab; subst hab
        have haG : a ∈ G := by
          rw [← hcovG, ← permList_toFinset gList π, List.mem_toFinset]
          exact List.mem_of_mem_drop ha
        exact hdisjT a hb haG
      have hdisjR : ∀ i ∈ ordR, i ∉ S := by
        intro i hi hiS
        rw [List.mem_toFinset] at hiS
        rcases List.mem_append.mp hi with h1 | h2
        · exact hnd_take_drop.2.2 i hiS i h1 rfl
        · have hiG : i ∈ G := by
            rw [← hcovG, ← permList_toFinset gList π, List.mem_toFinset]
            exact List.mem_of_mem_take hiS
          exact hdisjT i h2 hiG
      have hcovR : S ∪ ordR.toFinset = Finset.univ := by
        have : S ∪ (pL.drop k).toFinset = G := by
          rw [← List.toFinset_append, htake_drop, permList_toFinset, hcovG]
        simp only [ordR, List.toFinset_append, ← Finset.union_assoc, this, hcovGT]
      have hfi := fibre_inequality Ω hΩ hAC S ordR hndR hdisjR hcovR
        loc.htau0 loc.htau1 (fun x y hx0 hx1 hy0 hy1 => loc.hF_nonneg hx0 hx1 hy0 hy1)
      -- Split hfi into (pL.drop k) part and ordT part!
      have hlen_drop : (pL.drop k).length = d - k := by simp [hlen_pL]
      have hlen_ordR : ordR.length = (d - k) + ordT.length := by simp [ordR, hlen_drop]
      rw [← (finCongr hlen_ordR.symm).sum_comp, Fin.sum_univ_add] at hfi
      -- Lower-bound T-part by Cauchy–Schwarz:
      have hT_lb : ∑ l : Fin ordT.length,
            (((∑ v ∈ Ω, unifW Ω v * Real.sqrt (Qrv Ω (G ∪ (ordT.take l).toFinset) (ordT[l]) v
                * h (Qrv Ω (G ∪ (ordT.take l).toFinset) (ordT[l]) v))) ^ 2)
             - mStar * coordCondEnt Ω (unifW Ω) id (ordT[l]) (G ∪ (ordT.take l).toFinset))
          ≤ ∑ l : Fin ordT.length,
              ∑ v ∈ Ω, unifW Ω v * (Qrv Ω S (ordR[(finCongr hlen_ordR.symm) (Fin.natAdd (d - k) l)]) v - mStar)
                * h (Qrv Ω (S ∪ (ordR.take ((finCongr hlen_ordR.symm) (Fin.natAdd (d - k) l))).toFinset)
                      (ordR[(finCongr hlen_ordR.symm) (Fin.natAdd (d - k) l)]) v) := by
        apply Finset.sum_le_sum; intro l _
        have hget : ordR[(finCongr hlen_ordR.symm) (Fin.natAdd (d - k) l)] = ordT[l] := by
          simp [ordR, List.getElem_append_right (by omega : (pL.drop k).length ≤ d - k + l.1), hlen_drop]
        have hpref : S ∪ (ordR.take ((finCongr hlen_ordR.symm) (Fin.natAdd (d - k) l))).toFinset
            = G ∪ (ordT.take l).toFinset := by
          have h1 : S ∪ (pL.drop k).toFinset = G := by
            rw [← List.toFinset_append, htake_drop, permList_toFinset, hcovG]
          have htk : (pL.drop k).take (d - k + l.1) = pL.drop k :=
            List.take_of_length_le (by omega)
          simp only [finCongr_apply, Fin.val_cast, Fin.val_natAdd, ordR, List.take_append, hlen_drop,
            htk, Nat.add_sub_cancel_left, List.toFinset_append, ← Finset.union_assoc, h1]
        rw [hget, hpref]
        have hS_sub : S ⊆ G ∪ (ordT.take l).toFinset := by
          intro x hx; apply Finset.mem_union_left
          rw [← hcovG, ← permList_toFinset gList π, List.mem_toFinset]
          exact List.mem_of_mem_take (List.mem_toFinset.mp hx)
        have hcs := cauchy_schwarz_fibre Ω hΩ hS_sub (ordT[l])
        have he := coordCondEnt_eq_expect_h Ω (G ∪ (ordT.take l).toFinset) (ordT[l])
        have hsub : ∑ v ∈ Ω, unifW Ω v * (Qrv Ω S (ordT[l]) v - mStar) * h (Qrv Ω (G ∪ (ordT.take l).toFinset) (ordT[l]) v)
            = (∑ v ∈ Ω, unifW Ω v * Qrv Ω S (ordT[l]) v * h (Qrv Ω (G ∪ (ordT.take l).toFinset) (ordT[l]) v))
              - mStar * (∑ v ∈ Ω, unifW Ω v * h (Qrv Ω (G ∪ (ordT.take l).toFinset) (ordT[l]) v)) := by
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro v _; ring
        rw [hsub, ← he]; linarith
      -- Lower-bound G \ S part using fibre_term_lower_bound!
      have hG_lb :
          (∑ j : Fin d, if k ≤ (j : ℕ) then
              ((bm / pStar) * coordCondEnt Ω (unifW Ω) id ((ordP π)[idxG π j]) (((ordP π).take (idxG π j)).toFinset)
              + bm * cParam * (∑ v ∈ Ω, unifW Ω v * phi (Qrv Ω (((ordP π).take (idxG π j)).toFinset) ((ordP π)[idxG π j]) v))
              - CtotParam * (∑ v ∈ Ω, unifW Ω v * R_fun (Qrv Ω (((ordP π).take (idxG π j)).toFinset) ((ordP π)[idxG π j]) v)))
            else 0)
          - DParam * (subEnt Ω (unifW Ω) id G - subEnt Ω (unifW Ω) id S)
          - kappaParam * totalCorr Ω (unifW Ω) id G S
          ≤ ∑ r : Fin (d - k),
              ∑ v ∈ Ω, unifW Ω v * (Qrv Ω S (ordR[(finCongr hlen_ordR.symm) (Fin.castAdd ordT.length r)]) v - mStar)
                * h (Qrv Ω (S ∪ (ordR.take ((finCongr hlen_ordR.symm) (Fin.castAdd ordT.length r))).toFinset)
                      (ordR[(finCongr hlen_ordR.symm) (Fin.castAdd ordT.length r)]) v) := by
        -- Identify each r : Fin (d - k) with j = ⟨k + r, ...⟩ : Fin d!
        have hstep_r : ∀ r : Fin (d - k),
            let j : Fin d := ⟨k + r.1, by omega⟩
            ((bm / pStar) * coordCondEnt Ω (unifW Ω) id ((ordP π)[idxG π j]) (((ordP π).take (idxG π j)).toFinset)
            + bm * cParam * (∑ v ∈ Ω, unifW Ω v * phi (Qrv Ω (((ordP π).take (idxG π j)).toFinset) ((ordP π)[idxG π j]) v))
            - CtotParam * (∑ v ∈ Ω, unifW Ω v * R_fun (Qrv Ω (((ordP π).take (idxG π j)).toFinset) ((ordP π)[idxG π j]) v))
            - DParam * coordCondEnt Ω (unifW Ω) id ((ordP π)[idxG π j]) (((ordP π).take (idxG π j)).toFinset)
            - kappaParam * (coordCondEnt Ω (unifW Ω) id ((ordP π)[idxG π j]) S
                - coordCondEnt Ω (unifW Ω) id ((ordP π)[idxG π j]) (((ordP π).take (idxG π j)).toFinset)))
            ≤ ∑ v ∈ Ω, unifW Ω v * (Qrv Ω S (ordR[(finCongr hlen_ordR.symm) (Fin.castAdd ordT.length r)]) v - mStar)
                * h (Qrv Ω (S ∪ (ordR.take ((finCongr hlen_ordR.symm) (Fin.castAdd ordT.length r))).toFinset)
                      (ordR[(finCongr hlen_ordR.symm) (Fin.castAdd ordT.length r)]) v) := by
          intro r j
          have hget : ordR[(finCongr hlen_ordR.symm) (Fin.castAdd ordT.length r)] = (ordP π)[idxG π j] := by
            rw [hgetG]
            simp [ordR, List.getElem_append_left (by omega : r.1 < (pL.drop k).length), pL, j]
          have hpref : S ∪ (ordR.take ((finCongr hlen_ordR.symm) (Fin.castAdd ordT.length r))).toFinset
              = ((ordP π).take (idxG π j)).toFinset := by
            rw [htakeG]
            have h1 : ordR.take r.1 = (pL.drop k).take r.1 :=
              List.take_append_of_le_length (by rw [hlen_drop]; exact le_of_lt r.isLt)
            simp only [S, finCongr_apply, Fin.val_cast, Fin.val_castAdd, h1, ← List.toFinset_append]
            congr 1
            exact (List.take_add (l := pL) (i := k) (j := r.1)).symm
          rw [hget, hpref]
          have hS_sub : S ⊆ ((ordP π).take (idxG π j)).toFinset := by
            rw [htakeG]; intro x hx; rw [List.mem_toFinset] at hx ⊢
            exact mem_take_of_le (by simp [j]) hx
          exact fibre_term_lower_bound Ω hΩ hS_sub ((ordP π)[idxG π j]) loc
        have hsum_r := Finset.sum_le_sum fun r (_ : r ∈ Finset.univ) => hstep_r r
        -- Rewrite the sum over r : Fin (d - k) into the LHS using chain rule and totalCorr!
        have hbij_sum : ∀ f : Fin d → ℝ,
            (∑ r : Fin (d - k), f ⟨k + r.1, by omega⟩) = ∑ j : Fin d, if k ≤ (j : ℕ) then f j else 0 := by
          intro f
          rw [← Finset.sum_filter]
          apply Finset.sum_nbij (fun r : Fin (d - k) => (⟨k + r.1, by omega⟩ : Fin d))
          · intro r _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp⟩
          · intro r1 _ r2 _ hEq; ext; have := congr_arg Fin.val hEq; dsimp at this; omega
          · intro j hj
            have hkj : k ≤ j.1 := (Finset.mem_filter.mp hj).2
            exact ⟨⟨j.1 - k, by omega⟩, Finset.mem_univ _, by ext; simp; omega⟩
          · intro r _; rfl
        have hchain_diff : subEnt Ω (unifW Ω) id G - subEnt Ω (unifW Ω) id S
            = ∑ r : Fin (d - k), coordCondEnt Ω (unifW Ω) id ((ordP π)[idxG π ⟨k + r.1, by omega⟩])
                (((ordP π).take (idxG π ⟨k + r.1, by omega⟩)).toFinset) := by
          have hdisj_drop : ∀ i ∈ pL.drop k, i ∉ S := fun i hi hiS =>
            hnd_take_drop.2.2 i (List.mem_toFinset.mp hiS) i hi rfl
          have h1 := subEnt_append_list Ω (unifW Ω) id S (pL.drop k) hnd_take_drop.2.1 hdisj_drop
          have hSG : S ∪ (pL.drop k).toFinset = G := by
            rw [← List.toFinset_append, htake_drop, permList_toFinset, hcovG]
          rw [hSG] at h1
          rw [h1, ← (finCongr hlen_drop.symm).sum_comp]
          apply Finset.sum_congr rfl; intro r _
          congr 1
          · rw [hgetG]; simp [pL]
          · rw [htakeG, ← List.toFinset_append, ← List.take_add]; rfl
        have hS_cond_sum : ∑ i ∈ G \ S, coordCondEnt Ω (unifW Ω) id i S
            = ∑ r : Fin (d - k), coordCondEnt Ω (unifW Ω) id ((ordP π)[idxG π ⟨k + r.1, by omega⟩]) S := by
          have hGsdiff : G \ S = (pL.drop k).toFinset := by
            ext x; simp only [Finset.mem_sdiff, List.mem_toFinset]
            have hmemG : x ∈ G ↔ x ∈ pL.take k ∨ x ∈ pL.drop k := by
              have hG_pL : G = pL.toFinset := by simp only [pL, permList_toFinset, hcovG]
              conv_lhs => rw [hG_pL, ← htake_drop, List.toFinset_append, Finset.mem_union,
                  List.mem_toFinset, List.mem_toFinset]
            constructor
            · rintro ⟨hxG, hxnotS⟩
              rcases hmemG.mp hxG with h1 | h2
              · exact absurd (List.mem_toFinset.mpr h1) hxnotS
              · exact h2
            · intro hx
              exact ⟨hmemG.mpr (Or.inr hx), fun h1 => hnd_take_drop.2.2 x (List.mem_toFinset.mp h1) x hx rfl⟩
          rw [hGsdiff]
          symm
          apply Finset.sum_nbij (fun r : Fin (d - k) => (ordP π)[idxG π ⟨k + r.1, by omega⟩])
          · intro r _; rw [hgetG, List.mem_toFinset]
            have hlt : r.1 < (pL.drop k).length := by omega
            have heq : (pL.drop k)[r.1]'hlt = pL[k + r.1]'(by omega) := List.getElem_drop
            change pL[k + r.1]'(by omega) ∈ pL.drop k
            rw [← heq]; exact List.getElem_mem hlt
          · intro r1 _ r2 _ hEq
            simp only [hgetG, Fin.getElem_fin] at hEq
            have h2 := (List.nodup_iff_injective_getElem.mp hnd_pL)
              (a₁ := ⟨k + r1.1, by omega⟩) (a₂ := ⟨k + r2.1, by omega⟩) hEq
            ext; have := congr_arg Fin.val h2; dsimp at this; omega
          · intro x hx
            rcases List.mem_iff_getElem.mp (List.mem_toFinset.mp hx) with ⟨idx, hidx, rfl⟩
            refine ⟨⟨idx, by omega⟩, Finset.mem_univ _, ?_⟩
            simp only [hgetG, Fin.getElem_fin]; simp [pL]
          · intro r _; rfl
        have hLHS_rew :
            (∑ r : Fin (d - k),
              ((bm / pStar) * coordCondEnt Ω (unifW Ω) id ((ordP π)[idxG π ⟨k + r.1, by omega⟩])
                  (((ordP π).take (idxG π ⟨k + r.1, by omega⟩)).toFinset)
              + bm * cParam * (∑ v ∈ Ω, unifW Ω v * phi (Qrv Ω (((ordP π).take (idxG π ⟨k + r.1, by omega⟩)).toFinset)
                  ((ordP π)[idxG π ⟨k + r.1, by omega⟩]) v))
              - CtotParam * (∑ v ∈ Ω, unifW Ω v * R_fun (Qrv Ω (((ordP π).take (idxG π ⟨k + r.1, by omega⟩)).toFinset)
                  ((ordP π)[idxG π ⟨k + r.1, by omega⟩]) v))
              - DParam * coordCondEnt Ω (unifW Ω) id ((ordP π)[idxG π ⟨k + r.1, by omega⟩])
                  (((ordP π).take (idxG π ⟨k + r.1, by omega⟩)).toFinset)
              - kappaParam * (coordCondEnt Ω (unifW Ω) id ((ordP π)[idxG π ⟨k + r.1, by omega⟩]) S
                  - coordCondEnt Ω (unifW Ω) id ((ordP π)[idxG π ⟨k + r.1, by omega⟩])
                      (((ordP π).take (idxG π ⟨k + r.1, by omega⟩)).toFinset))))
            = (∑ j : Fin d, if k ≤ (j : ℕ) then
                ((bm / pStar) * coordCondEnt Ω (unifW Ω) id ((ordP π)[idxG π j]) (((ordP π).take (idxG π j)).toFinset)
                + bm * cParam * (∑ v ∈ Ω, unifW Ω v * phi (Qrv Ω (((ordP π).take (idxG π j)).toFinset) ((ordP π)[idxG π j]) v))
                - CtotParam * (∑ v ∈ Ω, unifW Ω v * R_fun (Qrv Ω (((ordP π).take (idxG π j)).toFinset) ((ordP π)[idxG π j]) v)))
              else 0)
              - DParam * (subEnt Ω (unifW Ω) id G - subEnt Ω (unifW Ω) id S)
              - kappaParam * totalCorr Ω (unifW Ω) id G S := by
          let fA : Fin d → ℝ := fun j =>
            (bm / pStar) * coordCondEnt Ω (unifW Ω) id ((ordP π)[idxG π j]) (((ordP π).take (idxG π j)).toFinset)
            + bm * cParam * (∑ v ∈ Ω, unifW Ω v * phi (Qrv Ω (((ordP π).take (idxG π j)).toFinset) ((ordP π)[idxG π j]) v))
            - CtotParam * (∑ v ∈ Ω, unifW Ω v * R_fun (Qrv Ω (((ordP π).take (idxG π j)).toFinset) ((ordP π)[idxG π j]) v))
          change (∑ r : Fin (d - k),
              (fA ⟨k + r.1, by omega⟩
               - DParam * coordCondEnt Ω (unifW Ω) id ((ordP π)[idxG π ⟨k + r.1, by omega⟩])
                   (((ordP π).take (idxG π ⟨k + r.1, by omega⟩)).toFinset)
               - kappaParam * (coordCondEnt Ω (unifW Ω) id ((ordP π)[idxG π ⟨k + r.1, by omega⟩]) S
                   - coordCondEnt Ω (unifW Ω) id ((ordP π)[idxG π ⟨k + r.1, by omega⟩])
                       (((ordP π).take (idxG π ⟨k + r.1, by omega⟩)).toFinset))))
            = (∑ j : Fin d, if k ≤ (j : ℕ) then fA j else 0)
              - DParam * (subEnt Ω (unifW Ω) id G - subEnt Ω (unifW Ω) id S)
              - kappaParam * totalCorr Ω (unifW Ω) id G S
          rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hbij_sum fA,
              ← Finset.mul_sum, ← hchain_diff, ← Finset.mul_sum, Finset.sum_sub_distrib,
              ← hS_cond_sum, ← hchain_diff]
          unfold totalCorr; ring
        linarith
      linarith
    -- STEP B: Average hfib_k over π ~ Unif(Perm (Fin d)), k ~ Bin(d, 1 - t), and integrate t ~ fTheta on [a0, 1]!
    -- Define the permutation-averaged G-terms and T-terms:
    let baseG (π : Equiv.Perm (Fin d)) (j : Fin d) : ℝ :=
      (bm / pStar) * coordCondEnt Ω (unifW Ω) id ((ordP π)[idxG π j]) (((ordP π).take (idxG π j)).toFinset)
      + bm * cParam * (∑ v ∈ Ω, unifW Ω v * phi (Qrv Ω (((ordP π).take (idxG π j)).toFinset) ((ordP π)[idxG π j]) v))
      - CtotParam * (∑ v ∈ Ω, unifW Ω v * R_fun (Qrv Ω (((ordP π).take (idxG π j)).toFinset) ((ordP π)[idxG π j]) v))
    let T_part : ℝ := ∑ l : Fin ordT.length,
      (((∑ v ∈ Ω, unifW Ω v * Real.sqrt (Qrv Ω (G ∪ (ordT.take l).toFinset) (ordT[l]) v
          * h (Qrv Ω (G ∪ (ordT.take l).toFinset) (ordT[l]) v))) ^ 2)
       - mStar * coordCondEnt Ω (unifW Ω) id (ordT[l]) (G ∪ (ordT.take l).toFinset))
    have hfib_t : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        (1 / (Nat.factorial d : ℝ)) * (∑ π : Equiv.Perm (Fin d), ∑ j : Fin d, binLe d t j * baseG π j)
        - DParam * (t * subEnt Ω (unifW Ω) id G - deltaH Ω G t)
        - kappaParam * CH Ω G t
        + T_part ≤ 0 := by
      intro t ht0 ht1
      -- Average hfib_k over k ~ Bin(d, 1 - t) and π ~ Unif(Perm (Fin d))!
      have havg_ineq :
          ∑ k ∈ Finset.range (d + 1),
            (Nat.choose d k : ℝ) * (1 - t) ^ k * t ^ (d - k)
              * ((1 / (Nat.factorial d : ℝ)) * ∑ π : Equiv.Perm (Fin d),
                  ((∑ j : Fin d, if k ≤ (j : ℕ) then baseG π j else 0)
                  - DParam * (subEnt Ω (unifW Ω) id G - subEnt Ω (unifW Ω) id (((permList gList π).take k).toFinset))
                  - kappaParam * totalCorr Ω (unifW Ω) id G (((permList gList π).take k).toFinset)
                  + T_part)) ≤ 0 := by
        apply Finset.sum_nonpos; intro k hk
        have hk_le : k ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        have h1mt : 0 ≤ 1 - t := by linarith
        apply mul_nonpos_of_nonneg_of_nonpos (by positivity)
        apply mul_nonpos_of_nonneg_of_nonpos (by positivity)
        exact Finset.sum_nonpos fun π _ => hfib_k π k hk_le
      -- Expand each of the 4 terms in havg_ineq!
      have hbin_sum1 : ∑ k ∈ Finset.range (d + 1), (Nat.choose d k : ℝ) * (1 - t) ^ k * t ^ (d - k) = 1 := by
        have hpow := add_pow (1 - t) t d; rw [sub_add_cancel, one_pow] at hpow
        calc ∑ k ∈ Finset.range (d + 1), (Nat.choose d k : ℝ) * (1 - t) ^ k * t ^ (d - k)
            = ∑ k ∈ Finset.range (d + 1), (1 - t) ^ k * t ^ (d - k) * (Nat.choose d k : ℝ) :=
              Finset.sum_congr rfl fun k _ => by ring
          _ = 1 := hpow.symm
      have hterm1 : ∑ k ∈ Finset.range (d + 1),
            (Nat.choose d k : ℝ) * (1 - t) ^ k * t ^ (d - k)
              * ((1 / (Nat.factorial d : ℝ)) * ∑ π : Equiv.Perm (Fin d), ∑ j : Fin d, if k ≤ (j : ℕ) then baseG π j else 0)
          = (1 / (Nat.factorial d : ℝ)) * ∑ π : Equiv.Perm (Fin d), ∑ j : Fin d, binLe d t j * baseG π j := by
        have h1 : ∀ k ∈ Finset.range (d + 1),
            (Nat.choose d k : ℝ) * (1 - t) ^ k * t ^ (d - k)
              * ((1 / (Nat.factorial d : ℝ)) * ∑ π : Equiv.Perm (Fin d), ∑ j : Fin d, if k ≤ (j : ℕ) then baseG π j else 0)
            = (1 / (Nat.factorial d : ℝ)) * ∑ π : Equiv.Perm (Fin d), ∑ j : Fin d,
                (if k ≤ (j : ℕ) then (Nat.choose d k : ℝ) * (1 - t) ^ k * t ^ (d - k) else 0) * baseG π j := by
          intro k _
          rw [← mul_assoc, mul_comm ((Nat.choose d k : ℝ) * (1 - t) ^ k * t ^ (d - k)), mul_assoc, Finset.mul_sum]
          congr 1; apply Finset.sum_congr rfl; intro π _; rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro j _; split_ifs <;> ring
        rw [Finset.sum_congr rfl h1, ← Finset.mul_sum, Finset.sum_comm]
        congr 1; apply Finset.sum_congr rfl; intro π _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro j _
        rw [← Finset.sum_mul]
        congr 1
        unfold binLe
        rw [← Finset.sum_filter]
        congr 1; ext k; simp only [Finset.mem_filter, Finset.mem_range]; omega
      have hterm2 : ∑ k ∈ Finset.range (d + 1),
            (Nat.choose d k : ℝ) * (1 - t) ^ k * t ^ (d - k)
              * ((1 / (Nat.factorial d : ℝ)) * ∑ π : Equiv.Perm (Fin d),
                  (subEnt Ω (unifW Ω) id G - subEnt Ω (unifW Ω) id (((permList gList π).take k).toFinset)))
          = t * subEnt Ω (unifW Ω) id G - deltaH Ω G t := by
        have h1 : subEnt Ω (unifW Ω) id G - gH Ω G t = t * subEnt Ω (unifW Ω) id G - deltaH Ω G t := by
          unfold deltaH; ring
        rw [← h1]
        have h2 := avg_perm_subset hndG hcovG t (fun S => subEnt Ω (unifW Ω) id G - subEnt Ω (unifW Ω) id S)
        rw [← h2]
        unfold gH
        simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, sum_subsetWeight G t, one_mul]
      have hterm3 : ∑ k ∈ Finset.range (d + 1),
            (Nat.choose d k : ℝ) * (1 - t) ^ k * t ^ (d - k)
              * ((1 / (Nat.factorial d : ℝ)) * ∑ π : Equiv.Perm (Fin d),
                  totalCorr Ω (unifW Ω) id G (((permList gList π).take k).toFinset))
          = CH Ω G t :=
        (avg_perm_subset hndG hcovG t (fun S => totalCorr Ω (unifW Ω) id G S)).symm
      have hterm4 : ∑ k ∈ Finset.range (d + 1),
            (Nat.choose d k : ℝ) * (1 - t) ^ k * t ^ (d - k)
              * ((1 / (Nat.factorial d : ℝ)) * ∑ _π : Equiv.Perm (Fin d), T_part)
          = T_part := by
        have hc : (1 / (Nat.factorial d : ℝ)) * ∑ _π : Equiv.Perm (Fin d), T_part = T_part := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
          field_simp [hfact_ne]
        simp_rw [hc, ← Finset.sum_mul, hbin_sum1, one_mul]
      have hexp : ∑ k ∈ Finset.range (d + 1),
            (Nat.choose d k : ℝ) * (1 - t) ^ k * t ^ (d - k)
              * ((1 / (Nat.factorial d : ℝ)) * ∑ π : Equiv.Perm (Fin d),
                  ((∑ j : Fin d, if k ≤ (j : ℕ) then baseG π j else 0)
                  - DParam * (subEnt Ω (unifW Ω) id G - subEnt Ω (unifW Ω) id (((permList gList π).take k).toFinset))
                  - kappaParam * totalCorr Ω (unifW Ω) id G (((permList gList π).take k).toFinset)
                  + T_part))
          = (1 / (Nat.factorial d : ℝ)) * (∑ π : Equiv.Perm (Fin d), ∑ j : Fin d, binLe d t j * baseG π j)
            - DParam * (t * subEnt Ω (unifW Ω) id G - deltaH Ω G t)
            - kappaParam * CH Ω G t
            + T_part := by
        conv_rhs =>
          rw [← hterm1, ← hterm2, ← hterm3, ← hterm4,
              Finset.mul_sum, Finset.mul_sum,
              ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro k _
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
        ring
      linarith
    -- Integrate hfib_t against fTheta(t) on [a0Param, 1]!
    have hfib_int :
        (1 / (Nat.factorial d : ℝ)) * (∑ π : Equiv.Perm (Fin d), ∑ j : Fin d, wWeight d j * baseG π j)
        - DParam * etaParam * subEnt Ω (unifW Ω) id G
        - WParam * deltaH Ω G a0Param
        + T_part ≤ 0 := by
      have ha0 : a0Param ≤ 1 := le_of_lt a0Param_lt_one
      have hcont_gH : Continuous (gH Ω G) := by unfold gH subsetWeight; fun_prop
      have hcont_deltaH : Continuous (deltaH Ω G) := by unfold deltaH; exact hcont_gH.sub (by fun_prop)
      have hcont_CH : Continuous (CH Ω G) := by unfold CH subsetWeight; fun_prop
      have hcont_base : Continuous (fun t => (1 / (Nat.factorial d : ℝ)) *
          ∑ π : Equiv.Perm (Fin d), ∑ j : Fin d, binLe d t j * baseG π j) := by
        unfold binLe; fun_prop
      have hint_main : IntervalIntegrable (fun t => fTheta t *
          ((1 / (Nat.factorial d : ℝ)) * (∑ π : Equiv.Perm (Fin d), ∑ j : Fin d, binLe d t j * baseG π j)
          - DParam * (t * subEnt Ω (unifW Ω) id G - deltaH Ω G t)
          - kappaParam * CH Ω G t + T_part)) MeasureTheory.volume a0Param 1 := by
        apply ContinuousOn.intervalIntegrable
        exact continuousOn_fTheta.mul (((hcont_base.continuousOn.sub
          (continuousOn_const.mul ((continuousOn_id.mul continuousOn_const).sub hcont_deltaH.continuousOn))).sub
          (continuousOn_const.mul hcont_CH.continuousOn)).add continuousOn_const)
      have hle0 : ∫ t in a0Param..1, fTheta t *
          ((1 / (Nat.factorial d : ℝ)) * (∑ π : Equiv.Perm (Fin d), ∑ j : Fin d, binLe d t j * baseG π j)
          - DParam * (t * subEnt Ω (unifW Ω) id G - deltaH Ω G t)
          - kappaParam * CH Ω G t + T_part) ≤ 0 := by
        calc ∫ t in a0Param..1, _ ≤ ∫ _t in a0Param..1, (0 : ℝ) := by
              apply intervalIntegral.integral_mono_on ha0 hint_main intervalIntegrable_const
              intro t ht
              exact mul_nonpos_of_nonneg_of_nonpos
                (fTheta_nonneg (lt_of_lt_of_le a0Param_pos ht.1) loc.hD_lt_kappa)
                (hfib_t t (le_trans (le_of_lt a0Param_pos) ht.1) ht.2)
          _ = 0 := by simp
      -- Evaluate the integral piece by piece!
      have h1 : IntervalIntegrable (fun t => fTheta t * ((1 / (Nat.factorial d : ℝ)) *
          ∑ π : Equiv.Perm (Fin d), ∑ j : Fin d, binLe d t j * baseG π j)) MeasureTheory.volume a0Param 1 :=
        (continuousOn_fTheta.mul hcont_base.continuousOn).intervalIntegrable
      have h2 : IntervalIntegrable (fun t => fTheta t * (DParam * (t * subEnt Ω (unifW Ω) id G)))
          MeasureTheory.volume a0Param 1 :=
        (continuousOn_fTheta.mul (continuousOn_const.mul (continuousOn_id.mul continuousOn_const))).intervalIntegrable
      have h3 : IntervalIntegrable (fun t => fTheta t * (kappaParam * CH Ω G t - DParam * deltaH Ω G t))
          MeasureTheory.volume a0Param 1 :=
        (continuousOn_fTheta.mul ((continuousOn_const.mul hcont_CH.continuousOn).sub
          (continuousOn_const.mul hcont_deltaH.continuousOn))).intervalIntegrable
      have h4 : IntervalIntegrable (fun t => fTheta t * T_part) MeasureTheory.volume a0Param 1 :=
        (continuousOn_fTheta.mul continuousOn_const).intervalIntegrable
      have hsplit_fn : (fun t => fTheta t *
          ((1 / (Nat.factorial d : ℝ)) * (∑ π : Equiv.Perm (Fin d), ∑ j : Fin d, binLe d t j * baseG π j)
          - DParam * (t * subEnt Ω (unifW Ω) id G - deltaH Ω G t)
          - kappaParam * CH Ω G t + T_part))
          = (fun t =>
              (fTheta t * ((1 / (Nat.factorial d : ℝ)) *
                ∑ π : Equiv.Perm (Fin d), ∑ j : Fin d, binLe d t j * baseG π j))
              - (fTheta t * (DParam * (t * subEnt Ω (unifW Ω) id G)))
              - (fTheta t * (kappaParam * CH Ω G t - DParam * deltaH Ω G t))
              + (fTheta t * T_part)) := by ext t; ring
      rw [hsplit_fn, intervalIntegral.integral_add ((h1.sub h2).sub h3) h4,
          intervalIntegral.integral_sub (h1.sub h2) h3,
          intervalIntegral.integral_sub h1 h2] at hle0
      -- Evaluate each of the 4 integrals:
      have hint1 : ∫ t in a0Param..1, fTheta t * ((1 / (Nat.factorial d : ℝ)) *
            ∑ π : Equiv.Perm (Fin d), ∑ j : Fin d, binLe d t j * baseG π j)
          = (1 / (Nat.factorial d : ℝ)) * ∑ π : Equiv.Perm (Fin d), ∑ j : Fin d, wWeight d j * baseG π j := by
        have hrew : (fun t => fTheta t * ((1 / (Nat.factorial d : ℝ)) *
              ∑ π : Equiv.Perm (Fin d), ∑ j : Fin d, binLe d t j * baseG π j))
            = (fun t => (1 / (Nat.factorial d : ℝ)) *
              ∑ π : Equiv.Perm (Fin d), ∑ j : Fin d, (fTheta t * binLe d t j) * baseG π j) := by
          ext t; rw [← mul_assoc, mul_comm (fTheta t), mul_assoc, Finset.mul_sum]
          congr 1; apply Finset.sum_congr rfl; intro π _; rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro j _; ring
        rw [hrew, intervalIntegral.integral_const_mul]
        congr 1
        rw [intervalIntegral.integral_finsetSum]
        · apply Finset.sum_congr rfl; intro π _
          rw [intervalIntegral.integral_finsetSum]
          · apply Finset.sum_congr rfl; intro j _
            rw [intervalIntegral.integral_mul_const]; rfl
          · intro j _; exact ((continuousOn_fTheta.mul (by unfold binLe; fun_prop)).mul continuousOn_const).intervalIntegrable
        · intro π _; apply ContinuousOn.intervalIntegrable
          apply continuousOn_finsetSum; intro j _
          exact (continuousOn_fTheta.mul (by unfold binLe; fun_prop)).mul continuousOn_const
      have hint2 : ∫ t in a0Param..1, fTheta t * (DParam * (t * subEnt Ω (unifW Ω) id G))
          = DParam * etaParam * subEnt Ω (unifW Ω) id G := by
        have hrew : (fun t => fTheta t * (DParam * (t * subEnt Ω (unifW Ω) id G)))
            = (fun t => (DParam * subEnt Ω (unifW Ω) id G) * (t * fTheta t)) := by ext t; ring
        rw [hrew, intervalIntegral.integral_const_mul, integral_mul_fTheta loc.hD0 loc.hD_lt_kappa]; ring
      have hint3 : ∫ t in a0Param..1, fTheta t * (kappaParam * CH Ω G t - DParam * deltaH Ω G t)
          = WParam * deltaH Ω G a0Param := beta_ibp Ω hΩ G loc.hD_lt_kappa
      have hint4 : ∫ t in a0Param..1, fTheta t * T_part = T_part := by
        rw [intervalIntegral.integral_mul_const, integral_fTheta loc.hD_lt_kappa, one_mul]
      rw [hint1, hint2, hint3, hint4] at hle0
      exact hle0
    -- STEP C: Combine hfib_int + permutation-averaged U-bound + global budget + zero-sum!
    let sG : Equiv.Perm (Fin d) → Fin d → ℝ := fun π j => margProb Ω ((ordP π)[idxG π j])
    let eG : Equiv.Perm (Fin d) → Fin d → ℝ := fun π j =>
      coordCondEnt Ω (unifW Ω) id ((ordP π)[idxG π j]) (((ordP π).take (idxG π j)).toFinset)
    let tG : Equiv.Perm (Fin d) → Fin d → ℝ := fun π j =>
      ∑ v ∈ Ω, unifW Ω v * phi (Qrv Ω (((ordP π).take (idxG π j)).toFinset) ((ordP π)[idxG π j]) v)
    let RG : Equiv.Perm (Fin d) → Fin d → ℝ := fun π j =>
      ∑ v ∈ Ω, unifW Ω v * R_fun (Qrv Ω (((ordP π).take (idxG π j)).toFinset) ((ordP π)[idxG π j]) v)
    let UG : Equiv.Perm (Fin d) → Fin d → ℝ := fun π j => localU Ω (ordP π) (idxG π j)
    let gG : Equiv.Perm (Fin d) → Fin d → ℝ := fun π j => localG Ω (ordP π) (idxG π j)
    let sT : Equiv.Perm (Fin d) → Fin ordT.length → ℝ := fun π l => margProb Ω ((ordP π)[idxT π l])
    let eT : Equiv.Perm (Fin d) → Fin ordT.length → ℝ := fun π l =>
      coordCondEnt Ω (unifW Ω) id ((ordP π)[idxT π l]) (((ordP π).take (idxT π l)).toFinset)
    let tT : Equiv.Perm (Fin d) → Fin ordT.length → ℝ := fun π l =>
      ∑ v ∈ Ω, unifW Ω v * phi (Qrv Ω (((ordP π).take (idxT π l)).toFinset) ((ordP π)[idxT π l]) v)
    let RT : Equiv.Perm (Fin d) → Fin ordT.length → ℝ := fun π l =>
      ∑ v ∈ Ω, unifW Ω v * R_fun (Qrv Ω (((ordP π).take (idxT π l)).toFinset) ((ordP π)[idxT π l]) v)
    let sqT : Equiv.Perm (Fin d) → Fin ordT.length → ℝ := fun π l =>
      (∑ v ∈ Ω, unifW Ω v * Real.sqrt (Qrv Ω (((ordP π).take (idxT π l)).toFinset) ((ordP π)[idxT π l]) v
        * h (Qrv Ω (((ordP π).take (idxT π l)).toFinset) ((ordP π)[idxT π l]) v))) ^ 2
    let UT : Equiv.Perm (Fin d) → Fin ordT.length → ℝ := fun π l => localU Ω (ordP π) (idxT π l)
    let gT : Equiv.Perm (Fin d) → Fin ordT.length → ℝ := fun π l => localG Ω (ordP π) (idxT π l)
    let totalComb : ℝ :=
      (1 / (Nat.factorial d : ℝ)) * ∑ π : Equiv.Perm (Fin d),
        ((∑ j : Fin d, PhiG (wWeight d j) (omWeight d j) (sG π j) (eG π j) (tG π j) (RG π j) (UG π j) (gG π j))
         + (∑ l : Fin ordT.length, PhiT (sT π l) (eT π l) (tT π l) (RT π l) (sqT π l) (UT π l) (gT π l)))
    have hcomb_le : totalComb ≤ 0 := by
      have hU_pi : ∀ π : Equiv.Perm (Fin d),
          (∑ j : Fin d, (UG π j - eG π j)) + (∑ l : Fin ordT.length, (UT π l - eT π l)) ≤ 0 := by
        intro π
        have hU := independent_protocol_bound Ω hΩ hAC (ordP π) (hordP_nd π) (hordP_cov π)
        have hH := log_card_eq_sum_coordCondEnt Ω hΩ (ordP π) (hordP_nd π) (hordP_cov π)
        have hsplit : ∑ k : Fin (ordP π).length,
              (localU Ω (ordP π) k - coordCondEnt Ω (unifW Ω) id ((ordP π)[k]) (((ordP π).take k).toFinset))
            = (∑ j : Fin d, (UG π j - eG π j)) + (∑ l : Fin ordT.length, (UT π l - eT π l)) := by
          rw [← (finCongr (hordP_len π).symm).sum_comp, Fin.sum_univ_add]; rfl
        rw [← hsplit, Finset.sum_sub_distrib, ← hH]
        exact sub_nonpos.mpr hU
      have hG_pi : ∀ π : Equiv.Perm (Fin d),
          (∑ j : Fin d, (gG π j + 2 * (sG π j - mStar) * eG π j))
          + (∑ l : Fin ordT.length, (gT π l + 2 * (sT π l - mStar) * eT π l)) ≤ 0 := by
        intro π
        have hgb := global_budget_bound Ω hΩ hAC (ordP π) (hordP_nd π) (hordP_cov π)
          (le_of_lt loc.htau0) (by linarith [loc.htau1])
        have hsplit : ∑ k : Fin (ordP π).length,
              (localG Ω (ordP π) k + 2 * (margProb Ω ((ordP π)[k]) - mStar)
                * coordCondEnt Ω (unifW Ω) id ((ordP π)[k]) (((ordP π).take k).toFinset))
            = (∑ j : Fin d, (gG π j + 2 * (sG π j - mStar) * eG π j))
              + (∑ l : Fin ordT.length, (gT π l + 2 * (sT π l - mStar) * eT π l)) := by
          rw [← (finCongr (hordP_len π).symm).sum_comp, Fin.sum_univ_add]; rfl
        have h2 : ∑ k : Fin (ordP π).length,
              2 * (margProb Ω ((ordP π)[k]) - mStar)
                * coordCondEnt Ω (unifW Ω) id ((ordP π)[k]) (((ordP π).take k).toFinset)
            = 2 * ∑ k : Fin (ordP π).length,
                (margProb Ω ((ordP π)[k]) - mStar)
                  * coordCondEnt Ω (unifW Ω) id ((ordP π)[k]) (((ordP π).take k).toFinset) := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring
        rw [← hsplit, Finset.sum_add_distrib, h2]; exact hgb
      have hzero_nu : ∑ j : Fin d, (nu1Param * (wWeight d j - etaParam) + nu2Param * omWeight d j) = 0 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
            Finset.sum_sub_distrib, sum_wWeight d loc.hD0 loc.hD_lt_kappa,
            Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, sum_omWeight d]; ring
      have hHG_pi : ∀ π : Equiv.Perm (Fin d), subEnt Ω (unifW Ω) id G = ∑ j : Fin d, eG π j := by
        intro π
        have h1 := subEnt_append_list Ω (unifW Ω) id ∅ (permList gList π) (permList_nodup hndG π) (by simp)
        simp only [Finset.empty_union, permList_toFinset, hcovG,
          subEnt_empty Ω (unifW Ω) (sum_unifW hΩ) id, sub_zero] at h1
        rw [h1, ← (finCongr (permList_length gList π).symm).sum_comp]
        apply Finset.sum_congr rfl; intro j _; dsimp only [eG]; rw [hgetG, htakeG]; rfl
      have hLHS_id :
          totalComb
          = ((1 / (Nat.factorial d : ℝ)) * (∑ π : Equiv.Perm (Fin d), ∑ j : Fin d, wWeight d j * baseG π j)
              - DParam * etaParam * subEnt Ω (unifW Ω) id G
              - WParam * deltaH Ω G a0Param + T_part)
            + muUParam * ((1 / (Nat.factorial d : ℝ)) * ∑ π : Equiv.Perm (Fin d),
                ((∑ j : Fin d, (UG π j - eG π j)) + (∑ l : Fin ordT.length, (UT π l - eT π l))))
            + mugParam * ((1 / (Nat.factorial d : ℝ)) * ∑ π : Equiv.Perm (Fin d),
                ((∑ j : Fin d, (gG π j + 2 * (sG π j - mStar) * eG π j))
                 + (∑ l : Fin ordT.length, (gT π l + 2 * (sT π l - mStar) * eT π l)))) := by
        have hconst_avg : ∀ c : ℝ, c = (1 / (Nat.factorial d : ℝ)) * ∑ _π : Equiv.Perm (Fin d), c := fun c => by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
          field_simp [hfact_ne]
        rw [deltaH_a0_eq_perm_avg Ω hΩ hndG hcovG]
        conv_rhs => rw [hconst_avg (DParam * etaParam * subEnt Ω (unifW Ω) id G), hconst_avg T_part]
        have hpull : ∀ A B C E F G1 : ℝ,
            (1 / (Nat.factorial d : ℝ)) * A - (1 / (Nat.factorial d : ℝ)) * B
            - WParam * ((1 / (Nat.factorial d : ℝ)) * C) + (1 / (Nat.factorial d : ℝ)) * E
            + muUParam * ((1 / (Nat.factorial d : ℝ)) * F)
            + mugParam * ((1 / (Nat.factorial d : ℝ)) * G1)
            = (1 / (Nat.factorial d : ℝ)) * (A - B - WParam * C + E + muUParam * F + mugParam * G1) := by
          intros; ring
        rw [hpull]; dsimp only [totalComb]; congr 1
        conv_rhs =>
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
              ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
              ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro π _
        rw [hHG_pi π]
        have hT_eq : T_part = ∑ l : Fin ordT.length, (sqT π l - mStar * eT π l) := by
          apply Finset.sum_congr rfl; intro l _; dsimp only [sqT, eT]; rw [hgetT, htakeT]
        have hdel_pi : ∑ j : Fin d, omWeight d j *
              (coordCondEnt Ω (unifW Ω) id ((permList gList π)[j]'(by simp [permList, d]))
                (((permList gList π).take j).toFinset) - eStar)
            = ∑ j : Fin d, omWeight d j * (eG π j - eStar) := by
          apply Finset.sum_congr rfl; intro j _; dsimp only [eG]; rw [hgetG, htakeG]
        have hbase_eq : ∀ j : Fin d, baseG π j = (bm / pStar) * eG π j + bm * cParam * tG π j - CtotParam * RG π j :=
          fun j => rfl
        rw [hT_eq, hdel_pi]
        simp_rw [hbase_eq]
        unfold PhiG PhiT
        have hG_part :
            ∑ j : Fin d,
              (wWeight d j * ((bm / pStar) * eG π j + bm * cParam * tG π j - CtotParam * RG π j)
               - DParam * etaParam * eG π j - WParam * omWeight d j * (eG π j - eStar)
               - nu1Param * (wWeight d j - etaParam) - nu2Param * omWeight d j
               + muUParam * (UG π j - eG π j) + mugParam * (gG π j + 2 * (sG π j - mStar) * eG π j))
            = (∑ j : Fin d, wWeight d j * ((bm / pStar) * eG π j + bm * cParam * tG π j - CtotParam * RG π j))
              - DParam * etaParam * (∑ j : Fin d, eG π j)
              - WParam * (∑ j : Fin d, omWeight d j * (eG π j - eStar))
              + muUParam * (∑ j : Fin d, (UG π j - eG π j))
              + mugParam * (∑ j : Fin d, (gG π j + 2 * (sG π j - mStar) * eG π j)) := by
          have h1 : ∀ j : Fin d,
              (wWeight d j * ((bm / pStar) * eG π j + bm * cParam * tG π j - CtotParam * RG π j)
               - DParam * etaParam * eG π j - WParam * omWeight d j * (eG π j - eStar)
               - nu1Param * (wWeight d j - etaParam) - nu2Param * omWeight d j
               + muUParam * (UG π j - eG π j) + mugParam * (gG π j + 2 * (sG π j - mStar) * eG π j))
              = (wWeight d j * ((bm / pStar) * eG π j + bm * cParam * tG π j - CtotParam * RG π j)
                 - (DParam * etaParam) * eG π j - WParam * (omWeight d j * (eG π j - eStar))
                 + muUParam * (UG π j - eG π j) + mugParam * (gG π j + 2 * (sG π j - mStar) * eG π j))
                - (nu1Param * (wWeight d j - etaParam) + nu2Param * omWeight d j) := fun _ => by ring
          rw [Finset.sum_congr rfl (fun j _ => h1 j), Finset.sum_sub_distrib, hzero_nu, sub_zero,
              Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
              ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
        have hT_part :
            ∑ l : Fin ordT.length,
              (sqT π l - mStar * eT π l + muUParam * (UT π l - eT π l) + mugParam * (gT π l + 2 * (sT π l - mStar) * eT π l))
            = (∑ l : Fin ordT.length, (sqT π l - mStar * eT π l))
              + muUParam * (∑ l : Fin ordT.length, (UT π l - eT π l))
              + mugParam * (∑ l : Fin ordT.length, (gT π l + 2 * (sT π l - mStar) * eT π l)) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        rw [hG_part, hT_part]; ring
      rw [hLHS_id]
      have hU_avg : (1 / (Nat.factorial d : ℝ)) * ∑ π : Equiv.Perm (Fin d),
            ((∑ j : Fin d, (UG π j - eG π j)) + (∑ l : Fin ordT.length, (UT π l - eT π l))) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) (Finset.sum_nonpos fun π _ => hU_pi π)
      have hG_avg : (1 / (Nat.factorial d : ℝ)) * ∑ π : Equiv.Perm (Fin d),
            ((∑ j : Fin d, (gG π j + 2 * (sG π j - mStar) * eG π j))
             + (∑ l : Fin ordT.length, (gT π l + 2 * (sT π l - mStar) * eT π l))) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) (Finset.sum_nonpos fun π _ => hG_pi π)
      have hmuU := muUParam_nonneg; have hmug := mugParam_nonneg
      nlinarith
    -- STEP D: Every G-term is strictly positive (3-Vertex Triangle Lemma + hPolyG) and every T-term is ≥ 0!
    have hcomb_pos : 0 < totalComb := by
      apply mul_pos (by positivity)
      apply Finset.sum_pos _ Finset.univ_nonempty
      intro π _
      have hG_pos : 0 < ∑ j : Fin d,
          PhiG (wWeight d j) (omWeight d j) (sG π j) (eG π j) (tG π j) (RG π j) (UG π j) (gG π j) := by
        apply Finset.sum_pos _ ⟨⟨0, hd_pos⟩, Finset.mem_univ _⟩
        intro j _
        have hvp := extract_validPoint Ω hΩ hs_min (ordP π) (hordP_nd π) (idxG π j) loc
        have hiG : (ordP π)[idxG π j] ∈ G := by
          rw [hgetG, ← hcovG, ← permList_toFinset gList π, List.mem_toFinset]
          exact List.getElem_mem (by simp [permList, d])
        have hpref_sub : ((ordP π).take (idxG π j)).toFinset ⊆ G.erase ((ordP π)[idxG π j]) := by
          intro x hx
          rw [Finset.mem_erase]
          constructor
          · intro heq; subst heq
            rw [List.mem_toFinset] at hx
            rcases List.mem_iff_getElem.mp hx with ⟨t, ht, hteq⟩
            have ht_lt : t < (idxG π j : ℕ) := by simp only [List.length_take] at ht; omega
            have h1 : (ordP π)[t]'(lt_trans ht_lt (idxG π j).isLt) = (ordP π)[idxG π j] := by
              simpa [List.getElem_take] using hteq
            have h2 := congr_arg Fin.val ((List.nodup_iff_injective_getElem.mp (hordP_nd π))
              (a₁ := ⟨t, lt_trans ht_lt (idxG π j).isLt⟩) (a₂ := idxG π j) h1)
            dsimp at h2; omega
          · rw [htakeG, List.mem_toFinset] at hx
            rw [← hcovG, ← permList_toFinset gList π, List.mem_toFinset]
            exact List.mem_of_mem_take hx
        have he_ge_z : zParam ≤ eG π j :=
          le_trans (hG_ent _ hiG) (coordCondEnt_anti Ω (unifW Ω) (fun v _ => unifW_nonneg Ω v) id _ hpref_sub)
        have htri := three_vertex_triangle d j.isLt loc.hD_lt_kappa
        have hv1 := hPolyG 0 a0Param (Or.inl ⟨rfl, rfl⟩) _ _ _ _ _ _ _ _ hvp he_ge_z
        have hv2 := hPolyG 1 a0Param (Or.inr (Or.inl ⟨rfl, rfl⟩)) _ _ _ _ _ _ _ _ hvp he_ge_z
        have hv3 := hPolyG 1 (a0Param - 1) (Or.inr (Or.inr ⟨rfl, rfl⟩)) _ _ _ _ _ _ _ _ hvp he_ge_z
        set m_min := min (PhiG 0 a0Param (sG π j) (eG π j) (tG π j) (RG π j) (UG π j) (gG π j))
          (min (PhiG 1 a0Param (sG π j) (eG π j) (tG π j) (RG π j) (UG π j) (gG π j))
               (PhiG 1 (a0Param - 1) (sG π j) (eG π j) (tG π j) (RG π j) (UG π j) (gG π j)))
        have hm_pos : 0 < m_min := lt_min hv1 (lt_min hv2 hv3)
        have hid : PhiG (wWeight d j) (omWeight d j) (sG π j) (eG π j) (tG π j) (RG π j) (UG π j) (gG π j)
            = (1 - wWeight d j) * PhiG 0 a0Param (sG π j) (eG π j) (tG π j) (RG π j) (UG π j) (gG π j)
              + (wWeight d j + omWeight d j - a0Param) * PhiG 1 a0Param (sG π j) (eG π j) (tG π j) (RG π j) (UG π j) (gG π j)
              + (a0Param - omWeight d j) * PhiG 1 (a0Param - 1) (sG π j) (eG π j) (tG π j) (RG π j) (UG π j) (gG π j) := by
          unfold PhiG; ring
        rw [hid]
        have ha : m_min ≤ PhiG 0 a0Param (sG π j) (eG π j) (tG π j) (RG π j) (UG π j) (gG π j) := min_le_left _ _
        have hb : m_min ≤ PhiG 1 a0Param (sG π j) (eG π j) (tG π j) (RG π j) (UG π j) (gG π j) := le_trans (min_le_right _ _) (min_le_left _ _)
        have hc : m_min ≤ PhiG 1 (a0Param - 1) (sG π j) (eG π j) (tG π j) (RG π j) (UG π j) (gG π j) := le_trans (min_le_right _ _) (min_le_right _ _)
        nlinarith [htri.1, htri.2.1, htri.2.2]
      have hT_nn : 0 ≤ ∑ l : Fin ordT.length,
          PhiT (sT π l) (eT π l) (tT π l) (RT π l) (sqT π l) (UT π l) (gT π l) := by
        apply Finset.sum_nonneg; intro l _
        have hvp := extract_validPoint Ω hΩ hs_min (ordP π) (hordP_nd π) (idxT π l) loc
        have he_le_z : eT π l ≤ zParam := by dsimp only [eT]; rw [hgetT, htakeT]; exact le_of_lt (hT_ent l)
        rcases hvp.he_lo.eq_or_lt with he0 | he_pos
        · exact PhiT_nonneg_of_e_zero hvp he0.symm
        · exact le_of_lt (hPolyT _ _ _ _ _ _ _ _ hvp he_pos he_le_z)
      linarith
    linarith

end UCBound
