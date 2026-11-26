module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import UCBound.Basic
public import UCBound.Entropy

@[expose] public section

/-!
# Union-Closed Reduction, Two-Copy Independent & CIID Protocols, Fibre Inequality

Contains:
- `AndClosed`: finite family of absence vectors `Fin n → Bool` closed under coordinatewise `&&`
- `unionClosed_to_andClosed`: exact ground-set reduction from any finite `UnionClosed` family
- `independent_protocol_bound`: `∑ k, U_k ≤ log |Ω|`
- `ciid_protocol_bound`: explicit finite-space CIID fair-sign coupling proving `∑ k, V_k ≤ log |Ω|`
  with an explicit CIID auxiliary variable `Z_k` whose marginals average to the law of `Q_k`
- `global_budget_bound`: `∑ g_k + 2 ∑ (s_k - mStar) e_k ≤ 0`
- `fibre_inequality`: for any subset `S` placed first, `∑_{i ∉ S} E[(p_i - mStar) h(Q_i)] ≤ 0`
- `cauchy_schwarz_fibre`: `E[p_i h(Q_i)] ≥ (E[√(Q_i h(Q_i))])^2`
-/

noncomputable section

namespace UCBound

open scoped BigOperators
open Real Finset

/-- Coordinatewise `&&`-closed family of binary absence vectors. -/
def AndClosed {n : ℕ} (Ω : Finset (Fin n → Bool)) : Prop :=
  ∀ a ∈ Ω, ∀ b ∈ Ω, (fun i => a i && b i) ∈ Ω

/-- Ground-set reduction: if a finite union-closed family `F` has a nonempty member and every
    element appears in strictly fewer than `c * |F|` sets (for `c ≤ 1`), then there exists an
    `AndClosed` family `Ω ⊆ (Fin n → Bool)` with `2 ≤ |Ω|` and every coordinate absence
    probability strictly exceeding `1 - c`. -/
lemma unionClosed_to_andClosed {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (hUC : UnionClosed F) (hNE : ∃ A ∈ F, A.Nonempty)
    {c : ℝ} (hc1 : c ≤ 1)
    (hbad : ∀ a : α, ((F.filter (fun A => a ∈ A)).card : ℝ) < c * (F.card : ℝ)) :
    ∃ (n : ℕ) (Ω : Finset (Fin n → Bool)),
      2 ≤ Ω.card ∧ AndClosed Ω ∧
      ∀ i : Fin n, 1 - c < ((Ω.filter (fun v => v i = true)).card : ℝ) / (Ω.card : ℝ) := by
  -- First show 2 ≤ F.card:
  rcases hNE with ⟨A0, hA0F, ⟨a0, ha0A0⟩⟩
  have hF_ge_two : 2 ≤ F.card := by
    by_contra hlt
    push Not at hlt
    have hcard1 : F.card = 1 := by
      have hpos : 0 < F.card := Finset.card_pos.mpr ⟨A0, hA0F⟩
      omega
    have hmem : A0 ∈ F.filter (fun A => a0 ∈ A) := Finset.mem_filter.mpr ⟨hA0F, ha0A0⟩
    have hge1 : 1 ≤ (F.filter (fun A => a0 ∈ A)).card := Finset.card_pos.mpr ⟨A0, hmem⟩
    have hb := hbad a0
    rw [hcard1] at hb
    have hge1R : (1 : ℝ) ≤ ((F.filter (fun A => a0 ∈ A)).card : ℝ) := by exact_mod_cast hge1
    push_cast at hb
    linarith
  -- Ground set U = union of all sets in F
  let U : Finset α := F.biUnion id
  let n : ℕ := U.card
  let e : Fin n ≃ {x : α // x ∈ U} := (Fintype.equivFin {x : α // x ∈ U}).symm.trans
    (Equiv.refl _) |> fun _ => (Fintype.equivFinOfCardEq (Fintype.card_coe U)).symm
  let vec : Finset α → (Fin n → Bool) := fun A i => decide ((e i).1 ∉ A)
  have hvec_inj : Set.InjOn vec (F : Set (Finset α)) := by
    intro A hAF B hBF hAB
    ext x
    by_cases hxU : x ∈ U
    · let i : Fin n := e.symm ⟨x, hxU⟩
      have hi := congr_fun hAB i
      have hei : (e i).1 = x := by simp [i]
      simp only [vec, hei, decide_eq_decide] at hi
      tauto
    · have hxA : x ∉ A := fun h => hxU (Finset.mem_biUnion.mpr ⟨A, hAF, h⟩)
      have hxB : x ∉ B := fun h => hxU (Finset.mem_biUnion.mpr ⟨B, hBF, h⟩)
      exact ⟨fun h => absurd h hxA, fun h => absurd h hxB⟩
  let Ω : Finset (Fin n → Bool) := F.image vec
  have hΩ_card : Ω.card = F.card := Finset.card_image_of_injOn hvec_inj
  refine ⟨n, Ω, by omega, ?_, ?_⟩
  · -- AndClosed Ω
    intro u hu v hv
    rcases Finset.mem_image.mp hu with ⟨A, hAF, rfl⟩
    rcases Finset.mem_image.mp hv with ⟨B, hBF, rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨A ∪ B, hUC A hAF B hBF, ?_⟩
    ext i
    by_cases hA : (e i).1 ∈ A <;> by_cases hB : (e i).1 ∈ B <;> simp [vec, hA, hB]
  · -- Absence probability > 1 - c
    intro i
    let a : α := (e i).1
    have hfilt : (Ω.filter (fun v => v i = true)).card = (F.filter (fun A => a ∉ A)).card := by
      have h1 : Ω.filter (fun v => v i = true) = (F.filter (fun A => a ∉ A)).image vec := by
        ext v
        simp only [Ω, Finset.mem_filter, Finset.mem_image]
        constructor
        · rintro ⟨⟨A, hAF, rfl⟩, hvi⟩
          exact ⟨A, ⟨hAF, by simpa [vec, a] using hvi⟩, rfl⟩
        · rintro ⟨A, ⟨hAF, haA⟩, rfl⟩
          exact ⟨⟨A, hAF, rfl⟩, by simpa [vec, a] using haA⟩
      rw [h1]
      exact Finset.card_image_of_injOn (hvec_inj.mono (by intro A hA; exact (Finset.mem_filter.mp hA).1))
    have hcomp : (F.filter (fun A => a ∈ A)).card + (F.filter (fun A => a ∉ A)).card = F.card :=
      Finset.card_filter_add_card_filter_not (fun A => a ∈ A)
    have hFpos : (0 : ℝ) < F.card := by exact_mod_cast (show 0 < F.card by omega)
    rw [hΩ_card, hfilt, lt_div_iff₀ hFpos]
    have hb := hbad a
    have hcompR : ((F.filter (fun A => a ∈ A)).card : ℝ)
        + ((F.filter (fun A => a ∉ A)).card : ℝ) = (F.card : ℝ) := by exact_mod_cast hcomp
    linarith

/-! ### Uniform Distribution & Conditional Probabilities on `Ω ⊆ (Fin n → Bool)` -/

/-- Uniform weight on a finite family `Ω`. -/
def unifW {n : ℕ} (Ω : Finset (Fin n → Bool)) : (Fin n → Bool) → ℝ :=
  fun _ => (1 : ℝ) / Ω.card

lemma unifW_nonneg {n : ℕ} (Ω : Finset (Fin n → Bool)) (v : Fin n → Bool) :
    0 ≤ unifW Ω v := by
  unfold unifW; positivity

lemma sum_unifW {n : ℕ} {Ω : Finset (Fin n → Bool)} (hΩ : Ω.Nonempty) :
    ∑ v ∈ Ω, unifW Ω v = 1 := by
  unfold unifW
  have hpos : (0 : ℝ) < Ω.card := Nat.cast_pos.mpr hΩ.card_pos
  rw [Finset.sum_const, nsmul_eq_mul]
  field_simp [ne_of_gt hpos]

/-- Marginal probability `s_i = P(A_i = true)` under uniform distribution on `Ω`. -/
def margProb {n : ℕ} (Ω : Finset (Fin n → Bool)) (i : Fin n) : ℝ :=
  pushProb Ω (unifW Ω) (fun v => v i) true

lemma margProb_eq_card_div {n : ℕ} (Ω : Finset (Fin n → Bool)) (i : Fin n) :
    margProb Ω i = ((Ω.filter (fun v => v i = true)).card : ℝ) / (Ω.card : ℝ) := by
  unfold margProb pushProb unifW
  rw [Finset.sum_const, nsmul_eq_mul, mul_one_div]

/-- Fibre probability `P(A_S = y)` under uniform distribution on `Ω`. -/
def fibreProb {n : ℕ} (Ω : Finset (Fin n → Bool)) (S : Finset (Fin n)) (y : Fin n → Bool) : ℝ :=
  pushProb Ω (unifW Ω) (restrictVec S) y

/-- Conditional probability `P(A_i = true | A_S = y)`. -/
def condProb {n : ℕ} (Ω : Finset (Fin n → Bool)) (S : Finset (Fin n)) (i : Fin n)
    (y : Fin n → Bool) : ℝ :=
  pushProb Ω (unifW Ω) (fun v => (v i, restrictVec S v)) (true, y) / fibreProb Ω S y

/-- Random variable `Q_{i, S}(v) = P(A_i = true | A_S = v_S)`. -/
def Qrv {n : ℕ} (Ω : Finset (Fin n → Bool)) (S : Finset (Fin n)) (i : Fin n)
    (v : Fin n → Bool) : ℝ :=
  condProb Ω S i (restrictVec S v)

lemma fibreProb_nonneg {n : ℕ} (Ω : Finset (Fin n → Bool)) (S : Finset (Fin n))
    (y : Fin n → Bool) : 0 ≤ fibreProb Ω S y :=
  pushProb_nonneg Ω (unifW Ω) (fun v _ => unifW_nonneg Ω v) _ _

lemma fibreProb_pos_of_mem_image {n : ℕ} (Ω : Finset (Fin n → Bool)) (S : Finset (Fin n))
    {y : Fin n → Bool} (hy : y ∈ Ω.image (restrictVec S)) :
    0 < fibreProb Ω S y := by
  rcases Finset.mem_image.mp hy with ⟨v, hvΩ, rfl⟩
  have hΩpos : (0 : ℝ) < Ω.card := Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨v, hvΩ⟩)
  unfold fibreProb pushProb unifW
  rw [Finset.sum_const, nsmul_eq_mul, mul_one_div]
  have hfilt : 0 < (Ω.filter (fun w => restrictVec S w = restrictVec S v)).card :=
    Finset.card_pos.mpr ⟨v, Finset.mem_filter.mpr ⟨hvΩ, rfl⟩⟩
  exact div_pos (Nat.cast_pos.mpr hfilt) hΩpos

lemma condProb_nonneg {n : ℕ} (Ω : Finset (Fin n → Bool)) (S : Finset (Fin n))
    (i : Fin n) (y : Fin n → Bool) : 0 ≤ condProb Ω S i y :=
  div_nonneg (pushProb_nonneg Ω (unifW Ω) (fun v _ => unifW_nonneg Ω v) _ _)
    (fibreProb_nonneg Ω S y)

lemma condProb_le_one {n : ℕ} (Ω : Finset (Fin n → Bool)) (S : Finset (Fin n))
    (i : Fin n) (y : Fin n → Bool) : condProb Ω S i y ≤ 1 := by
  unfold condProb fibreProb
  have hden : 0 ≤ pushProb Ω (unifW Ω) (restrictVec S) y :=
    pushProb_nonneg Ω (unifW Ω) (fun v _ => unifW_nonneg Ω v) _ _
  rcases hden.eq_or_lt with h0 | hpos
  · rw [← h0, div_zero]; norm_num
  · rw [div_le_one hpos]
    unfold pushProb
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro v hv
      have h := Finset.mem_filter.mp hv
      exact Finset.mem_filter.mpr ⟨h.1, (Prod.mk.inj h.2).2⟩
    · intro v _ _; exact unifW_nonneg Ω v

lemma Qrv_mem_Icc {n : ℕ} (Ω : Finset (Fin n → Bool)) (S : Finset (Fin n))
    (i : Fin n) (v : Fin n → Bool) : 0 ≤ Qrv Ω S i v ∧ Qrv Ω S i v ≤ 1 :=
  ⟨condProb_nonneg Ω S i _, condProb_le_one Ω S i _⟩

/-- Fiberwise expectation identity: `E_Ω[ψ(Qrv Ω S i)] = ∑_y P(A_S = y) ψ(condProb Ω S i y)`. -/
lemma expect_comp_restrictVec {n : ℕ} (Ω : Finset (Fin n → Bool)) (S : Finset (Fin n))
    (g : (Fin n → Bool) → ℝ) :
    ∑ v ∈ Ω, unifW Ω v * g (restrictVec S v) =
      ∑ y ∈ Ω.image (restrictVec S), fibreProb Ω S y * g y := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := restrictVec S) (t := Ω.image (restrictVec S))
        (fun v hv => Finset.mem_image_of_mem _ hv)]
  apply Finset.sum_congr rfl
  intro y _
  unfold fibreProb pushProb
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro v hv
  rw [(Finset.mem_filter.mp hv).2]

lemma expect_Qrv {n : ℕ} (Ω : Finset (Fin n → Bool)) (S : Finset (Fin n)) (i : Fin n) :
    ∑ v ∈ Ω, unifW Ω v * Qrv Ω S i v = margProb Ω i := by
  unfold Qrv
  rw [expect_comp_restrictVec]
  have hterm : ∀ y ∈ Ω.image (restrictVec S),
      fibreProb Ω S y * condProb Ω S i y
        = pushProb Ω (unifW Ω) (fun v => (v i, restrictVec S v)) (true, y) := by
    intro y hy
    unfold condProb
    exact mul_div_cancel₀ _ (ne_of_gt (fibreProb_pos_of_mem_image Ω S hy))
  rw [Finset.sum_congr rfl hterm]
  unfold margProb pushProb
  have hpart : ∀ y ∈ Ω.image (restrictVec S),
      Ω.filter (fun v => (v i, restrictVec S v) = (true, y))
        = (Ω.filter (fun v => v i = true)).filter (fun v => restrictVec S v = y) := by
    intro y _; ext v; simp only [Finset.mem_filter, Prod.mk.injEq]; tauto
  rw [Finset.sum_congr rfl fun y hy => by rw [hpart y hy]]
  rw [← Finset.sum_fiberwise_of_maps_to (g := restrictVec S) (t := Ω.image (restrictVec S))
        (fun v hv => Finset.mem_image_of_mem _ (Finset.mem_filter.mp hv).1)]

lemma coordCondEnt_eq_expect_h {n : ℕ} (Ω : Finset (Fin n → Bool)) (S : Finset (Fin n)) (i : Fin n) :
    coordCondEnt Ω (unifW Ω) id i S = ∑ v ∈ Ω, unifW Ω v * h (Qrv Ω S i v) := by
  unfold Qrv
  rw [expect_comp_restrictVec Ω S (fun y => h (condProb Ω S i y))]
  exact condRvEnt_bool_eq_sum_h Ω (unifW Ω) (fun v _ => unifW_nonneg Ω v) (fun v => v i) (restrictVec S)

/-- Tower property: if `S ⊆ P`, then summing `unifW Ω v * Qrv Ω P i v` over the fibre `A_S = y`
    equals `fibreProb Ω S y * condProb Ω S i y`. -/
lemma sum_fibre_Qrv {n : ℕ} (Ω : Finset (Fin n → Bool)) {S P : Finset (Fin n)} (hSP : S ⊆ P)
    (i : Fin n) (y : Fin n → Bool) :
    ∑ v ∈ Ω.filter (fun v => restrictVec S v = y), unifW Ω v * Qrv Ω P i v =
      fibreProb Ω S y * condProb Ω S i y := by
  set Fy := Ω.filter (fun v => restrictVec S v = y)
  have hmaps : ∀ v ∈ Fy, restrictVec P v ∈ Ω.image (restrictVec P) := fun v hv =>
    Finset.mem_image_of_mem _ (Finset.mem_filter.mp hv).1
  rw [← Finset.sum_fiberwise_of_maps_to (g := restrictVec P) hmaps]
  have hsub_eq : ∀ z ∈ Ω.image (restrictVec P),
      ∑ v ∈ Fy.filter (fun v => restrictVec P v = z), unifW Ω v * Qrv Ω P i v =
        if restrictVec S z = y then
          pushProb Ω (unifW Ω) (fun v => (v i, restrictVec P v)) (true, z)
        else 0 := by
    intro z hz
    by_cases hzy : restrictVec S z = y
    · simp only [hzy, ↓reduceIte]
      have hfilt : Fy.filter (fun v => restrictVec P v = z) = Ω.filter (fun v => restrictVec P v = z) := by
        ext v; simp only [Fy, Finset.mem_filter]
        constructor
        · rintro ⟨⟨hvΩ, _⟩, hvP⟩; exact ⟨hvΩ, hvP⟩
        · rintro ⟨hvΩ, hvP⟩
          refine ⟨⟨hvΩ, ?_⟩, hvP⟩
          rw [← hzy, ← hvP]
          ext j; simp only [restrictVec]
          by_cases hj : j ∈ S
          · simp [hj, hSP hj]
          · simp [hj]
      rw [hfilt]
      have hcongr : ∀ v ∈ Ω.filter (fun v => restrictVec P v = z),
          unifW Ω v * Qrv Ω P i v = unifW Ω v * condProb Ω P i z := by
        intro v hv; unfold Qrv; rw [(Finset.mem_filter.mp hv).2]
      rw [Finset.sum_congr rfl hcongr, ← Finset.sum_mul]
      change fibreProb Ω P z * condProb Ω P i z = _
      unfold condProb
      exact mul_div_cancel₀ _ (ne_of_gt (fibreProb_pos_of_mem_image Ω P hz))
    · simp only [hzy, ↓reduceIte]
      apply Finset.sum_eq_zero; intro v hv; exfalso
      have h := Finset.mem_filter.mp hv
      have h1 := (Finset.mem_filter.mp h.1).2
      have h2 := h.2
      apply hzy
      rw [← h1, ← h2]
      ext j; simp only [restrictVec]
      by_cases hj : j ∈ S
      · simp [hj, hSP hj]
      · simp [hj]
  rw [Finset.sum_congr rfl hsub_eq, ← Finset.sum_filter]
  -- Now sum over z ∈ (Ω.image (restrictVec P)).filter (restrictVec S z = y) of P(v i = true, v_P = z)
  have hRHS : fibreProb Ω S y * condProb Ω S i y
      = pushProb Ω (unifW Ω) (fun v => (v i, restrictVec S v)) (true, y) := by
    by_cases hy : y ∈ Ω.image (restrictVec S)
    · unfold condProb; exact mul_div_cancel₀ _ (ne_of_gt (fibreProb_pos_of_mem_image Ω S hy))
    · have h0 : fibreProb Ω S y = 0 := pushProb_eq_zero_of_not_mem_image Ω (unifW Ω) (restrictVec S) hy
      rw [h0, zero_mul]
      symm
      unfold pushProb
      apply Finset.sum_eq_zero; intro v hv; exfalso
      have h := Finset.mem_filter.mp hv
      exact hy (Finset.mem_image.mpr ⟨v, h.1, (Prod.mk.inj h.2).2⟩)
  rw [hRHS]
  unfold pushProb
  set Zset := (Ω.image (restrictVec P)).filter (fun z => restrictVec S z = y)
  have hpart : ∀ z ∈ Zset,
      Ω.filter (fun v => (v i, restrictVec P v) = (true, z))
        = (Ω.filter (fun v => (v i, restrictVec S v) = (true, y))).filter (fun v => restrictVec P v = z) := by
    intro z hz
    have hzy : restrictVec S z = y := (Finset.mem_filter.mp hz).2
    ext v; simp only [Finset.mem_filter, Prod.mk.injEq]
    constructor
    · rintro ⟨hvΩ, hvi, hvP⟩
      refine ⟨⟨hvΩ, hvi, ?_⟩, hvP⟩
      rw [← hzy, ← hvP]
      ext j; simp only [restrictVec]
      by_cases hj : j ∈ S
      · simp [hj, hSP hj]
      · simp [hj]
    · rintro ⟨⟨hvΩ, hvi, _⟩, hvP⟩; exact ⟨hvΩ, hvi, hvP⟩
  rw [Finset.sum_congr rfl fun z hz => by rw [hpart z hz]]
  rw [Finset.sum_fiberwise_of_maps_to (g := restrictVec P) (t := Zset)]
  intro v hv
  have h := Finset.mem_filter.mp hv
  refine Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ h.1, ?_⟩
  rw [← (Prod.mk.inj h.2).2]
  ext j; simp only [restrictVec]
  by_cases hj : j ∈ S
  · simp [hj, hSP hj]
  · simp [hj]

/-! ### Independent Two-Copy Protocol (`∑ U_k ≤ log |Ω|`) -/

/-- Two-copy independent protocol bound along any complete nodup coordinate order `ord`. -/
lemma independent_protocol_bound {n : ℕ} (Ω : Finset (Fin n → Bool)) (hΩ : Ω.Nonempty)
    (hAC : AndClosed Ω) (ord : List (Fin n)) (hnd : ord.Nodup) (hcov : ord.toFinset = Finset.univ) :
    ∑ k : Fin ord.length,
      (∑ a ∈ Ω, ∑ b ∈ Ω,
        unifW Ω a * unifW Ω b *
          h (Qrv Ω ((ord.take k).toFinset) (ord[k]) a *
             Qrv Ω ((ord.take k).toFinset) (ord[k]) b))
      ≤ Real.log Ω.card := by
  let Ω2 := Ω ×ˢ Ω
  let w2 : (Fin n → Bool) × (Fin n → Bool) → ℝ := fun p => unifW Ω p.1 * unifW Ω p.2
  let C : (Fin n → Bool) × (Fin n → Bool) → (Fin n → Bool) := fun p i => p.1 i && p.2 i
  have hw2_nn : ∀ p ∈ Ω2, 0 ≤ w2 p := fun p _ => mul_nonneg (unifW_nonneg Ω p.1) (unifW_nonneg Ω p.2)
  have hw2_sum : ∑ p ∈ Ω2, w2 p = 1 := by
    simp only [Ω2, w2, Finset.sum_product, ← Finset.mul_sum, sum_unifW hΩ, mul_one]
  -- Step 1: H(C) ≤ log |Ω| since C(Ω × Ω) ⊆ Ω
  have hC_sub : Ω2.image C ⊆ Ω := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨⟨a, b⟩, hab, rfl⟩
    rcases Finset.mem_product.mp hab with ⟨ha, hb⟩
    exact hAC a ha b hb
  have hHC_le : rvEnt Ω2 w2 C ≤ Real.log Ω.card := by
    have h1 := rvEnt_le_log_card Ω2 w2 hw2_nn hw2_sum (hΩ.product hΩ) C
    have hcard_le : ((Ω2.image C).card : ℝ) ≤ (Ω.card : ℝ) := by
      exact_mod_cast Finset.card_le_card hC_sub
    have himg_pos : (0 : ℝ) < (Ω2.image C).card := Nat.cast_pos.mpr ((hΩ.product hΩ).image C).card_pos
    exact le_trans h1 (Real.log_le_log himg_pos hcard_le)
  -- Step 2: Chain rule for H(C) along ord
  have hchain : rvEnt Ω2 w2 C =
      ∑ k : Fin ord.length, coordCondEnt Ω2 w2 C (ord[k]) ((ord.take k).toFinset) := by
    have h1 := subEnt_append_list Ω2 w2 C ∅ ord hnd (by simp)
    simp only [Finset.empty_union, hcov, subEnt_univ, subEnt_empty Ω2 w2 hw2_sum C, sub_zero] at h1
    exact h1
  -- Step 3: For each k, bound coordCondEnt from below by conditioning on (a_{<k}, b_{<k})
  have hstep : ∀ k : Fin ord.length,
      (∑ a ∈ Ω, ∑ b ∈ Ω,
        unifW Ω a * unifW Ω b *
          h (Qrv Ω ((ord.take k).toFinset) (ord[k]) a *
             Qrv Ω ((ord.take k).toFinset) (ord[k]) b))
        ≤ coordCondEnt Ω2 w2 C (ord[k]) ((ord.take k).toFinset) := by
    intro k
    set S := (ord.take k).toFinset
    set i := ord[k]
    -- restrictVec S (C p) = ψ (restrictVec S p.1, restrictVec S p.2)
    let ψ : (Fin n → Bool) × (Fin n → Bool) → (Fin n → Bool) :=
      fun q j => q.1 j && q.2 j
    have hcomp : (fun p => restrictVec S (C p))
        = (fun p => ψ (restrictVec S p.1, restrictVec S p.2)) := by
      ext ⟨a, b⟩ j
      simp only [restrictVec, C, ψ]
      by_cases hj : j ∈ S <;> simp [hj]
    have hmono : condRvEnt Ω2 w2 (fun p => C p i) (fun p => (restrictVec S p.1, restrictVec S p.2))
        ≤ coordCondEnt Ω2 w2 C i S := by
      unfold coordCondEnt
      rw [hcomp]
      exact condRvEnt_le_of_comp Ω2 w2 hw2_nn (fun p => C p i)
        (fun p => (restrictVec S p.1, restrictVec S p.2)) ψ
    -- Compute LHS using condRvEnt_bool_eq_sum_h:
    have hLHS_eq :
        condRvEnt Ω2 w2 (fun p => C p i) (fun p => (restrictVec S p.1, restrictVec S p.2))
        = ∑ a ∈ Ω, ∑ b ∈ Ω, unifW Ω a * unifW Ω b * h (Qrv Ω S i a * Qrv Ω S i b) := by
      rw [condRvEnt_bool_eq_sum_h Ω2 w2 hw2_nn]
      have himg : Ω2.image (fun p => (restrictVec S p.1, restrictVec S p.2))
          = (Ω.image (restrictVec S)) ×ˢ (Ω.image (restrictVec S)) := by
        ext ⟨x, y⟩
        simp only [Ω2, Finset.mem_image, Finset.mem_product, Prod.exists, Prod.mk.injEq]
        constructor
        · rintro ⟨a, b, ⟨ha, hb⟩, hx, hy⟩; exact ⟨⟨a, ha, hx⟩, ⟨b, hb, hy⟩⟩
        · rintro ⟨⟨a, ha, hx⟩, ⟨b, hb, hy⟩⟩; exact ⟨a, b, ⟨ha, hb⟩, hx, hy⟩
      rw [himg, Finset.sum_product]
      -- Compute pushProb on product space
      have hterm : ∀ x ∈ Ω.image (restrictVec S), ∀ y ∈ Ω.image (restrictVec S),
          pushProb Ω2 w2 (fun p => (restrictVec S p.1, restrictVec S p.2)) (x, y)
            * h (pushProb Ω2 w2 (fun p => (C p i, (restrictVec S p.1, restrictVec S p.2))) (true, (x, y))
                / pushProb Ω2 w2 (fun p => (restrictVec S p.1, restrictVec S p.2)) (x, y))
          = fibreProb Ω S x * fibreProb Ω S y * h (condProb Ω S i x * condProb Ω S i y) := by
        intro x hx y hy
        have hden : pushProb Ω2 w2 (fun p => (restrictVec S p.1, restrictVec S p.2)) (x, y)
            = fibreProb Ω S x * fibreProb Ω S y := by
          unfold fibreProb pushProb
          have hfilt : Ω2.filter (fun p => (restrictVec S p.1, restrictVec S p.2) = (x, y))
              = (Ω.filter (fun a => restrictVec S a = x)) ×ˢ (Ω.filter (fun b => restrictVec S b = y)) := by
            ext ⟨a, b⟩; simp only [Ω2, Finset.mem_filter, Finset.mem_product, Prod.mk.injEq]; tauto
          rw [hfilt, Finset.sum_product]
          simp only [w2, ← Finset.mul_sum, ← Finset.sum_mul]
        have hnum : pushProb Ω2 w2 (fun p => (C p i, (restrictVec S p.1, restrictVec S p.2))) (true, (x, y))
            = pushProb Ω (unifW Ω) (fun a => (a i, restrictVec S a)) (true, x)
              * pushProb Ω (unifW Ω) (fun b => (b i, restrictVec S b)) (true, y) := by
          unfold pushProb
          have hfilt : Ω2.filter (fun p => (C p i, (restrictVec S p.1, restrictVec S p.2)) = (true, (x, y)))
              = (Ω.filter (fun a => (a i, restrictVec S a) = (true, x)))
                ×ˢ (Ω.filter (fun b => (b i, restrictVec S b) = (true, y))) := by
            ext ⟨a, b⟩
            simp only [Ω2, C, Finset.mem_filter, Finset.mem_product, Prod.mk.injEq, Bool.and_eq_true]
            tauto
          rw [hfilt, Finset.sum_product]
          simp only [w2, ← Finset.mul_sum, ← Finset.sum_mul]
        rw [hden, hnum]
        unfold condProb
        rw [mul_div_mul_comm]
      calc ∑ x ∈ Ω.image (restrictVec S), ∑ y ∈ Ω.image (restrictVec S),
            pushProb Ω2 w2 (fun p => (restrictVec S p.1, restrictVec S p.2)) (x, y)
              * h (pushProb Ω2 w2 (fun p => (C p i, (restrictVec S p.1, restrictVec S p.2))) (true, (x, y))
                  / pushProb Ω2 w2 (fun p => (restrictVec S p.1, restrictVec S p.2)) (x, y))
          = ∑ x ∈ Ω.image (restrictVec S), ∑ y ∈ Ω.image (restrictVec S),
              fibreProb Ω S x * fibreProb Ω S y * h (condProb Ω S i x * condProb Ω S i y) :=
            Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => hterm x hx y hy
        _ = ∑ a ∈ Ω, ∑ b ∈ Ω, unifW Ω a * unifW Ω b * h (Qrv Ω S i a * Qrv Ω S i b) := by
            -- Apply expect_comp_restrictVec twice!
            have h1 : ∀ a ∈ Ω,
                (∑ b ∈ Ω, unifW Ω a * unifW Ω b * h (Qrv Ω S i a * Qrv Ω S i b))
                = unifW Ω a * ∑ y ∈ Ω.image (restrictVec S),
                    fibreProb Ω S y * h (Qrv Ω S i a * condProb Ω S i y) := by
              intro a _
              have := expect_comp_restrictVec Ω S (fun y => h (Qrv Ω S i a * condProb Ω S i y))
              rw [← this, Finset.mul_sum]
              apply Finset.sum_congr rfl; intro b _; unfold Qrv; ring
            rw [Finset.sum_congr rfl h1]
            have h2 := expect_comp_restrictVec Ω S (fun x =>
              ∑ y ∈ Ω.image (restrictVec S), fibreProb Ω S y * h (condProb Ω S i x * condProb Ω S i y))
            rw [show (∑ a ∈ Ω, unifW Ω a * ∑ y ∈ Ω.image (restrictVec S),
                  fibreProb Ω S y * h (Qrv Ω S i a * condProb Ω S i y))
                = ∑ x ∈ Ω.image (restrictVec S), fibreProb Ω S x *
                    ∑ y ∈ Ω.image (restrictVec S), fibreProb Ω S y * h (condProb Ω S i x * condProb Ω S i y)
                from h2]
            apply Finset.sum_congr rfl; intro x _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl; intro y _; ring
    linarith
  calc ∑ k : Fin ord.length,
        (∑ a ∈ Ω, ∑ b ∈ Ω,
          unifW Ω a * unifW Ω b *
            h (Qrv Ω ((ord.take k).toFinset) (ord[k]) a *
               Qrv Ω ((ord.take k).toFinset) (ord[k]) b))
      ≤ ∑ k : Fin ord.length, coordCondEnt Ω2 w2 C (ord[k]) ((ord.take k).toFinset) :=
        Finset.sum_le_sum fun k _ => hstep k
    _ = rvEnt Ω2 w2 C := hchain.symm
    _ ≤ Real.log Ω.card := hHC_le

/-! ### Finite CIID Fair-Sign Protocol (`∑ V_k ≤ log |Ω|`) -/

/-- Perturbed conditional probability for a single coordinate given sign `σ : Bool`. -/
def perturbProb (x : ℝ) (σ : Bool) : ℝ :=
  x + (if σ then (1 : ℝ) else -1) * Real.sqrt tau * x * (1 - x)

lemma perturbProb_mem_Icc {x : ℝ} (_htau0 : 0 ≤ tau) (htau1 : tau ≤ 1)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (σ : Bool) :
    0 ≤ perturbProb x σ ∧ perturbProb x σ ≤ 1 := by
  have hs0 : 0 ≤ Real.sqrt tau := Real.sqrt_nonneg _
  have hs1 : Real.sqrt tau ≤ 1 := by
    calc Real.sqrt tau ≤ Real.sqrt 1 := Real.sqrt_le_sqrt htau1
      _ = 1 := Real.sqrt_one
  have hprod : 0 ≤ x * (1 - x) := mul_nonneg hx0 (by linarith)
  unfold perturbProb
  cases σ
  · -- σ = false: x - √τ x (1 - x)
    simp only [Bool.false_eq_true, ↓reduceIte, neg_one_mul]
    constructor
    · have : Real.sqrt tau * (x * (1 - x)) ≤ 1 * (x * (1 - x)) :=
        mul_le_mul_of_nonneg_right hs1 hprod
      have hsq : 0 ≤ x ^ 2 := sq_nonneg x
      nlinarith
    · have : 0 ≤ Real.sqrt tau * (x * (1 - x)) := mul_nonneg hs0 hprod
      linarith
  · -- σ = true: x + √τ x (1 - x)
    simp only [↓reduceIte, one_mul]
    constructor
    · have : 0 ≤ Real.sqrt tau * (x * (1 - x)) := mul_nonneg hs0 hprod
      linarith
    · have : Real.sqrt tau * (x * (1 - x)) ≤ 1 * (x * (1 - x)) :=
        mul_le_mul_of_nonneg_right hs1 hprod
      have hsq : 0 ≤ (1 - x) ^ 2 := sq_nonneg (1 - x)
      nlinarith

lemma perturbProb_avg (x : ℝ) :
    (perturbProb x true + perturbProb x false) / 2 = x := by
  unfold perturbProb; simp; ring

lemma perturbProb_prod_avg {x y : ℝ} (htau0 : 0 ≤ tau) :
    (perturbProb x true * perturbProb y true + perturbProb x false * perturbProb y false) / 2
      = I_fun x y := by
  unfold perturbProb I_fun
  simp only [↓reduceIte, Bool.false_eq_true, one_mul, neg_one_mul]
  have hsq : Real.sqrt tau * Real.sqrt tau = tau := Real.mul_self_sqrt htau0
  calc ((x + Real.sqrt tau * x * (1 - x)) * (y + Real.sqrt tau * y * (1 - y))
        + (x + -Real.sqrt tau * x * (1 - x)) * (y + -Real.sqrt tau * y * (1 - y))) / 2
      = x * y + (Real.sqrt tau * Real.sqrt tau) * x * y * (1 - x) * (1 - y) := by ring
    _ = x * y * (1 + tau * (1 - x) * (1 - y)) := by rw [hsq]; ring

/-- Helper: `l.take a ⊆ l.take b` whenever `a ≤ b`. -/
lemma mem_take_of_le {α : Type*} {l : List α} {a b : ℕ} (hab : a ≤ b) {x : α} (hx : x ∈ l.take a) :
    x ∈ l.take b := by
  have h1 : (l.take b).take a = l.take a := by rw [List.take_take, min_eq_left hab]
  rw [← h1] at hx
  exact List.mem_of_mem_take hx

/-- Step factor at index `j` of ordering `ord` with sign `b : Bool`. -/
def stepFactor {n : ℕ} (Ω : Finset (Fin n → Bool)) (ord : List (Fin n))
    (j : Fin ord.length) (b : Bool) (v : Fin n → Bool) : ℝ :=
  let q := Qrv Ω ((ord.take j).toFinset) (ord[j]) v
  if v (ord[j]) then perturbProb q b else 1 - perturbProb q b

/-- Unperturbed step factor at index `j` of ordering `ord`. -/
def baseStepFactor {n : ℕ} (Ω : Finset (Fin n → Bool)) (ord : List (Fin n))
    (j : Fin ord.length) (v : Fin n → Bool) : ℝ :=
  let q := Qrv Ω ((ord.take j).toFinset) (ord[j]) v
  if v (ord[j]) then q else 1 - q

/-- Prefix weight up to step `m ≤ ord.length` under signs `σ`. -/
def prefWeight {n : ℕ} (Ω : Finset (Fin n → Bool)) (ord : List (Fin n))
    (σ : Fin ord.length → Bool) (m : ℕ) (v : Fin n → Bool) : ℝ :=
  ∏ j : Fin ord.length, if (j : ℕ) < m then stepFactor Ω ord j (σ j) v else 1

/-- Full vector weight under signs `σ`. -/
def fullWeight {n : ℕ} (Ω : Finset (Fin n → Bool)) (ord : List (Fin n))
    (σ : Fin ord.length → Bool) (v : Fin n → Bool) : ℝ :=
  ∏ j : Fin ord.length, stepFactor Ω ord j (σ j) v

lemma stepFactor_nonneg {n : ℕ} (Ω : Finset (Fin n → Bool)) (ord : List (Fin n))
    (htau0 : 0 ≤ tau) (htau1 : tau ≤ 1) (j : Fin ord.length) (b : Bool) (v : Fin n → Bool) :
    0 ≤ stepFactor Ω ord j b v := by
  unfold stepFactor
  have hq := Qrv_mem_Icc Ω ((ord.take j).toFinset) (ord[j]) v
  have hp := perturbProb_mem_Icc htau0 htau1 hq.1 hq.2 b
  dsimp only
  split_ifs
  · exact hp.1
  · exact sub_nonneg.mpr hp.2

lemma fullWeight_nonneg {n : ℕ} (Ω : Finset (Fin n → Bool)) (ord : List (Fin n))
    (htau0 : 0 ≤ tau) (htau1 : tau ≤ 1) (σ : Fin ord.length → Bool) (v : Fin n → Bool) :
    0 ≤ fullWeight Ω ord σ v :=
  Finset.prod_nonneg fun j _ => stepFactor_nonneg Ω ord htau0 htau1 j (σ j) v

lemma stepFactor_depends_on_prefix {n : ℕ} (Ω : Finset (Fin n → Bool)) (ord : List (Fin n))
    (j : Fin ord.length) (b : Bool) {v w : Fin n → Bool}
    (hpref : restrictVec ((ord.take (j + 1)).toFinset) v = restrictVec ((ord.take (j + 1)).toFinset) w) :
    stepFactor Ω ord j b v = stepFactor Ω ord j b w := by
  have hj_mem : ord[j] ∈ (ord.take (j + 1)).toFinset := by
    rw [List.mem_toFinset]
    have hlt : (j : ℕ) < (ord.take (j + 1)).length := by simp [j.isLt]
    have heq : (ord.take (j + 1))[j]'hlt = ord[j] := List.getElem_take
    rw [← heq]
    exact List.getElem_mem hlt
  have hvi : v (ord[j]) = w (ord[j]) := by
    have h := congr_fun hpref (ord[j])
    simp only [restrictVec, hj_mem, ↓reduceIte] at h
    exact h
  have hsub : (ord.take j).toFinset ⊆ (ord.take (j + 1)).toFinset := by
    intro x hx; rw [List.mem_toFinset] at hx ⊢
    exact mem_take_of_le (Nat.le_succ _) hx
  have hS : restrictVec ((ord.take j).toFinset) v = restrictVec ((ord.take j).toFinset) w := by
    ext x; simp only [restrictVec]
    by_cases hx : x ∈ (ord.take j).toFinset
    · have h := congr_fun hpref x
      simp only [restrictVec, hx, hsub hx, ↓reduceIte] at h ⊢; exact h
    · simp [hx]
  unfold stepFactor Qrv
  rw [hvi, hS]

/-- Key backward-summation identity for `fullWeight`:
    For every `m ≤ ord.length` and every prefix value `y ∈ Ω.image (restrictVec (ord.take m).toFinset)`,
    summing `fullWeight Ω ord σ v` over `v ∈ Ω` matching `y` on `ord.take m` gives `prefWeight Ω ord σ m y`! -/
lemma sum_fibre_fullWeight {n : ℕ} (Ω : Finset (Fin n → Bool)) (ord : List (Fin n))
    (hnd : ord.Nodup) (hcov : ord.toFinset = Finset.univ)
    (σ : Fin ord.length → Bool) :
    ∀ (k : ℕ), k ≤ ord.length →
      ∀ y ∈ Ω.image (restrictVec ((ord.take (ord.length - k)).toFinset)),
        ∑ v ∈ Ω.filter (fun v => restrictVec ((ord.take (ord.length - k)).toFinset) v = y),
            fullWeight Ω ord σ v
          = prefWeight Ω ord σ (ord.length - k) y := by
  intro k
  induction k with
  | zero =>
    intro _ y hy
    simp only [Nat.sub_zero, List.take_length, hcov] at hy ⊢
    rcases Finset.mem_image.mp hy with ⟨v0, hv0Ω, rfl⟩
    rw [restrictVec_univ]
    have hfilt : Ω.filter (fun v => restrictVec Finset.univ v = v0) = {v0} := by
      ext v; simp only [Finset.mem_filter, Finset.mem_singleton, restrictVec_univ]
      exact ⟨fun h => h.2, fun h => ⟨h ▸ hv0Ω, h⟩⟩
    rw [hfilt, Finset.sum_singleton]
    unfold fullWeight prefWeight
    apply Finset.prod_congr rfl; intro j _
    simp [j.isLt]
  | succ k ih =>
    intro hk y hy
    set m := ord.length - (k + 1) with hm_def
    have hm_lt : m < ord.length := by omega
    have hm1 : ord.length - k = m + 1 := by omega
    let j0 : Fin ord.length := ⟨m, hm_lt⟩
    set S := (ord.take m).toFinset
    set S1 := (ord.take (m + 1)).toFinset
    have hS1_eq : S1 = insert (ord[j0]) S := by
      ext x; simp only [S1, S, Finset.mem_insert, List.mem_toFinset, j0]
      rw [List.take_add_one, List.getElem?_eq_getElem hm_lt, Option.toList_some, List.mem_append, List.mem_singleton]
      tauto
    have hord_not_S : ord[j0] ∉ S := by
      intro hmem
      rw [List.mem_toFinset] at hmem
      rcases List.mem_iff_getElem.mp hmem with ⟨t, ht, hteq⟩
      have ht_lt : t < m := by simp only [List.length_take] at ht; omega
      have h1 : ord[t]'(lt_trans ht_lt hm_lt) = ord[m]'hm_lt := by
        simpa [List.getElem_take] using hteq
      have := (List.nodup_iff_injective_getElem.mp hnd) (a₁ := ⟨t, lt_trans ht_lt hm_lt⟩)
        (a₂ := ⟨m, hm_lt⟩) h1
      simp at this; omega
    -- Split the fibre {v ∈ Ω : v_S = y} by v (ord[j0]) ∈ {true, false}!
    let yT : Fin n → Bool := fun x => if x = ord[j0] then true else y x
    let yF : Fin n → Bool := fun x => if x = ord[j0] then false else y x
    have hy_prop : ∀ x, x ∉ S → y x = false := by
      rcases Finset.mem_image.mp hy with ⟨v0, _, rfl⟩
      intro x hx; simp [restrictVec, hx]
    have hsplit : Ω.filter (fun v => restrictVec S v = y)
        = (Ω.filter (fun v => restrictVec S1 v = yT))
          ∪ (Ω.filter (fun v => restrictVec S1 v = yF)) := by
      ext v; simp only [Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro ⟨hvΩ, hvS⟩
        cases hvb : v (ord[j0])
        · right; refine ⟨hvΩ, ?_⟩
          ext x; simp only [restrictVec, hS1_eq, Finset.mem_insert, yF]
          by_cases hx : x = ord[j0]
          · subst hx; simp only [true_or, ↓reduceIte]; exact hvb
          · simp only [hx, false_or, ↓reduceIte]
            have h := congr_fun hvS x; simpa [restrictVec] using h
        · left; refine ⟨hvΩ, ?_⟩
          ext x; simp only [restrictVec, hS1_eq, Finset.mem_insert, yT]
          by_cases hx : x = ord[j0]
          · subst hx; simp only [true_or, ↓reduceIte]; exact hvb
          · simp only [hx, false_or, ↓reduceIte]
            have h := congr_fun hvS x; simpa [restrictVec] using h
      · rintro (⟨hvΩ, hvS1⟩ | ⟨hvΩ, hvS1⟩)
        · refine ⟨hvΩ, ?_⟩; ext x; simp only [restrictVec]
          by_cases hx : x ∈ S
          · have hne : x ≠ ord[j0] := fun h => hord_not_S (h ▸ hx)
            have h := congr_fun hvS1 x
            simp only [restrictVec, hS1_eq, Finset.mem_insert, hx, or_true, ↓reduceIte, yT, hne] at h ⊢
            exact h
          · simp [hx, hy_prop x hx]
        · refine ⟨hvΩ, ?_⟩; ext x; simp only [restrictVec]
          by_cases hx : x ∈ S
          · have hne : x ≠ ord[j0] := fun h => hord_not_S (h ▸ hx)
            have h := congr_fun hvS1 x
            simp only [restrictVec, hS1_eq, Finset.mem_insert, hx, or_true, ↓reduceIte, yF, hne] at h ⊢
            exact h
          · simp [hx, hy_prop x hx]
    have hdisj : Disjoint (Ω.filter (fun v => restrictVec S1 v = yT))
        (Ω.filter (fun v => restrictVec S1 v = yF)) := by
      rw [Finset.disjoint_left]
      intro v hv1 hv2
      have h1 := congr_fun (Finset.mem_filter.mp hv1).2 (ord[j0])
      have h2 := congr_fun (Finset.mem_filter.mp hv2).2 (ord[j0])
      simp [restrictVec, hS1_eq, yT, yF] at h1 h2
      rw [h1] at h2; cases h2
    rw [hsplit, Finset.sum_union hdisj]
    -- Evaluate each half via IH (or 0 if empty)!
    have hpref_step : ∀ z : Fin n → Bool, restrictVec S z = y →
        prefWeight Ω ord σ (m + 1) z = prefWeight Ω ord σ m y * stepFactor Ω ord j0 (σ j0) z := by
      intro z hz
      unfold prefWeight
      have hprod : ∀ j : Fin ord.length,
          (if (j : ℕ) < m + 1 then stepFactor Ω ord j (σ j) z else 1)
          = (if (j : ℕ) < m then stepFactor Ω ord j (σ j) y else 1)
            * (if j = j0 then stepFactor Ω ord j0 (σ j0) z else 1) := by
        intro j
        by_cases hjm : (j : ℕ) < m
        · have hjne : j ≠ j0 := fun h => by subst h; simp [j0] at hjm
          have hjm1 : (j : ℕ) < m + 1 := Nat.lt_succ_of_lt hjm
          simp only [hjm, hjm1, hjne, ↓reduceIte, mul_one]
          apply stepFactor_depends_on_prefix
          have hsub : (ord.take (j + 1)).toFinset ⊆ S := by
            intro x hx; rw [List.mem_toFinset] at hx ⊢
            exact mem_take_of_le (by omega) hx
          ext x; simp only [restrictVec]
          by_cases hx : x ∈ (ord.take (j + 1)).toFinset
          · have h := congr_fun hz x; simp only [restrictVec, hx, hsub hx, ↓reduceIte] at h ⊢; exact h
          · simp [hx]
        · by_cases hjeq : j = j0
          · subst hjeq
            simp [j0]
          · have hjgt : ¬ ((j : ℕ) < m + 1) := by
              intro h; apply hjeq; ext; simp [j0]; omega
            simp [hjm, hjgt, hjeq]
      rw [Finset.prod_congr rfl (fun j _ => hprod j), Finset.prod_mul_distrib]
      congr 1
      rw [Finset.prod_ite_eq' Finset.univ j0 (fun _ => stepFactor Ω ord j0 (σ j0) z)]
      simp
    -- Helper for yT and yF:
    have hq := Qrv_mem_Icc Ω S (ord[j0]) y
    have hyT_S : restrictVec S yT = y := by
      ext x; simp only [restrictVec, yT]
      by_cases hx : x ∈ S
      · have hne : x ≠ ord[j0] := fun h => hord_not_S (h ▸ hx)
        simp only [hx, hne, ↓reduceIte]
      · simp only [hx, ↓reduceIte, hy_prop x hx]
    have hyF_S : restrictVec S yF = y := by
      ext x; simp only [restrictVec, yF]
      by_cases hx : x ∈ S
      · have hne : x ≠ ord[j0] := fun h => hord_not_S (h ▸ hx)
        simp only [hx, hne, ↓reduceIte]
      · simp only [hx, ↓reduceIte, hy_prop x hx]
    have hsumT : ∑ v ∈ Ω.filter (fun v => restrictVec S1 v = yT), fullWeight Ω ord σ v
        = prefWeight Ω ord σ m y * perturbProb (condProb Ω S (ord[j0]) y) (σ j0) := by
      by_cases hmemT : yT ∈ Ω.image (restrictVec S1)
      · have hih := ih (by omega) yT (by rw [hm1]; exact hmemT)
        rw [hm1] at hih
        rw [hih, hpref_step yT hyT_S]
        unfold stepFactor Qrv
        simp only [yT, ↓reduceIte, j0, S, hyT_S]
      · have hemp : Ω.filter (fun v => restrictVec S1 v = yT) = ∅ := by
          rw [Finset.filter_eq_empty_iff]
          intro v hvΩ hEq; exact hmemT (Finset.mem_image.mpr ⟨v, hvΩ, hEq⟩)
        rw [hemp, Finset.sum_empty]
        have hq0 : condProb Ω S (ord[j0]) y = 0 := by
          unfold condProb
          have hnum0 : pushProb Ω (unifW Ω) (fun v => (v (ord[j0]), restrictVec S v)) (true, y) = 0 := by
            unfold pushProb
            apply Finset.sum_eq_zero; intro v hv; exfalso
            have h := Finset.mem_filter.mp hv
            have hvT : restrictVec S1 v = yT := by
              ext x; simp only [restrictVec, hS1_eq, Finset.mem_insert, yT]
              by_cases hx : x = ord[j0]
              · subst hx; simp only [true_or, ↓reduceIte]; exact (Prod.mk.inj h.2).1
              · simp only [hx, false_or, ↓reduceIte]
                have h2 := congr_fun (Prod.mk.inj h.2).2 x; simpa [restrictVec] using h2
            exact hmemT (Finset.mem_image.mpr ⟨v, h.1, hvT⟩)
          rw [hnum0, zero_div]
        rw [hq0]; unfold perturbProb; ring
    have hsumF : ∑ v ∈ Ω.filter (fun v => restrictVec S1 v = yF), fullWeight Ω ord σ v
        = prefWeight Ω ord σ m y * (1 - perturbProb (condProb Ω S (ord[j0]) y) (σ j0)) := by
      by_cases hmemF : yF ∈ Ω.image (restrictVec S1)
      · have hih := ih (by omega) yF (by rw [hm1]; exact hmemF)
        rw [hm1] at hih
        rw [hih, hpref_step yF hyF_S]
        unfold stepFactor Qrv
        simp only [yF, ↓reduceIte, Bool.false_eq_true, j0, S, hyF_S]
      · have hemp : Ω.filter (fun v => restrictVec S1 v = yF) = ∅ := by
          rw [Finset.filter_eq_empty_iff]
          intro v hvΩ hEq; exact hmemF (Finset.mem_image.mpr ⟨v, hvΩ, hEq⟩)
        rw [hemp, Finset.sum_empty]
        have hq1 : condProb Ω S (ord[j0]) y = 1 := by
          unfold condProb
          have hnum_eq : pushProb Ω (unifW Ω) (fun v => (v (ord[j0]), restrictVec S v)) (true, y)
              = fibreProb Ω S y := by
            unfold fibreProb pushProb; congr 1; ext v
            simp only [Finset.mem_filter, Prod.mk.injEq]
            constructor
            · rintro ⟨hvΩ, _, hvS⟩; exact ⟨hvΩ, hvS⟩
            · rintro ⟨hvΩ, hvS⟩
              refine ⟨hvΩ, ?_, hvS⟩
              cases hvb : v (ord[j0])
              · exfalso
                have hvF : restrictVec S1 v = yF := by
                  ext x; simp only [restrictVec, hS1_eq, Finset.mem_insert, yF]
                  by_cases hx : x = ord[j0]
                  · subst hx; simp only [true_or, ↓reduceIte]; exact hvb
                  · simp only [hx, false_or, ↓reduceIte]
                    have h2 := congr_fun hvS x; simpa [restrictVec] using h2
                exact hmemF (Finset.mem_image.mpr ⟨v, hvΩ, hvF⟩)
              · rfl
          rw [hnum_eq, div_self (ne_of_gt (fibreProb_pos_of_mem_image Ω S hy))]
        rw [hq1]; unfold perturbProb; ring
    rw [hsumT, hsumF]
    ring

lemma sum_fullWeight {n : ℕ} (Ω : Finset (Fin n → Bool)) (hΩ : Ω.Nonempty)
    (ord : List (Fin n)) (hnd : ord.Nodup) (hcov : ord.toFinset = Finset.univ)
    (σ : Fin ord.length → Bool) :
    ∑ v ∈ Ω, fullWeight Ω ord σ v = 1 := by
  have h0 := sum_fibre_fullWeight Ω ord hnd hcov σ ord.length le_rfl (fun _ => false)
  have hmem : (fun _ : Fin n => false) ∈ Ω.image (restrictVec ((ord.take (ord.length - ord.length)).toFinset)) := by
    rcases hΩ with ⟨v0, hv0⟩
    refine Finset.mem_image.mpr ⟨v0, hv0, ?_⟩
    simp [restrictVec_empty]
  specialize h0 hmem
  simp only [Nat.sub_self, List.take_zero, List.toFinset_nil, restrictVec_empty, Finset.filter_true] at h0
  rw [h0]
  unfold prefWeight
  simp

/-- Averaging `prefWeight Ω ord σ m y` over all sign vectors `σ : Fin ord.length → Bool`
    recovers the exact unperturbed fibre probability `fibreProb Ω (ord.take m).toFinset y`! -/
lemma avg_prefWeight {n : ℕ} (Ω : Finset (Fin n → Bool)) (hΩ : Ω.Nonempty)
    (ord : List (Fin n)) (hnd : ord.Nodup) (m : ℕ) (hm : m ≤ ord.length)
    (y : Fin n → Bool) (hy : y ∈ Ω.image (restrictVec ((ord.take m).toFinset))) :
    (∑ σ : Fin ord.length → Bool, prefWeight Ω ord σ m y) / (2 : ℝ) ^ ord.length
      = fibreProb Ω ((ord.take m).toFinset) y := by
  -- First, by Fintype.prod_sum, ∑_σ ∏_j f_j(σ j) = ∏_j (∑_{b : Bool} f_j b)!
  have hswap : ∑ σ : Fin ord.length → Bool, prefWeight Ω ord σ m y
      = ∏ j : Fin ord.length,
          ∑ b : Bool, (if (j : ℕ) < m then stepFactor Ω ord j b y else 1) := by
    unfold prefWeight
    rw [Fintype.prod_sum (fun (j : Fin ord.length) (b : Bool) =>
      if (j : ℕ) < m then stepFactor Ω ord j b y else 1)]
  rw [hswap]
  have hdiv : (∏ j : Fin ord.length, ∑ b : Bool, (if (j : ℕ) < m then stepFactor Ω ord j b y else 1))
      / (2 : ℝ) ^ ord.length
      = ∏ j : Fin ord.length,
          (if (j : ℕ) < m then baseStepFactor Ω ord j y else 1) := by
    have h2 : (2 : ℝ) ^ ord.length = ∏ _j : Fin ord.length, (2 : ℝ) := by simp
    rw [h2, ← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro j _
    by_cases hj : (j : ℕ) < m
    · simp only [hj, ↓reduceIte, Fintype.sum_bool, stepFactor, baseStepFactor]
      cases y (ord[j])
      · simp only [Bool.false_eq_true, ↓reduceIte]
        have := perturbProb_avg (Qrv Ω ((ord.take j).toFinset) (ord[j]) y)
        linarith
      · simp only [↓reduceIte]
        exact perturbProb_avg _
    · simp only [hj, ↓reduceIte, Fintype.sum_bool]; norm_num
  rw [hdiv]
  -- Now prove by induction on m that ∏_{j < m} baseStepFactor j y = fibreProb Ω (ord.take m).toFinset y!
  clear hswap hdiv
  induction m generalizing y with
  | zero =>
    simp only [Nat.not_lt_zero, ↓reduceIte, Finset.prod_const_one, List.take_zero, List.toFinset_nil] at hy ⊢
    rcases Finset.mem_image.mp hy with ⟨v0, _, rfl⟩
    rw [restrictVec_empty]
    unfold fibreProb pushProb
    have hfilt : Ω.filter (fun v => restrictVec ∅ v = fun _ => false) = Ω := by
      ext v; simp [restrictVec_empty]
    rw [hfilt, sum_unifW hΩ]
  | succ m ih =>
    have hm_lt : m < ord.length := Nat.lt_of_succ_le hm
    let j0 : Fin ord.length := ⟨m, hm_lt⟩
    set S := (ord.take m).toFinset
    set S1 := (ord.take (m + 1)).toFinset
    have hS1_eq : S1 = insert (ord[j0]) S := by
      ext x; simp only [S1, S, Finset.mem_insert, List.mem_toFinset, j0]
      rw [List.take_add_one, List.getElem?_eq_getElem hm_lt, Option.toList_some, List.mem_append, List.mem_singleton]
      tauto
    have hord_not_S : ord[j0] ∉ S := by
      intro hmem; rw [List.mem_toFinset] at hmem
      rcases List.mem_iff_getElem.mp hmem with ⟨t, ht, hteq⟩
      have ht_lt : t < m := by simp only [List.length_take] at ht; omega
      have h1 : ord[t]'(lt_trans ht_lt hm_lt) = ord[m]'hm_lt := by simpa [List.getElem_take] using hteq
      have := (List.nodup_iff_injective_getElem.mp hnd) (a₁ := ⟨t, lt_trans ht_lt hm_lt⟩) (a₂ := ⟨m, hm_lt⟩) h1
      simp at this; omega
    let y0 := restrictVec S y
    have hy0_mem : y0 ∈ Ω.image (restrictVec S) := by
      rcases Finset.mem_image.mp hy with ⟨v0, hv0, rfl⟩
      refine Finset.mem_image.mpr ⟨v0, hv0, ?_⟩
      ext x; simp only [y0, restrictVec]
      by_cases hx : x ∈ S
      · simp [hx, hS1_eq]
      · simp [hx]
    have hprod_split : (∏ j : Fin ord.length, if (j : ℕ) < m + 1 then baseStepFactor Ω ord j y else 1)
        = (∏ j : Fin ord.length, if (j : ℕ) < m then baseStepFactor Ω ord j y0 else 1)
          * baseStepFactor Ω ord j0 y := by
      have hterm : ∀ j : Fin ord.length,
          (if (j : ℕ) < m + 1 then baseStepFactor Ω ord j y else 1)
          = (if (j : ℕ) < m then baseStepFactor Ω ord j y0 else 1)
            * (if j = j0 then baseStepFactor Ω ord j0 y else 1) := by
        intro j
        by_cases hjm : (j : ℕ) < m
        · have hjne : j ≠ j0 := fun h => by subst h; simp [j0] at hjm
          have hjm1 : (j : ℕ) < m + 1 := Nat.lt_succ_of_lt hjm
          simp only [hjm, hjm1, hjne, ↓reduceIte, mul_one]
          have hsub : (ord.take j).toFinset ⊆ S := by
            intro x hx; rw [List.mem_toFinset] at hx ⊢
            exact mem_take_of_le (by omega) hx
          have hjS : ord[j] ∈ S := by
            rw [List.mem_toFinset]
            have hlt : (j : ℕ) < (ord.take m).length := by simp only [List.length_take, lt_min_iff]; exact ⟨hjm, j.isLt⟩
            have hget : (ord.take m)[j]'hlt = ord[j] := List.getElem_take
            rw [← hget]
            exact List.getElem_mem hlt
          have hy_j : y (ord[j]) = y0 (ord[j]) := by simp only [y0, restrictVec, hjS, ↓reduceIte]
          have hy_S : restrictVec ((ord.take j).toFinset) y = restrictVec ((ord.take j).toFinset) y0 := by
            ext x; simp only [restrictVec, y0]
            by_cases hx : x ∈ (ord.take j).toFinset
            · simp [hx, hsub hx]
            · simp [hx]
          unfold baseStepFactor Qrv
          rw [hy_j, hy_S]
        · by_cases hjeq : j = j0
          · subst hjeq; simp [j0]
          · have hjgt : ¬ ((j : ℕ) < m + 1) := by intro h; apply hjeq; ext; simp [j0]; omega
            simp [hjm, hjgt, hjeq]
      rw [Finset.prod_congr rfl (fun j _ => hterm j), Finset.prod_mul_distrib]
      congr 1
      rw [Finset.prod_ite_eq' Finset.univ j0 (fun _ => baseStepFactor Ω ord j0 y)]
      simp
    rw [hprod_split, ih (Nat.le_of_succ_le hm) y0 hy0_mem]
    -- Now show fibreProb Ω S y0 * baseStepFactor Ω ord j0 y = fibreProb Ω S1 y!
    have hpos0 : 0 < fibreProb Ω S y0 := fibreProb_pos_of_mem_image Ω S hy0_mem
    have hbase : baseStepFactor Ω ord j0 y =
        if y (ord[j0]) then condProb Ω S (ord[j0]) y0 else 1 - condProb Ω S (ord[j0]) y0 := rfl
    rw [hbase]
    have hfilt_pair : ∀ b : Bool,
        Ω.filter (fun v => (v (ord[j0]), restrictVec S v) = (b, y0))
        = Ω.filter (fun v => restrictVec S1 v = (fun x => if x = ord[j0] then b else y0 x)) := by
      intro b; ext v; simp only [Finset.mem_filter, Prod.mk.injEq]
      constructor
      · rintro ⟨hvΩ, hvb, hvS⟩; refine ⟨hvΩ, ?_⟩
        ext x; simp only [restrictVec, hS1_eq, Finset.mem_insert]
        by_cases hx : x = ord[j0]
        · subst hx; simp only [true_or, ↓reduceIte]; exact hvb
        · simp only [hx, false_or, ↓reduceIte]
          have := congr_fun hvS x; simpa [restrictVec] using this
      · rintro ⟨hvΩ, hvS1⟩
        refine ⟨hvΩ, ?_, ?_⟩
        · have := congr_fun hvS1 (ord[j0]); simpa [restrictVec, hS1_eq] using this
        · ext x; simp only [restrictVec]
          by_cases hx : x ∈ S
          · have hne : x ≠ ord[j0] := fun h => hord_not_S (h ▸ hx)
            have := congr_fun hvS1 x
            simp only [restrictVec, hS1_eq, Finset.mem_insert, hx, or_true, ↓reduceIte, hne] at this
            simp only [hx, ↓reduceIte]
            exact this
          · simp [hx, y0, restrictVec]
    have hy_eq : (fun x => if x = ord[j0] then y (ord[j0]) else y0 x) = y := by
      rcases Finset.mem_image.mp hy with ⟨v0, _, rfl⟩
      ext x; simp only [y0, restrictVec, hS1_eq, Finset.mem_insert]
      by_cases hx : x = ord[j0]
      · subst hx; simp only [true_or, ↓reduceIte]
      · by_cases hxS : x ∈ S <;> simp only [hx, hxS, false_or, ↓reduceIte]
    cases hyb : y (ord[j0])
    · -- y (ord[j0]) = false
      simp only [Bool.false_eq_true, ↓reduceIte]
      have h1 : fibreProb Ω S y0 * (1 - condProb Ω S (ord[j0]) y0)
          = fibreProb Ω S y0 - pushProb Ω (unifW Ω) (fun v => (v (ord[j0]), restrictVec S v)) (true, y0) := by
        unfold condProb; rw [mul_sub, mul_one, mul_div_cancel₀ _ (ne_of_gt hpos0)]
      rw [h1]
      have hsum_tf := sum_pushProb_pair Ω (unifW Ω) (fun v => v (ord[j0])) (restrictVec S) y0
      have hsub : ∑ x ∈ (Finset.univ : Finset Bool), pushProb Ω (unifW Ω) (fun v => (v (ord[j0]), restrictVec S v)) (x, y0)
          = ∑ x ∈ Ω.image (fun v => v (ord[j0])), pushProb Ω (unifW Ω) (fun v => (v (ord[j0]), restrictVec S v)) (x, y0) := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro x _ hnot
        unfold pushProb; apply Finset.sum_eq_zero; intro v hv; exfalso
        have h := Finset.mem_filter.mp hv
        exact hnot (Finset.mem_image.mpr ⟨v, h.1, (Prod.mk.inj h.2).1⟩)
      rw [← hsub, Fintype.sum_bool] at hsum_tf
      have hF : pushProb Ω (unifW Ω) (fun v => (v (ord[j0]), restrictVec S v)) (false, y0) = fibreProb Ω S1 y := by
        unfold fibreProb pushProb
        rw [hfilt_pair false, ← hyb, hy_eq]
      change fibreProb Ω S y0 - pushProb Ω (unifW Ω) (fun v => (v (ord[j0]), restrictVec S v)) (true, y0) = fibreProb Ω S1 y
      unfold fibreProb at hF ⊢
      linarith
    · -- y (ord[j0]) = true
      simp only [↓reduceIte]
      unfold condProb
      rw [mul_div_cancel₀ _ (ne_of_gt hpos0)]
      unfold fibreProb pushProb
      rw [hfilt_pair true, ← hyb, hy_eq]

/-- **CIID Fair-Sign Protocol Bound**:
    For every nonempty `AndClosed` family `Ω`, complete nodup order `ord`, and `0 ≤ tau ≤ 1`,
    using the finite CIID auxiliary variable `Z = σ_{<k}` (`Fin k → Bool`) with conditional law
    `μ_{k, z}(y) = prefWeight Ω ord z k y` on `Ω.image (restrictVec (ord.take k).toFinset)`,
    we have:
      `∑ k : Fin ord.length, V_k ≤ Real.log Ω.card`,
    where `V_k = (1 / 2^k) ∑_{z : Fin k → Bool} ∑_{x, y} μ_{k, z}(x) μ_{k, z}(y) h(I_fun (q_k x) (q_k y))`. -/
lemma ciid_protocol_bound {n : ℕ} (Ω : Finset (Fin n → Bool)) (hΩ : Ω.Nonempty)
    (hAC : AndClosed Ω) (ord : List (Fin n)) (hnd : ord.Nodup) (hcov : ord.toFinset = Finset.univ)
    (htau0 : 0 ≤ tau) (htau1 : tau ≤ 1) :
    ∑ k : Fin ord.length,
      (∑ σ : Fin ord.length → Bool,
        ∑ x ∈ Ω.image (restrictVec ((ord.take k).toFinset)),
          ∑ y ∈ Ω.image (restrictVec ((ord.take k).toFinset)),
            (1 / (2 : ℝ) ^ ord.length)
              * prefWeight Ω ord σ k x * prefWeight Ω ord σ k y
              * h (I_fun (condProb Ω ((ord.take k).toFinset) (ord[k]) x)
                         (condProb Ω ((ord.take k).toFinset) (ord[k]) y)))
      ≤ Real.log Ω.card := by
  let SigmaSet := (Finset.univ : Finset (Fin ord.length → Bool))
  let Ξ := SigmaSet ×ˢ (Ω ×ˢ Ω)
  let W : (Fin ord.length → Bool) × (Fin n → Bool) × (Fin n → Bool) → ℝ :=
    fun p => (1 / (2 : ℝ) ^ ord.length) * fullWeight Ω ord p.1 p.2.1 * fullWeight Ω ord p.1 p.2.2
  let C : (Fin ord.length → Bool) × (Fin n → Bool) × (Fin n → Bool) → (Fin n → Bool) :=
    fun p i => p.2.1 i && p.2.2 i
  have hW_nn : ∀ p ∈ Ξ, 0 ≤ W p := by
    intro ⟨σ, a, b⟩ _
    unfold W
    exact mul_nonneg (mul_nonneg (by positivity) (fullWeight_nonneg Ω ord htau0 htau1 σ a))
      (fullWeight_nonneg Ω ord htau0 htau1 σ b)
  have hW_sum : ∑ p ∈ Ξ, W p = 1 := by
    simp only [Ξ, SigmaSet, W, Finset.sum_product]
    have hinner : ∀ σ : Fin ord.length → Bool,
        ∑ a ∈ Ω, ∑ b ∈ Ω, (1 / (2 : ℝ) ^ ord.length) * fullWeight Ω ord σ a * fullWeight Ω ord σ b
        = 1 / (2 : ℝ) ^ ord.length := by
      intro σ
      calc ∑ a ∈ Ω, ∑ b ∈ Ω, (1 / (2 : ℝ) ^ ord.length) * fullWeight Ω ord σ a * fullWeight Ω ord σ b
          = (1 / (2 : ℝ) ^ ord.length) * (∑ a ∈ Ω, fullWeight Ω ord σ a) * (∑ b ∈ Ω, fullWeight Ω ord σ b) := by
            rw [mul_assoc, Finset.mul_sum]; simp_rw [Finset.sum_mul, Finset.mul_sum]
            apply Finset.sum_congr rfl; intro a _
            apply Finset.sum_congr rfl; intro b _; ring
        _ = 1 / (2 : ℝ) ^ ord.length := by
            rw [sum_fullWeight Ω hΩ ord hnd hcov σ, mul_one, mul_one]
    simp_rw [hinner]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    have h2 : (2 : ℝ) ^ ord.length ≠ 0 := by positivity
    field_simp [h2]
  have hΞ_ne : Ξ.Nonempty := (Finset.univ_nonempty).product (hΩ.product hΩ)
  -- Step 1: H(C) ≤ log |Ω|
  have hC_sub : Ξ.image C ⊆ Ω := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨⟨σ, a, b⟩, hp, rfl⟩
    rcases Finset.mem_product.mp hp with ⟨_, hab⟩
    rcases Finset.mem_product.mp hab with ⟨ha, hb⟩
    exact hAC a ha b hb
  have hHC_le : rvEnt Ξ W C ≤ Real.log Ω.card := by
    have h1 := rvEnt_le_log_card Ξ W hW_nn hW_sum hΞ_ne C
    have hcard_le : ((Ξ.image C).card : ℝ) ≤ (Ω.card : ℝ) := by
      exact_mod_cast Finset.card_le_card hC_sub
    have himg_pos : (0 : ℝ) < (Ξ.image C).card := Nat.cast_pos.mpr (hΞ_ne.image C).card_pos
    exact le_trans h1 (Real.log_le_log himg_pos hcard_le)
  -- Step 2: Chain rule for H(C) along ord
  have hchain : rvEnt Ξ W C =
      ∑ k : Fin ord.length, coordCondEnt Ξ W C (ord[k]) ((ord.take k).toFinset) := by
    have h1 := subEnt_append_list Ξ W C ∅ ord hnd (by simp)
    simp only [Finset.empty_union, hcov, subEnt_univ, subEnt_empty Ξ W hW_sum C, sub_zero] at h1
    exact h1
  -- Step 3: For each k, condition on (σ_{<k}, a_{<k}, b_{<k}) where σ_{<k} zeroes coordinates ≥ k
  have hstep : ∀ k : Fin ord.length,
      (∑ σ : Fin ord.length → Bool,
        ∑ x ∈ Ω.image (restrictVec ((ord.take k).toFinset)),
          ∑ y ∈ Ω.image (restrictVec ((ord.take k).toFinset)),
            (1 / (2 : ℝ) ^ ord.length)
              * prefWeight Ω ord σ k x * prefWeight Ω ord σ k y
              * h (I_fun (condProb Ω ((ord.take k).toFinset) (ord[k]) x)
                         (condProb Ω ((ord.take k).toFinset) (ord[k]) y)))
        ≤ coordCondEnt Ξ W C (ord[k]) ((ord.take k).toFinset) := by
    intro k
    set S := (ord.take k).toFinset
    set i := ord[k]
    let mask : (Fin ord.length → Bool) → (Fin ord.length → Bool) :=
      fun σ j => if (j : ℕ) < k then σ j else false
    let Gmap : ((Fin ord.length → Bool) × (Fin n → Bool) × (Fin n → Bool)) →
        ((Fin ord.length → Bool) × (Fin n → Bool) × (Fin n → Bool)) :=
      fun p => (mask p.1, restrictVec S p.2.1, restrictVec S p.2.2)
    let ψ : ((Fin ord.length → Bool) × (Fin n → Bool) × (Fin n → Bool)) → (Fin n → Bool) :=
      fun q t => q.2.1 t && q.2.2 t
    have hcomp : (fun p => restrictVec S (C p)) = (fun p => ψ (Gmap p)) := by
      ext ⟨σ, a, b⟩ t
      simp only [restrictVec, C, ψ, Gmap]
      by_cases ht : t ∈ S <;> simp [ht]
    have hmono : condRvEnt Ξ W (fun p => C p i) Gmap ≤ coordCondEnt Ξ W C i S := by
      unfold coordCondEnt
      rw [hcomp]
      exact condRvEnt_le_of_comp Ξ W hW_nn (fun p => C p i) Gmap ψ
    -- Evaluate condRvEnt Ξ W (fun p => C p i) Gmap via condRvEnt_bool_eq_sum_h!
    rw [condRvEnt_bool_eq_sum_h Ξ W hW_nn] at hmono
    -- Note that prefWeight Ω ord σ k x depends ONLY on mask σ!
    have hpref_mask : ∀ σ x, prefWeight Ω ord σ k x = prefWeight Ω ord (mask σ) k x := by
      intro σ x; unfold prefWeight
      apply Finset.prod_congr rfl; intro j _
      by_cases hj : (j : ℕ) < k
      · simp only [hj, ↓reduceIte, mask]
      · simp [hj]
    -- Compute pushProb for any (τ, x, y) in Ξ.image Gmap:
    let Mset := SigmaSet.image mask
    have hGimg : Ξ.image Gmap = Mset ×ˢ ((Ω.image (restrictVec S)) ×ˢ (Ω.image (restrictVec S))) := by
      ext ⟨τ, x, y⟩
      simp only [Ξ, Mset, Gmap, Finset.mem_image, Finset.mem_product, Prod.exists, Prod.mk.injEq]
      constructor
      · rintro ⟨σ, a, b, ⟨hσ, ha, hb⟩, hτ, hx, hy⟩
        exact ⟨⟨σ, hσ, hτ⟩, ⟨a, ha, hx⟩, ⟨b, hb, hy⟩⟩
      · rintro ⟨⟨σ, hσ, hτ⟩, ⟨a, ha, hx⟩, ⟨b, hb, hy⟩⟩
        exact ⟨σ, a, b, ⟨hσ, ha, hb⟩, hτ, hx, hy⟩
    rw [hGimg] at hmono
    -- For each τ ∈ Mset, how many σ ∈ SigmaSet satisfy mask σ = τ? And what are their values at k?
    have hfib_den : ∀ τ ∈ Mset, ∀ x ∈ Ω.image (restrictVec S), ∀ y ∈ Ω.image (restrictVec S),
        pushProb Ξ W Gmap (τ, x, y)
        = (∑ σ ∈ SigmaSet.filter (fun σ => mask σ = τ), (1 / (2 : ℝ) ^ ord.length))
          * prefWeight Ω ord τ k x * prefWeight Ω ord τ k y := by
      intro τ _ x hx y hy
      unfold pushProb
      have hfilt : Ξ.filter (fun p => Gmap p = (τ, x, y))
          = (SigmaSet.filter (fun σ => mask σ = τ))
            ×ˢ ((Ω.filter (fun a => restrictVec S a = x))
                ×ˢ (Ω.filter (fun b => restrictVec S b = y))) := by
        ext ⟨σ, a, b⟩
        simp only [Ξ, Gmap, Finset.mem_filter, Finset.mem_product, Prod.mk.injEq]
        tauto
      rw [hfilt, Finset.sum_product]
      have hinner : ∀ σ ∈ SigmaSet.filter (fun σ => mask σ = τ),
          ∑ ab ∈ (Ω.filter (fun a => restrictVec S a = x)) ×ˢ (Ω.filter (fun b => restrictVec S b = y)),
            W (σ, ab)
          = (1 / (2 : ℝ) ^ ord.length) * prefWeight Ω ord τ k x * prefWeight Ω ord τ k y := by
        intro σ hσ
        have hmask : mask σ = τ := (Finset.mem_filter.mp hσ).2
        rw [Finset.sum_product]
        have hfx := sum_fibre_fullWeight Ω ord hnd hcov σ (ord.length - k) (by omega)
        have hsubk : ord.length - (ord.length - k) = k := by omega
        rw [hsubk] at hfx
        calc ∑ a ∈ Ω.filter (fun a => restrictVec S a = x),
              ∑ b ∈ Ω.filter (fun b => restrictVec S b = y),
                (1 / (2 : ℝ) ^ ord.length) * fullWeight Ω ord σ a * fullWeight Ω ord σ b
            = (1 / (2 : ℝ) ^ ord.length)
              * (∑ a ∈ Ω.filter (fun a => restrictVec S a = x), fullWeight Ω ord σ a)
              * (∑ b ∈ Ω.filter (fun b => restrictVec S b = y), fullWeight Ω ord σ b) := by
              rw [mul_assoc, Finset.mul_sum]; simp_rw [Finset.sum_mul, Finset.mul_sum]
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl; intro a _
              apply Finset.sum_congr rfl; intro b _; ring
          _ = (1 / (2 : ℝ) ^ ord.length) * prefWeight Ω ord σ k x * prefWeight Ω ord σ k y := by
              rw [hfx x hx, hfx y hy]
          _ = (1 / (2 : ℝ) ^ ord.length) * prefWeight Ω ord τ k x * prefWeight Ω ord τ k y := by
              rw [hpref_mask σ x, hpref_mask σ y, hmask]
      rw [Finset.sum_congr rfl hinner, ← Finset.sum_mul, ← Finset.sum_mul]
    -- Similarly compute numerator pushProb (C p i = true, Gmap p = (τ, x, y)):
    have hfib_num : ∀ τ ∈ Mset, ∀ x ∈ Ω.image (restrictVec S), ∀ y ∈ Ω.image (restrictVec S),
        pushProb Ξ W (fun p => (C p i, Gmap p)) (true, (τ, x, y))
        = (∑ σ ∈ SigmaSet.filter (fun σ => mask σ = τ), (1 / (2 : ℝ) ^ ord.length))
          * prefWeight Ω ord τ k x * prefWeight Ω ord τ k y
          * I_fun (condProb Ω S i x) (condProb Ω S i y) := by
      intro τ _ x hx y hy
      unfold pushProb
      have hfilt : Ξ.filter (fun p => (C p i, Gmap p) = (true, (τ, x, y)))
          = (SigmaSet.filter (fun σ => mask σ = τ))
            ×ˢ ((Ω.filter (fun a => a i = true ∧ restrictVec S a = x))
                ×ˢ (Ω.filter (fun b => b i = true ∧ restrictVec S b = y))) := by
        ext ⟨σ, a, b⟩
        simp only [Ξ, C, Gmap, Finset.mem_filter, Finset.mem_product, Prod.mk.injEq, Bool.and_eq_true]
        tauto
      rw [hfilt, Finset.sum_product]
      -- First prove for any σ with mask σ = τ and x ∈ Ω.image (restrictVec S):
      -- ∑_{a ∈ Ω, a i = true, a_S = x} fullWeight Ω ord σ a = prefWeight Ω ord τ k x * perturbProb (condProb Ω S i x) (σ k)!
      have htrue_sum : ∀ σ ∈ SigmaSet.filter (fun σ => mask σ = τ), ∀ z ∈ Ω.image (restrictVec S),
          ∑ a ∈ Ω.filter (fun a => a i = true ∧ restrictVec S a = z), fullWeight Ω ord σ a
          = prefWeight Ω ord τ k z * perturbProb (condProb Ω S i z) (σ k) := by
        intro σ hσ z hz
        have hmask : mask σ = τ := (Finset.mem_filter.mp hσ).2
        set S1 := (ord.take (k + 1)).toFinset
        have hS1_eq : S1 = insert i S := by
          ext t; simp only [S1, S, i, Finset.mem_insert, List.mem_toFinset]
          rw [List.take_add_one, List.getElem?_eq_getElem k.isLt, Option.toList_some, List.mem_append, List.mem_singleton]
          tauto
        have hi_not_S : i ∉ S := by
          intro hmem; rw [List.mem_toFinset] at hmem
          rcases List.mem_iff_getElem.mp hmem with ⟨t, ht, hteq⟩
          have ht_lt : t < (k : ℕ) := by simp only [List.length_take] at ht; omega
          have h1 : ord[t]'(lt_trans ht_lt k.isLt) = ord[k] := by simpa [List.getElem_take, i] using hteq
          have h2 := (List.nodup_iff_injective_getElem.mp hnd) (a₁ := ⟨t, lt_trans ht_lt k.isLt⟩) (a₂ := k) h1
          have h3 := congr_arg Fin.val h2
          dsimp at h3; omega
        let zT : Fin n → Bool := fun t => if t = i then true else z t
        have hz_prop : ∀ t, t ∉ S → z t = false := by
          rcases Finset.mem_image.mp hz with ⟨v0, _, rfl⟩
          intro t ht; simp [restrictVec, ht]
        have hfilt_zT : Ω.filter (fun a => a i = true ∧ restrictVec S a = z)
            = Ω.filter (fun a => restrictVec S1 a = zT) := by
          ext a; simp only [Finset.mem_filter]
          constructor
          · rintro ⟨haΩ, hai, haS⟩; refine ⟨haΩ, ?_⟩
            ext t; simp only [restrictVec, hS1_eq, Finset.mem_insert, zT]
            by_cases ht : t = i
            · subst ht; simp [hai]
            · simp only [ht, false_or, ↓reduceIte]
              have := congr_fun haS t; simpa [restrictVec] using this
          · rintro ⟨haΩ, haS1⟩; refine ⟨haΩ, ?_, ?_⟩
            · have := congr_fun haS1 i; simpa [restrictVec, hS1_eq, zT] using this
            · ext t; simp only [restrictVec]
              by_cases ht : t ∈ S
              · have hne : t ≠ i := fun h => hi_not_S (h ▸ ht)
                have := congr_fun haS1 t; simpa [restrictVec, hS1_eq, ht, zT, hne] using this
              · simp [ht, hz_prop t ht]
        rw [hfilt_zT]
        by_cases hmemT : zT ∈ Ω.image (restrictVec S1)
        · have hsf := sum_fibre_fullWeight Ω ord hnd hcov σ (ord.length - (k + 1)) (by omega)
          have hsub : ord.length - (ord.length - (k + 1)) = (k : ℕ) + 1 := by omega
          rw [hsub] at hsf
          rw [hsf zT hmemT]
          have hzT_S : restrictVec S zT = z := by
            ext t; simp only [restrictVec, zT]
            by_cases ht : t ∈ S
            · have hne : t ≠ i := fun h => hi_not_S (h ▸ ht)
              simp [ht, hne]
            · simp [ht, hz_prop t ht]
          -- Split prefWeight at k+1 into prefWeight at k * stepFactor at k
          unfold prefWeight
          have hterm : ∀ j : Fin ord.length,
              (if (j : ℕ) < (k : ℕ) + 1 then stepFactor Ω ord j (σ j) zT else 1)
              = (if (j : ℕ) < k then stepFactor Ω ord j (τ j) z else 1)
                * (if j = k then stepFactor Ω ord k (σ k) zT else 1) := by
            intro j
            by_cases hjk : (j : ℕ) < k
            · have hjne : j ≠ k := fun h => by subst h; exact Nat.lt_irrefl _ hjk
              have hjk1 : (j : ℕ) < (k : ℕ) + 1 := Nat.lt_succ_of_lt hjk
              have hτj : τ j = σ j := by rw [← hmask]; simp only [mask, hjk, ↓reduceIte]
              simp only [hjk, hjk1, hjne, ↓reduceIte, mul_one, hτj]
              apply stepFactor_depends_on_prefix
              have hsub2 : (ord.take (j + 1)).toFinset ⊆ S := by
                intro t ht; rw [List.mem_toFinset] at ht ⊢
                exact mem_take_of_le (by omega) ht
              ext t; simp only [restrictVec]
              by_cases ht : t ∈ (ord.take (j + 1)).toFinset
              · have := congr_fun hzT_S t; simpa [restrictVec, ht, hsub2 ht] using this
              · simp [ht]
            · by_cases hjeq : j = k
              · subst hjeq; simp
              · have hjgt : ¬ ((j : ℕ) < (k : ℕ) + 1) := by
                  intro h; apply hjeq; ext; omega
                simp [hjk, hjgt, hjeq]
          rw [Finset.prod_congr rfl (fun j _ => hterm j), Finset.prod_mul_distrib,
              Finset.prod_ite_eq' Finset.univ k (fun _ => stepFactor Ω ord k (σ k) zT)]
          simp only [Finset.mem_univ, ↓reduceIte]
          congr 1
          unfold stepFactor Qrv
          rw [hzT_S]
          simp [zT, i, S]
        · have hemp : Ω.filter (fun a => restrictVec S1 a = zT) = ∅ := by
            rw [Finset.filter_eq_empty_iff]
            intro a ha hEq; exact hmemT (Finset.mem_image.mpr ⟨a, ha, hEq⟩)
          rw [hemp, Finset.sum_empty]
          have hq0 : condProb Ω S i z = 0 := by
            unfold condProb
            have hnum0 : pushProb Ω (unifW Ω) (fun a => (a i, restrictVec S a)) (true, z) = 0 := by
              unfold pushProb; apply Finset.sum_eq_zero; intro a ha; exfalso
              have h := Finset.mem_filter.mp ha
              have haS1 : restrictVec S1 a = zT := by
                have : a ∈ Ω.filter (fun a => a i = true ∧ restrictVec S a = z) :=
                  Finset.mem_filter.mpr ⟨h.1, (Prod.mk.inj h.2).1, (Prod.mk.inj h.2).2⟩
                rw [hfilt_zT] at this; exact (Finset.mem_filter.mp this).2
              exact hmemT (Finset.mem_image.mpr ⟨a, h.1, haS1⟩)
            rw [hnum0, zero_div]
          rw [hq0]; unfold perturbProb; ring
      -- Substitute htrue_sum into the sum over σ:
      have hinner : ∀ σ ∈ SigmaSet.filter (fun σ => mask σ = τ),
          ∑ ab ∈ (Ω.filter (fun a => a i = true ∧ restrictVec S a = x))
                ×ˢ (Ω.filter (fun b => b i = true ∧ restrictVec S b = y)), W (σ, ab)
          = (1 / (2 : ℝ) ^ ord.length) * prefWeight Ω ord τ k x * prefWeight Ω ord τ k y
            * (perturbProb (condProb Ω S i x) (σ k) * perturbProb (condProb Ω S i y) (σ k)) := by
        intro σ hσ
        rw [Finset.sum_product]
        calc ∑ a ∈ Ω.filter (fun a => a i = true ∧ restrictVec S a = x),
              ∑ b ∈ Ω.filter (fun b => b i = true ∧ restrictVec S b = y),
                (1 / (2 : ℝ) ^ ord.length) * fullWeight Ω ord σ a * fullWeight Ω ord σ b
            = (1 / (2 : ℝ) ^ ord.length)
              * (∑ a ∈ Ω.filter (fun a => a i = true ∧ restrictVec S a = x), fullWeight Ω ord σ a)
              * (∑ b ∈ Ω.filter (fun b => b i = true ∧ restrictVec S b = y), fullWeight Ω ord σ b) := by
              rw [mul_assoc, Finset.mul_sum]; simp_rw [Finset.sum_mul, Finset.mul_sum]
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl; intro a _
              apply Finset.sum_congr rfl; intro b _; ring
          _ = (1 / (2 : ℝ) ^ ord.length) * prefWeight Ω ord τ k x * prefWeight Ω ord τ k y
              * (perturbProb (condProb Ω S i x) (σ k) * perturbProb (condProb Ω S i y) (σ k)) := by
              rw [htrue_sum σ hσ x hx, htrue_sum σ hσ y hy]; ring
      rw [Finset.sum_congr rfl hinner]
      -- Now pair each σ with flip σ k (involution on SigmaSet.filter (mask σ = τ)) to average σ k!
      set Fτ := SigmaSet.filter (fun σ => mask σ = τ)
      let flip : (Fin ord.length → Bool) → (Fin ord.length → Bool) :=
        fun σ j => if j = k then !(σ k) else σ j
      have hflip_mem : ∀ σ ∈ Fτ, flip σ ∈ Fτ := by
        intro σ hσ
        rw [Finset.mem_filter] at hσ ⊢
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [← hσ.2]; ext j; simp only [mask, flip]
        by_cases hjk : (j : ℕ) < k
        · have hjne : j ≠ k := fun h => by subst h; exact Nat.lt_irrefl _ hjk
          simp [hjk, hjne]
        · simp [hjk]
      have hflip_inv : ∀ σ, flip (flip σ) = σ := by
        intro σ; ext j; simp only [flip]
        by_cases hj : j = k
        · subst hj; simp
        · simp [hj]
      have hsum_flip : ∑ σ ∈ Fτ,
            (perturbProb (condProb Ω S i x) (σ k) * perturbProb (condProb Ω S i y) (σ k))
          = ∑ σ ∈ Fτ,
            (perturbProb (condProb Ω S i x) (!(σ k)) * perturbProb (condProb Ω S i y) (!(σ k))) := by
        apply Finset.sum_nbij flip hflip_mem
        · intro a _ b _ hab
          have := congr_arg flip hab; rwa [hflip_inv, hflip_inv] at this
        · intro b hb; exact ⟨flip b, hflip_mem b hb, hflip_inv b⟩
        · intro σ _; simp [flip]
      have havg_sum : ∑ σ ∈ Fτ,
            (perturbProb (condProb Ω S i x) (σ k) * perturbProb (condProb Ω S i y) (σ k))
          = (Fτ.card : ℝ) * I_fun (condProb Ω S i x) (condProb Ω S i y) := by
        have h2 : 2 * (∑ σ ∈ Fτ,
              (perturbProb (condProb Ω S i x) (σ k) * perturbProb (condProb Ω S i y) (σ k)))
            = ∑ σ ∈ Fτ,
              (perturbProb (condProb Ω S i x) (σ k) * perturbProb (condProb Ω S i y) (σ k)
               + perturbProb (condProb Ω S i x) (!(σ k)) * perturbProb (condProb Ω S i y) (!(σ k))) := by
          rw [two_mul, Finset.sum_add_distrib, ← hsum_flip]
        have hterm2 : ∀ σ ∈ Fτ,
            perturbProb (condProb Ω S i x) (σ k) * perturbProb (condProb Ω S i y) (σ k)
              + perturbProb (condProb Ω S i x) (!(σ k)) * perturbProb (condProb Ω S i y) (!(σ k))
            = 2 * I_fun (condProb Ω S i x) (condProb Ω S i y) := by
          intro σ _
          have hp := perturbProb_prod_avg (x := condProb Ω S i x) (y := condProb Ω S i y) htau0
          cases σ k <;> simp <;> linarith
        rw [Finset.sum_congr rfl hterm2, Finset.sum_const, nsmul_eq_mul] at h2
        linarith
      rw [← Finset.mul_sum, havg_sum]
      rw [Finset.sum_const, nsmul_eq_mul]
      ring
    -- Now rewrite the sum over Mset × (Ω.image) × (Ω.image) back to the sum over σ ∈ SigmaSet!
    have hsum_eq :
        ∑ p ∈ Mset ×ˢ ((Ω.image (restrictVec S)) ×ˢ (Ω.image (restrictVec S))),
          pushProb Ξ W Gmap p * h (pushProb Ξ W (fun q => (C q i, Gmap q)) (true, p) / pushProb Ξ W Gmap p)
        = ∑ σ : Fin ord.length → Bool,
            ∑ x ∈ Ω.image (restrictVec S),
              ∑ y ∈ Ω.image (restrictVec S),
                (1 / (2 : ℝ) ^ ord.length)
                  * prefWeight Ω ord σ k x * prefWeight Ω ord σ k y
                  * h (I_fun (condProb Ω S i x) (condProb Ω S i y)) := by
      rw [Finset.sum_product]
      have hterm_eq : ∀ τ ∈ Mset,
          ∑ xy ∈ (Ω.image (restrictVec S)) ×ˢ (Ω.image (restrictVec S)),
            pushProb Ξ W Gmap (τ, xy)
              * h (pushProb Ξ W (fun q => (C q i, Gmap q)) (true, (τ, xy)) / pushProb Ξ W Gmap (τ, xy))
          = ∑ σ ∈ SigmaSet.filter (fun σ => mask σ = τ),
              ∑ x ∈ Ω.image (restrictVec S),
                ∑ y ∈ Ω.image (restrictVec S),
                  (1 / (2 : ℝ) ^ ord.length)
                    * prefWeight Ω ord σ k x * prefWeight Ω ord σ k y
                    * h (I_fun (condProb Ω S i x) (condProb Ω S i y)) := by
        intro τ hτ
        rw [Finset.sum_product]
        calc ∑ x ∈ Ω.image (restrictVec S), ∑ y ∈ Ω.image (restrictVec S),
              pushProb Ξ W Gmap (τ, x, y)
                * h (pushProb Ξ W (fun q => (C q i, Gmap q)) (true, (τ, x, y)) / pushProb Ξ W Gmap (τ, x, y))
            = ∑ x ∈ Ω.image (restrictVec S), ∑ y ∈ Ω.image (restrictVec S),
                (∑ σ ∈ SigmaSet.filter (fun σ => mask σ = τ), (1 / (2 : ℝ) ^ ord.length))
                  * prefWeight Ω ord τ k x * prefWeight Ω ord τ k y
                  * h (I_fun (condProb Ω S i x) (condProb Ω S i y)) := by
              apply Finset.sum_congr rfl; intro x hx
              apply Finset.sum_congr rfl; intro y hy
              rw [hfib_den τ hτ x hx y hy, hfib_num τ hτ x hx y hy]
              set D := (∑ σ ∈ SigmaSet.filter (fun σ => mask σ = τ), (1 / (2 : ℝ) ^ ord.length))
                * prefWeight Ω ord τ k x * prefWeight Ω ord τ k y
              by_cases hD : D = 0
              · rw [hD]; simp
              · rw [mul_div_cancel_left₀ _ hD]
          _ = ∑ σ ∈ SigmaSet.filter (fun σ => mask σ = τ),
                ∑ x ∈ Ω.image (restrictVec S),
                  ∑ y ∈ Ω.image (restrictVec S),
                    (1 / (2 : ℝ) ^ ord.length)
                      * prefWeight Ω ord σ k x * prefWeight Ω ord σ k y
                      * h (I_fun (condProb Ω S i x) (condProb Ω S i y)) := by
              rw [Finset.sum_comm]
              conv_rhs => rw [Finset.sum_comm]
              -- Pull the sum over σ outside both x and y
              have hpull : ∀ x ∈ Ω.image (restrictVec S),
                  ∑ y ∈ Ω.image (restrictVec S),
                    (∑ σ ∈ SigmaSet.filter (fun σ => mask σ = τ), (1 / (2 : ℝ) ^ ord.length))
                      * prefWeight Ω ord τ k x * prefWeight Ω ord τ k y
                      * h (I_fun (condProb Ω S i x) (condProb Ω S i y))
                  = ∑ σ ∈ SigmaSet.filter (fun σ => mask σ = τ),
                      ∑ y ∈ Ω.image (restrictVec S),
                        (1 / (2 : ℝ) ^ ord.length)
                          * prefWeight Ω ord σ k x * prefWeight Ω ord σ k y
                          * h (I_fun (condProb Ω S i x) (condProb Ω S i y)) := by
                intro x _
                rw [Finset.sum_comm]
                apply Finset.sum_congr rfl; intro y _
                rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
                apply Finset.sum_congr rfl; intro σ hσ
                rw [hpref_mask σ x, hpref_mask σ y, (Finset.mem_filter.mp hσ).2]
              rw [Finset.sum_comm]
              rw [Finset.sum_congr rfl hpull]
      rw [Finset.sum_congr rfl hterm_eq]
      rw [Finset.sum_fiberwise_of_maps_to (g := mask) (t := Mset)
            (fun σ hσ => Finset.mem_image_of_mem mask hσ)]
    linarith
  calc ∑ k : Fin ord.length,
        (∑ σ : Fin ord.length → Bool,
          ∑ x ∈ Ω.image (restrictVec ((ord.take k).toFinset)),
            ∑ y ∈ Ω.image (restrictVec ((ord.take k).toFinset)),
              (1 / (2 : ℝ) ^ ord.length)
                * prefWeight Ω ord σ k x * prefWeight Ω ord σ k y
                * h (I_fun (condProb Ω ((ord.take k).toFinset) (ord[k]) x)
                           (condProb Ω ((ord.take k).toFinset) (ord[k]) y)))
      ≤ ∑ k : Fin ord.length, coordCondEnt Ξ W C (ord[k]) ((ord.take k).toFinset) :=
        Finset.sum_le_sum fun k _ => hstep k
    _ = rvEnt Ξ W C := hchain.symm
    _ ≤ Real.log Ω.card := hHC_le

/-! ### Global Budget, Fibre Inequality, and Cauchy–Schwarz on `T`-Fibres -/

/-- Exact local quantities `U, V, g` at position `k` of ordering `ord`. -/
def localU {n : ℕ} (Ω : Finset (Fin n → Bool)) (ord : List (Fin n)) (k : Fin ord.length) : ℝ :=
  ∑ a ∈ Ω, ∑ b ∈ Ω,
    unifW Ω a * unifW Ω b *
      h (Qrv Ω ((ord.take k).toFinset) (ord[k]) a *
         Qrv Ω ((ord.take k).toFinset) (ord[k]) b)

def localV {n : ℕ} (Ω : Finset (Fin n → Bool)) (ord : List (Fin n)) (k : Fin ord.length) : ℝ :=
  ∑ σ : Fin ord.length → Bool,
    ∑ x ∈ Ω.image (restrictVec ((ord.take k).toFinset)),
      ∑ y ∈ Ω.image (restrictVec ((ord.take k).toFinset)),
        (1 / (2 : ℝ) ^ ord.length)
          * prefWeight Ω ord σ k x * prefWeight Ω ord σ k y
          * h (I_fun (condProb Ω ((ord.take k).toFinset) (ord[k]) x)
                     (condProb Ω ((ord.take k).toFinset) (ord[k]) y))

def localG {n : ℕ} (Ω : Finset (Fin n → Bool)) (ord : List (Fin n)) (k : Fin ord.length) : ℝ :=
  localU Ω ord k + qStar * localV Ω ord k
    - 2 * margProb Ω (ord[k]) * coordCondEnt Ω (unifW Ω) id (ord[k]) ((ord.take k).toFinset)

/-- Exact chain rule for `log |Ω| = ∑ k, e_k`. -/
lemma log_card_eq_sum_coordCondEnt {n : ℕ} (Ω : Finset (Fin n → Bool)) (hΩ : Ω.Nonempty)
    (ord : List (Fin n)) (hnd : ord.Nodup) (hcov : ord.toFinset = Finset.univ) :
    Real.log Ω.card =
      ∑ k : Fin ord.length, coordCondEnt Ω (unifW Ω) id (ord[k]) ((ord.take k).toFinset) := by
  have h1 := subEnt_append_list Ω (unifW Ω) id ∅ ord hnd (by simp)
  simp only [Finset.empty_union, hcov, subEnt_univ, subEnt_empty Ω (unifW Ω) (sum_unifW hΩ) id,
    sub_zero] at h1
  have hent : rvEnt Ω (unifW Ω) id = Real.log Ω.card := by
    unfold rvEnt shannonEnt
    have himg : Ω.image id = Ω := by ext v; simp
    rw [himg]
    have hp : ∀ v ∈ Ω, pushProb Ω (unifW Ω) id v = (1 : ℝ) / Ω.card := by
      intro v hv
      unfold pushProb unifW
      have hfilt : Ω.filter (fun w => id w = v) = {v} := by
        ext w; simp only [Finset.mem_filter, Finset.mem_singleton, id_eq]
        exact ⟨fun h => h.2, fun h => ⟨h ▸ hv, h⟩⟩
      rw [hfilt, Finset.sum_singleton]
    rw [Finset.sum_congr rfl (fun v hv => by rw [hp v hv])]
    exact shannonEnt_unif Ω hΩ
  linarith

/-- Global budget inequality: `∑ k, g_k + 2 ∑ k, (s_k - mStar) e_k ≤ 0`. -/
lemma global_budget_bound {n : ℕ} (Ω : Finset (Fin n → Bool)) (hΩ : Ω.Nonempty)
    (hAC : AndClosed Ω) (ord : List (Fin n)) (hnd : ord.Nodup) (hcov : ord.toFinset = Finset.univ)
    (htau0 : 0 ≤ tau) (htau1 : tau ≤ 1) :
    (∑ k : Fin ord.length, localG Ω ord k)
      + 2 * ∑ k : Fin ord.length,
          (margProb Ω (ord[k]) - mStar) * coordCondEnt Ω (unifW Ω) id (ord[k]) ((ord.take k).toFinset)
      ≤ 0 := by
  have hU := independent_protocol_bound Ω hΩ hAC ord hnd hcov
  have hV := ciid_protocol_bound Ω hΩ hAC ord hnd hcov htau0 htau1
  have hH := log_card_eq_sum_coordCondEnt Ω hΩ ord hnd hcov
  have hq : 0 < qStar := qStar_pos
  have hq1 : qStar + 1 = 2 * mStar := qStar_add_one
  have hrew : (∑ k : Fin ord.length, localG Ω ord k)
      + 2 * ∑ k : Fin ord.length,
          (margProb Ω (ord[k]) - mStar) * coordCondEnt Ω (unifW Ω) id (ord[k]) ((ord.take k).toFinset)
      = (∑ k : Fin ord.length, localU Ω ord k)
        + qStar * (∑ k : Fin ord.length, localV Ω ord k)
        - 2 * mStar * (∑ k : Fin ord.length,
            coordCondEnt Ω (unifW Ω) id (ord[k]) ((ord.take k).toFinset)) := by
    unfold localG
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    have hmul : 2 * ∑ k : Fin ord.length,
          (margProb Ω (ord[k]) - mStar) * coordCondEnt Ω (unifW Ω) id (ord[k]) ((ord.take k).toFinset)
        = (∑ k : Fin ord.length,
            2 * margProb Ω (ord[k]) * coordCondEnt Ω (unifW Ω) id (ord[k]) ((ord.take k).toFinset))
          - 2 * mStar * (∑ k : Fin ord.length,
            coordCondEnt Ω (unifW Ω) id (ord[k]) ((ord.take k).toFinset)) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro k _; ring
    linarith
  rw [hrew, ← hH]
  change ∑ k : Fin ord.length, localU Ω ord k ≤ Real.log Ω.card at hU
  change ∑ k : Fin ord.length, localV Ω ord k ≤ Real.log Ω.card at hV
  have hqV : qStar * ∑ k : Fin ord.length, localV Ω ord k ≤ qStar * Real.log Ω.card :=
    mul_le_mul_of_nonneg_left hV (le_of_lt hq)
  rw [← hq1]
  linarith

/-- Exact decomposition of `localG` into `E[F] + q * E_K[J] + q * L * Var(t_Z)`!
    In particular, whenever `F ≥ 0` and `J ≥ 0` on `[0, 1]²`, `localG Ω ord k ≥ 0`. -/
lemma localG_decomposition {n : ℕ} (Ω : Finset (Fin n → Bool)) (hΩ : Ω.Nonempty)
    (ord : List (Fin n)) (hnd : ord.Nodup) (k : Fin ord.length) :
    let S := (ord.take k).toFinset
    let i := ord[k]
    let t := ∑ v ∈ Ω, unifW Ω v * phi (Qrv Ω S i v)
    let tZ : (Fin ord.length → Bool) → ℝ := fun σ =>
      ∑ x ∈ Ω.image (restrictVec S), prefWeight Ω ord σ k x * phi (condProb Ω S i x)
    localG Ω ord k =
      (∑ a ∈ Ω, ∑ b ∈ Ω, unifW Ω a * unifW Ω b * F_fun (Qrv Ω S i a) (Qrv Ω S i b))
      + qStar * (∑ σ : Fin ord.length → Bool,
          ∑ x ∈ Ω.image (restrictVec S), ∑ y ∈ Ω.image (restrictVec S),
            (1 / (2 : ℝ) ^ ord.length) * prefWeight Ω ord σ k x * prefWeight Ω ord σ k y
              * J_fun (condProb Ω S i x) (condProb Ω S i y))
      + qStar * L * (∑ σ : Fin ord.length → Bool, (1 / (2 : ℝ) ^ ord.length) * (tZ σ - t) ^ 2) := by
  intro S i t tZ
  -- 1. Expand E[F] = localU + qStar * L * t^2 - 2 * s * e:
  have hEF : (∑ a ∈ Ω, ∑ b ∈ Ω, unifW Ω a * unifW Ω b * F_fun (Qrv Ω S i a) (Qrv Ω S i b))
      = localU Ω ord k + qStar * L * t ^ 2
        - 2 * margProb Ω i * coordCondEnt Ω (unifW Ω) id i S := by
    unfold F_fun localU
    have hsplit : ∀ a ∈ Ω, ∀ b ∈ Ω,
        unifW Ω a * unifW Ω b *
          (h (Qrv Ω S i a * Qrv Ω S i b) + qStar * L * phi (Qrv Ω S i a) * phi (Qrv Ω S i b)
            - Qrv Ω S i b * h (Qrv Ω S i a) - Qrv Ω S i a * h (Qrv Ω S i b))
        = unifW Ω a * unifW Ω b * h (Qrv Ω S i a * Qrv Ω S i b)
          + qStar * L * ((unifW Ω a * phi (Qrv Ω S i a)) * (unifW Ω b * phi (Qrv Ω S i b)))
          - (unifW Ω a * h (Qrv Ω S i a)) * (unifW Ω b * Qrv Ω S i b)
          - (unifW Ω a * Qrv Ω S i a) * (unifW Ω b * h (Qrv Ω S i b)) := by
      intro a _ b _; ring
    simp_rw [Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => hsplit a ha b hb]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    have hphi2 : ∑ a ∈ Ω, ∑ b ∈ Ω,
          qStar * L * ((unifW Ω a * phi (Qrv Ω S i a)) * (unifW Ω b * phi (Qrv Ω S i b)))
        = qStar * L * t ^ 2 := by
      simp_rw [← Finset.mul_sum, ← Finset.sum_mul]; ring
    have hse1 : ∑ a ∈ Ω, ∑ b ∈ Ω, (unifW Ω a * h (Qrv Ω S i a)) * (unifW Ω b * Qrv Ω S i b)
        = coordCondEnt Ω (unifW Ω) id i S * margProb Ω i := by
      simp_rw [← Finset.mul_sum, ← Finset.sum_mul, expect_Qrv, coordCondEnt_eq_expect_h]
    have hse2 : ∑ a ∈ Ω, ∑ b ∈ Ω, (unifW Ω a * Qrv Ω S i a) * (unifW Ω b * h (Qrv Ω S i b))
        = margProb Ω i * coordCondEnt Ω (unifW Ω) id i S := by
      simp_rw [← Finset.mul_sum, ← Finset.sum_mul, expect_Qrv, coordCondEnt_eq_expect_h]
    rw [hphi2, hse1, hse2]; ring
  -- 2. Expand E_K[J] = localV - L * E[tZ^2]:
  have hEJ : (∑ σ : Fin ord.length → Bool,
        ∑ x ∈ Ω.image (restrictVec S), ∑ y ∈ Ω.image (restrictVec S),
          (1 / (2 : ℝ) ^ ord.length) * prefWeight Ω ord σ k x * prefWeight Ω ord σ k y
            * J_fun (condProb Ω S i x) (condProb Ω S i y))
      = localV Ω ord k - L * (∑ σ : Fin ord.length → Bool, (1 / (2 : ℝ) ^ ord.length) * (tZ σ) ^ 2) := by
    unfold J_fun localV
    have hsplit : ∀ σ : Fin ord.length → Bool, ∀ x ∈ Ω.image (restrictVec S), ∀ y ∈ Ω.image (restrictVec S),
        (1 / (2 : ℝ) ^ ord.length) * prefWeight Ω ord σ k x * prefWeight Ω ord σ k y
          * (h (I_fun (condProb Ω S i x) (condProb Ω S i y))
              - L * phi (condProb Ω S i x) * phi (condProb Ω S i y))
        = (1 / (2 : ℝ) ^ ord.length) * prefWeight Ω ord σ k x * prefWeight Ω ord σ k y
            * h (I_fun (condProb Ω S i x) (condProb Ω S i y))
          - L * (1 / (2 : ℝ) ^ ord.length)
            * ((prefWeight Ω ord σ k x * phi (condProb Ω S i x))
               * (prefWeight Ω ord σ k y * phi (condProb Ω S i y))) := by
      intro σ x _ y _; ring
    simp_rw [Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun x hx =>
      Finset.sum_congr rfl fun y hy => hsplit σ x hx y hy]
    simp only [Finset.sum_sub_distrib]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro σ _
    simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
    simp only [tZ]; ring
  -- 3. Variance identity: E[(tZ - t)^2] = E[tZ^2] - t^2 using E[tZ] = t!
  have hEtZ : ∑ σ : Fin ord.length → Bool, (1 / (2 : ℝ) ^ ord.length) * tZ σ = t := by
    simp only [tZ, Finset.mul_sum]
    rw [Finset.sum_comm]
    have hterm : ∀ x ∈ Ω.image (restrictVec S),
        ∑ σ : Fin ord.length → Bool, (1 / (2 : ℝ) ^ ord.length) * (prefWeight Ω ord σ k x * phi (condProb Ω S i x))
        = fibreProb Ω S x * phi (condProb Ω S i x) := by
      intro x hx
      have havg := avg_prefWeight Ω hΩ ord hnd k (le_of_lt k.isLt) x hx
      conv_rhs => rw [← havg, div_eq_mul_inv, Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl; intro σ _; ring
    rw [Finset.sum_congr rfl hterm]
    exact (expect_comp_restrictVec Ω S (fun x => phi (condProb Ω S i x))).symm
  have hsum1 : ∑ _σ : Fin ord.length → Bool, (1 / (2 : ℝ) ^ ord.length) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul]
    push_cast; field_simp [show (2 : ℝ) ^ ord.length ≠ 0 by positivity]
  have hVar : ∑ σ : Fin ord.length → Bool, (1 / (2 : ℝ) ^ ord.length) * (tZ σ - t) ^ 2
      = (∑ σ : Fin ord.length → Bool, (1 / (2 : ℝ) ^ ord.length) * (tZ σ) ^ 2) - t ^ 2 := by
    have h1 : ∀ σ : Fin ord.length → Bool,
        (1 / (2 : ℝ) ^ ord.length) * (tZ σ - t) ^ 2
        = (1 / (2 : ℝ) ^ ord.length) * (tZ σ) ^ 2
          - 2 * t * ((1 / (2 : ℝ) ^ ord.length) * tZ σ)
          + t ^ 2 * (1 / (2 : ℝ) ^ ord.length) := by intro σ; ring
    rw [Finset.sum_congr rfl (fun σ _ => h1 σ), Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [show (∑ σ : Fin ord.length → Bool, 2 * t * ((1 / (2 : ℝ) ^ ord.length) * tZ σ))
          = 2 * t * (∑ σ : Fin ord.length → Bool, (1 / (2 : ℝ) ^ ord.length) * tZ σ)
          from (Finset.mul_sum ..).symm,
        show (∑ σ : Fin ord.length → Bool, t ^ 2 * (1 / (2 : ℝ) ^ ord.length))
          = t ^ 2 * (∑ σ : Fin ord.length → Bool, (1 / (2 : ℝ) ^ ord.length))
          from (Finset.mul_sum ..).symm,
        hEtZ, hsum1]
    ring
  unfold localG
  rw [hEF, hEJ, hVar]
  ring

/-- Nonnegativity of `localG` whenever `F_fun ≥ 0` and `J_fun ≥ 0` on `[0, 1]²`. -/
lemma localG_nonneg {n : ℕ} (Ω : Finset (Fin n → Bool)) (hΩ : Ω.Nonempty)
    (ord : List (Fin n)) (hnd : ord.Nodup) (k : Fin ord.length)
    (htau0 : 0 < tau) (htau1 : tau < 1 / 2)
    (hF : ∀ x y : ℝ, 0 ≤ x → x ≤ 1 → 0 ≤ y → y ≤ 1 → 0 ≤ F_fun x y) :
    0 ≤ localG Ω ord k := by
  rw [localG_decomposition Ω hΩ ord hnd k]
  have hpref_nn : ∀ σ x, 0 ≤ prefWeight Ω ord σ k x := by
    intro σ x; unfold prefWeight
    apply Finset.prod_nonneg; intro j _
    split_ifs
    · exact stepFactor_nonneg Ω ord (le_of_lt htau0) (by linarith) j (σ j) x
    · norm_num
  have h1 : 0 ≤ ∑ a ∈ Ω, ∑ b ∈ Ω,
      unifW Ω a * unifW Ω b * F_fun (Qrv Ω ((ord.take k).toFinset) (ord[k]) a)
        (Qrv Ω ((ord.take k).toFinset) (ord[k]) b) := by
    apply Finset.sum_nonneg; intro a _
    apply Finset.sum_nonneg; intro b _
    have ha := Qrv_mem_Icc Ω ((ord.take k).toFinset) (ord[k]) a
    have hb := Qrv_mem_Icc Ω ((ord.take k).toFinset) (ord[k]) b
    exact mul_nonneg (mul_nonneg (unifW_nonneg Ω a) (unifW_nonneg Ω b)) (hF _ _ ha.1 ha.2 hb.1 hb.2)
  have h2 : 0 ≤ qStar * (∑ σ : Fin ord.length → Bool,
      ∑ x ∈ Ω.image (restrictVec ((ord.take k).toFinset)),
        ∑ y ∈ Ω.image (restrictVec ((ord.take k).toFinset)),
          (1 / (2 : ℝ) ^ ord.length) * prefWeight Ω ord σ k x * prefWeight Ω ord σ k y
            * J_fun (condProb Ω ((ord.take k).toFinset) (ord[k]) x)
                    (condProb Ω ((ord.take k).toFinset) (ord[k]) y)) := by
    apply mul_nonneg (le_of_lt qStar_pos)
    apply Finset.sum_nonneg; intro σ _
    apply Finset.sum_nonneg; intro x _
    apply Finset.sum_nonneg; intro y _
    exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (hpref_nn σ x)) (hpref_nn σ y))
      (J_fun_nonneg_of_tau htau0 htau1 (condProb_nonneg _ _ _ _) (condProb_le_one _ _ _ _)
        (condProb_nonneg _ _ _ _) (condProb_le_one _ _ _ _))
  have h3 : 0 ≤ qStar * L * (∑ σ : Fin ord.length → Bool,
      (1 / (2 : ℝ) ^ ord.length) *
        ((∑ x ∈ Ω.image (restrictVec ((ord.take k).toFinset)),
            prefWeight Ω ord σ k x * phi (condProb Ω ((ord.take k).toFinset) (ord[k]) x))
         - (∑ v ∈ Ω, unifW Ω v * phi (Qrv Ω ((ord.take k).toFinset) (ord[k]) v))) ^ 2) := by
    apply mul_nonneg (mul_nonneg (le_of_lt qStar_pos) (le_of_lt L_pos))
    apply Finset.sum_nonneg; intro σ _
    exact mul_nonneg (by positivity) (sq_nonneg _)
  linarith

/-- **Fibre Inequality (Lemma 3.1 of Sadhu–Ursin)**:
    If `S` is placed first in a complete nodup order `ord = ordS ++ ordR` (so `S = ordS.toFinset`),
    then `∑ k : Fin ordR.length, E[(p_{ordR[k]} - mStar) * h(Q_{ordR[k]})] ≤ 0`,
    where `p_i(v) = Qrv Ω S i v` and `Q_i(v) = Qrv Ω (S ∪ (ordR.take k).toFinset) i v`! -/
lemma fibre_inequality {n : ℕ} (Ω : Finset (Fin n → Bool)) (hΩ : Ω.Nonempty)
    (hAC : AndClosed Ω) (S : Finset (Fin n)) (ordR : List (Fin n))
    (hndR : ordR.Nodup) (hdisj : ∀ i ∈ ordR, i ∉ S) (hcov : S ∪ ordR.toFinset = Finset.univ)
    (htau0 : 0 < tau) (htau1 : tau < 1 / 2)
    (hF : ∀ x y : ℝ, 0 ≤ x → x ≤ 1 → 0 ≤ y → y ≤ 1 → 0 ≤ F_fun x y) :
    ∑ k : Fin ordR.length,
      ∑ v ∈ Ω, unifW Ω v * (Qrv Ω S (ordR[k]) v - mStar)
        * h (Qrv Ω (S ∪ (ordR.take k).toFinset) (ordR[k]) v) ≤ 0 := by
  -- Build a complete nodup order ord = S.toList ++ ordR on Fin n
  let ordS : List (Fin n) := S.toList
  have hndS : ordS.Nodup := Finset.nodup_toList S
  have hS_eq : ordS.toFinset = S := Finset.toList_toFinset S
  let ord : List (Fin n) := ordS ++ ordR
  have hnd : ord.Nodup := by
    rw [List.nodup_append]
    refine ⟨hndS, hndR, ?_⟩
    intro a ha b hb hab; subst hab
    exact hdisj a hb (by rwa [← hS_eq, List.mem_toFinset])
  have hcov_ord : ord.toFinset = Finset.univ := by
    simp [ord, List.toFinset_append, hS_eq, hcov]
  -- Partition Ω by y = restrictVec S v ∈ Ω.image (restrictVec S)!
  -- On each fibre Ωy := Ω.filter (restrictVec S v = y), Ωy is nonempty and AndClosed!
  have hfibre_sum :
      ∑ k : Fin ordR.length,
        ∑ v ∈ Ω, unifW Ω v * (Qrv Ω S (ordR[k]) v - mStar)
          * h (Qrv Ω (S ∪ (ordR.take k).toFinset) (ordR[k]) v)
      = ∑ y ∈ Ω.image (restrictVec S), fibreProb Ω S y *
          ∑ k : Fin ordR.length,
            (condProb Ω S (ordR[k]) y - mStar)
              * coordCondEnt (Ω.filter (fun v => restrictVec S v = y))
                  (unifW (Ω.filter (fun v => restrictVec S v = y))) id
                  (ordR[k]) (S ∪ (ordR.take k).toFinset) := by
    -- Group v ∈ Ω by restrictVec S v = y for each k, then swap sums!
    have hstep1 : ∀ k : Fin ordR.length,
        ∑ v ∈ Ω, unifW Ω v * (Qrv Ω S (ordR[k]) v - mStar)
          * h (Qrv Ω (S ∪ (ordR.take k).toFinset) (ordR[k]) v)
        = ∑ y ∈ Ω.image (restrictVec S), fibreProb Ω S y *
            ((condProb Ω S (ordR[k]) y - mStar)
              * coordCondEnt (Ω.filter (fun v => restrictVec S v = y))
                  (unifW (Ω.filter (fun v => restrictVec S v = y))) id
                  (ordR[k]) (S ∪ (ordR.take k).toFinset)) := by
      intro k
      set P := S ∪ (ordR.take k).toFinset
      set i := ordR[k]
      rw [← Finset.sum_fiberwise_of_maps_to (g := restrictVec S) (t := Ω.image (restrictVec S))
            (fun v hv => Finset.mem_image_of_mem _ hv)]
      apply Finset.sum_congr rfl
      intro y hy
      set Ωy := Ω.filter (fun v => restrictVec S v = y)
      have hΩy_ne : Ωy.Nonempty := by
        rcases Finset.mem_image.mp hy with ⟨v0, hv0, rfl⟩
        exact ⟨v0, Finset.mem_filter.mpr ⟨hv0, rfl⟩⟩
      have hΩy_pos : (0 : ℝ) < Ωy.card := Nat.cast_pos.mpr hΩy_ne.card_pos
      have hΩ_pos : (0 : ℝ) < Ω.card := Nat.cast_pos.mpr hΩ.card_pos
      have hfp : fibreProb Ω S y = (Ωy.card : ℝ) / (Ω.card : ℝ) := by
        unfold fibreProb pushProb unifW
        rw [Finset.sum_const, nsmul_eq_mul, mul_one_div]
      -- For every v ∈ Ωy, Qrv Ω P i v = Qrv Ωy P i v!
      have hQ_eq : ∀ v ∈ Ωy, Qrv Ω P i v = Qrv Ωy P i v := by
        intro v hv
        unfold Qrv condProb fibreProb pushProb unifW
        have hSP : S ⊆ P := Finset.subset_union_left
        have hvy : restrictVec S v = y := (Finset.mem_filter.mp hv).2
        have hf1 : Ωy.filter (fun w => restrictVec P w = restrictVec P v)
            = Ω.filter (fun w => restrictVec P w = restrictVec P v) := by
          ext w; simp only [Ωy, Finset.mem_filter]
          constructor
          · rintro ⟨⟨hwΩ, _⟩, hwP⟩; exact ⟨hwΩ, hwP⟩
          · rintro ⟨hwΩ, hwP⟩
            refine ⟨⟨hwΩ, ?_⟩, hwP⟩
            rw [← hvy]; ext j; simp only [restrictVec]
            by_cases hj : j ∈ S
            · have := congr_fun hwP j; simpa [restrictVec, hj, hSP hj] using this
            · simp [hj]
        have hf2 : Ωy.filter (fun w => (w i, restrictVec P w) = (true, restrictVec P v))
            = Ω.filter (fun w => (w i, restrictVec P w) = (true, restrictVec P v)) := by
          ext w; simp only [Ωy, Finset.mem_filter, Prod.mk.injEq]
          constructor
          · rintro ⟨⟨hwΩ, _⟩, hwi, hwP⟩; exact ⟨hwΩ, hwi, hwP⟩
          · rintro ⟨hwΩ, hwi, hwP⟩
            refine ⟨⟨hwΩ, ?_⟩, hwi, hwP⟩
            rw [← hvy]; ext j; simp only [restrictVec]
            by_cases hj : j ∈ S
            · have := congr_fun hwP j; simpa [restrictVec, hj, hSP hj] using this
            · simp [hj]
        rw [hf1, hf2]
        simp only [Finset.sum_const, nsmul_eq_mul, mul_one_div]
        field_simp [ne_of_gt hΩ_pos, ne_of_gt hΩy_pos]
      rw [coordCondEnt_eq_expect_h Ωy P i, hfp]
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v hv
      have hvy : restrictVec S v = y := (Finset.mem_filter.mp hv).2
      have hQv : Qrv Ω S i v = condProb Ω S i y := by unfold Qrv; rw [hvy]
      rw [hQv, hQ_eq v hv]
      unfold unifW
      field_simp [ne_of_gt hΩ_pos, ne_of_gt hΩy_pos]
    rw [Finset.sum_congr rfl (fun k _ => hstep1 k), Finset.sum_comm]
    apply Finset.sum_congr rfl; intro y _
    rw [Finset.mul_sum]
  rw [hfibre_sum]
  apply Finset.sum_nonpos
  intro y hy
  apply mul_nonpos_of_nonneg_of_nonpos (fibreProb_nonneg Ω S y)
  set Ωy := Ω.filter (fun v => restrictVec S v = y)
  have hΩy_ne : Ωy.Nonempty := by
    rcases Finset.mem_image.mp hy with ⟨v0, hv0, rfl⟩
    exact ⟨v0, Finset.mem_filter.mpr ⟨hv0, rfl⟩⟩
  have hΩy_AC : AndClosed Ωy := by
    intro a ha b hb
    rcases Finset.mem_filter.mp ha with ⟨haΩ, hay⟩
    rcases Finset.mem_filter.mp hb with ⟨hbΩ, hby⟩
    refine Finset.mem_filter.mpr ⟨hAC a haΩ b hbΩ, ?_⟩
    ext j; simp only [restrictVec]
    by_cases hj : j ∈ S
    · have ha1 := congr_fun hay j
      have hb1 := congr_fun hby j
      simp only [restrictVec, hj, ↓reduceIte] at ha1 hb1 ⊢
      rw [ha1, hb1, Bool.and_self]
    · simp only [hj, ↓reduceIte]
      have ha1 := congr_fun hay j; simpa [restrictVec, hj] using ha1
  -- Apply global_budget_bound and localG_nonneg to Ωy along ord!
  have hgb := global_budget_bound Ωy hΩy_ne hΩy_AC ord hnd hcov_ord (le_of_lt htau0) (by linarith)
  have hgnn : 0 ≤ ∑ j : Fin ord.length, localG Ωy ord j :=
    Finset.sum_nonneg fun j _ => localG_nonneg Ωy hΩy_ne ord hnd j htau0 htau1 hF
  have hsum_le : ∑ j : Fin ord.length,
      (margProb Ωy (ord[j]) - mStar) * coordCondEnt Ωy (unifW Ωy) id (ord[j]) ((ord.take j).toFinset)
      ≤ 0 := by linarith
  -- Split sum over ord = ordS ++ ordR: terms in ordS have coordCondEnt = 0 (since v is constant on S in Ωy!)
  have hsplit_ord : ∑ j : Fin ord.length,
        (margProb Ωy (ord[j]) - mStar) * coordCondEnt Ωy (unifW Ωy) id (ord[j]) ((ord.take j).toFinset)
      = ∑ k : Fin ordR.length,
          (condProb Ω S (ordR[k]) y - mStar)
            * coordCondEnt Ωy (unifW Ωy) id (ordR[k]) (S ∪ (ordR.take k).toFinset) := by
    have hlen : ord.length = ordS.length + ordR.length := List.length_append
    rw [← (finCongr hlen.symm).sum_comp, Fin.sum_univ_add]
    have hfirst0 : ∑ j : Fin ordS.length,
        (margProb Ωy (ord[finCongr hlen.symm (Fin.castAdd ordR.length j)]) - mStar)
          * coordCondEnt Ωy (unifW Ωy) id (ord[finCongr hlen.symm (Fin.castAdd ordR.length j)])
              ((ord.take (finCongr hlen.symm (Fin.castAdd ordR.length j))).toFinset) = 0 := by
      apply Finset.sum_eq_zero; intro j _
      set idx := ord[finCongr hlen.symm (Fin.castAdd ordR.length j)]
      have hidx_S : idx ∈ S := by
        have h1 : idx = ordS[j] := by simp [idx, ord, List.getElem_append_left j.isLt]
        have h2 : ordS[j] ∈ ordS.toFinset := List.mem_toFinset.mpr (List.getElem_mem j.isLt)
        rw [hS_eq] at h2
        rwa [h1]
      have hce0 : coordCondEnt Ωy (unifW Ωy) id idx
          ((ord.take (finCongr hlen.symm (Fin.castAdd ordR.length j))).toFinset) = 0 := by
        rw [coordCondEnt_eq_expect_h]
        apply Finset.sum_eq_zero; intro v hv
        have hconst : ∀ w ∈ Ωy, w idx = y idx := by
          intro w hw
          have := congr_fun (Finset.mem_filter.mp hw).2 idx
          simpa [restrictVec, hidx_S] using this
        set P := (ord.take (finCongr hlen.symm (Fin.castAdd ordR.length j))).toFinset
        have hmem : restrictVec P v ∈ Ωy.image (restrictVec P) := Finset.mem_image_of_mem _ hv
        have hpos := fibreProb_pos_of_mem_image Ωy P hmem
        cases hyi : y idx
        · have hq0 : Qrv Ωy P idx v = 0 := by
            unfold Qrv condProb; apply div_eq_zero_iff.mpr; left
            unfold pushProb; apply Finset.sum_eq_zero; intro w hw; exfalso
            have h := Finset.mem_filter.mp hw
            have h1 := hconst w h.1; rw [hyi] at h1
            have h2 := (Prod.mk.inj h.2).1; rw [h1] at h2; cases h2
          rw [hq0, h_zero, mul_zero]
        · have hq1 : Qrv Ωy P idx v = 1 := by
            unfold Qrv condProb
            have hnum : pushProb Ωy (unifW Ωy) (fun w => (w idx, restrictVec P w)) (true, restrictVec P v)
                = fibreProb Ωy P (restrictVec P v) := by
              unfold fibreProb pushProb; congr 1; ext w
              simp only [Finset.mem_filter, Prod.mk.injEq]
              constructor
              · rintro ⟨hw, _, hP⟩; exact ⟨hw, hP⟩
              · rintro ⟨hw, hP⟩; exact ⟨hw, by rw [hconst w hw, hyi], hP⟩
            rw [hnum, div_self (ne_of_gt hpos)]
          rw [hq1, h_one, mul_zero]
      rw [hce0, mul_zero]
    rw [hfirst0, zero_add]
    apply Finset.sum_congr rfl; intro k _
    have hidx : ord[finCongr hlen.symm (Fin.natAdd ordS.length k)] = ordR[k] := by
      simp [ord, List.getElem_append_right (Nat.le_add_right ordS.length k)]
    have htake : (ord.take (finCongr hlen.symm (Fin.natAdd ordS.length k))).toFinset
        = S ∪ (ordR.take k).toFinset := by
      simp only [finCongr_apply, Fin.val_cast, Fin.val_natAdd, ord]
      rw [List.take_append, List.take_of_length_le (Nat.le_add_right ordS.length k),
          Nat.add_sub_cancel_left, List.toFinset_append, hS_eq]
    have hmarg : margProb Ωy (ordR[k]) = condProb Ω S (ordR[k]) y := by
      unfold margProb condProb fibreProb pushProb unifW
      have hfilt : Ωy.filter (fun v => v (ordR[k]) = true)
          = Ω.filter (fun v => (v (ordR[k]), restrictVec S v) = (true, y)) := by
        ext v; simp only [Ωy, Finset.mem_filter, Prod.mk.injEq]; tauto
      rw [hfilt]
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one_div]
      have hΩ_pos : (0 : ℝ) < Ω.card := Nat.cast_pos.mpr hΩ.card_pos
      have hΩy_pos : (0 : ℝ) < Ωy.card := Nat.cast_pos.mpr hΩy_ne.card_pos
      change ((Ω.filter (fun v => (v (ordR[k]), restrictVec S v) = (true, y))).card : ℝ) / (Ωy.card : ℝ)
        = (((Ω.filter (fun v => (v (ordR[k]), restrictVec S v) = (true, y))).card : ℝ) / (Ω.card : ℝ))
          / ((Ωy.card : ℝ) / (Ω.card : ℝ))
      field_simp [ne_of_gt hΩ_pos, ne_of_gt hΩy_pos]
    rw [hidx, htake, hmarg]
  linarith

/-- **Cauchy–Schwarz on `T`-fibres**:
    If `S ⊆ P`, then for any coordinate `i`:
    `E[p_i * h(Q_i)] ≥ (E[√(Q_i * h(Q_i))])^2`,
    where `p_i = Qrv Ω S i` and `Q_i = Qrv Ω P i`! -/
lemma cauchy_schwarz_fibre {n : ℕ} (Ω : Finset (Fin n → Bool)) (hΩ : Ω.Nonempty)
    {S P : Finset (Fin n)} (hSP : S ⊆ P) (i : Fin n) :
    (∑ v ∈ Ω, unifW Ω v * Real.sqrt (Qrv Ω P i v * h (Qrv Ω P i v))) ^ 2
      ≤ ∑ v ∈ Ω, unifW Ω v * Qrv Ω S i v * h (Qrv Ω P i v) := by
  -- Step 1: On each fibre y = restrictVec S v, by Cauchy–Schwarz:
  -- (∑_{v ∈ Ωy} u(v) √(Q(v) h(Q(v))))^2 ≤ (∑_{v ∈ Ωy} u(v) Q(v)) * (∑_{v ∈ Ωy} u(v) h(Q(v)))
  -- = (fibreProb Ω S y * condProb Ω S i y) * (∑_{v ∈ Ωy} u(v) h(Q(v)))
  -- = fibreProb Ω S y * (∑_{v ∈ Ωy} u(v) * Qrv Ω S i v * h(Q(v)))!
  -- Step 2: Sum √(f_y) over y using Cauchy–Schwarz again with weights fibreProb Ω S y (summing to 1)!
  set Y := Ω.image (restrictVec S)
  let A : (Fin n → Bool) → ℝ := fun y =>
    ∑ v ∈ Ω.filter (fun v => restrictVec S v = y),
      unifW Ω v * Real.sqrt (Qrv Ω P i v * h (Qrv Ω P i v))
  let B : (Fin n → Bool) → ℝ := fun y =>
    ∑ v ∈ Ω.filter (fun v => restrictVec S v = y),
      unifW Ω v * Qrv Ω S i v * h (Qrv Ω P i v)
  have hLHS : ∑ v ∈ Ω, unifW Ω v * Real.sqrt (Qrv Ω P i v * h (Qrv Ω P i v)) = ∑ y ∈ Y, A y := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := restrictVec S) (t := Y)
          (fun v hv => Finset.mem_image_of_mem _ hv)]
  have hRHS : ∑ v ∈ Ω, unifW Ω v * Qrv Ω S i v * h (Qrv Ω P i v) = ∑ y ∈ Y, B y := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := restrictVec S) (t := Y)
          (fun v hv => Finset.mem_image_of_mem _ hv)]
  rw [hLHS, hRHS]
  -- Fibrewise Cauchy–Schwarz: (A y)^2 ≤ fibreProb Ω S y * B y!
  have hfib : ∀ y ∈ Y, (A y) ^ 2 ≤ fibreProb Ω S y * B y := by
    intro y _
    set Ωy := Ω.filter (fun v => restrictVec S v = y)
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq Ωy
      (fun v => Real.sqrt (unifW Ω v * Qrv Ω P i v))
      (fun v => Real.sqrt (unifW Ω v * h (Qrv Ω P i v)))
    have h1 : ∀ v ∈ Ωy,
        Real.sqrt (unifW Ω v * Qrv Ω P i v) * Real.sqrt (unifW Ω v * h (Qrv Ω P i v))
        = unifW Ω v * Real.sqrt (Qrv Ω P i v * h (Qrv Ω P i v)) := by
      intro v _
      have hw := unifW_nonneg Ω v
      have hq := Qrv_mem_Icc Ω P i v
      have hh := h_nonneg hq.1 hq.2
      rw [← Real.sqrt_mul (mul_nonneg hw hq.1)]
      have heq : unifW Ω v * Qrv Ω P i v * (unifW Ω v * h (Qrv Ω P i v))
          = (unifW Ω v) ^ 2 * (Qrv Ω P i v * h (Qrv Ω P i v)) := by ring
      rw [heq, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hw]
    have h2 : ∀ v ∈ Ωy, Real.sqrt (unifW Ω v * Qrv Ω P i v) ^ 2 = unifW Ω v * Qrv Ω P i v := by
      intro v _
      exact Real.sq_sqrt (mul_nonneg (unifW_nonneg Ω v) (Qrv_mem_Icc Ω P i v).1)
    have h3 : ∀ v ∈ Ωy, Real.sqrt (unifW Ω v * h (Qrv Ω P i v)) ^ 2 = unifW Ω v * h (Qrv Ω P i v) := by
      intro v _
      have hq := Qrv_mem_Icc Ω P i v
      exact Real.sq_sqrt (mul_nonneg (unifW_nonneg Ω v) (h_nonneg hq.1 hq.2))
    rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, Finset.sum_congr rfl h3] at hcs
    -- Substitute tower property sum_fibre_Qrv!
    have htower := sum_fibre_Qrv Ω hSP i y
    rw [htower] at hcs
    have hB_eq : condProb Ω S i y * (∑ v ∈ Ωy, unifW Ω v * h (Qrv Ω P i v)) = B y := by
      simp only [B, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro v hv
      have hvy : restrictVec S v = y := (Finset.mem_filter.mp hv).2
      unfold Qrv; rw [hvy]; ring
    linarith [show fibreProb Ω S y * condProb Ω S i y * (∑ v ∈ Ωy, unifW Ω v * h (Qrv Ω P i v))
      = fibreProb Ω S y * B y by rw [mul_assoc, hB_eq]]
  -- Outer Cauchy–Schwarz over y ∈ Y: (∑ A y)^2 ≤ (∑ fibreProb Ω S y) * (∑ B y) = 1 * (∑ B y)!
  have hA_le : ∀ y ∈ Y, A y ≤ Real.sqrt (fibreProb Ω S y) * Real.sqrt (B y) := by
    intro y hy
    have hA_nn : 0 ≤ A y := Finset.sum_nonneg fun v _ => mul_nonneg (unifW_nonneg Ω v) (Real.sqrt_nonneg _)
    have hB_nn : 0 ≤ B y := Finset.sum_nonneg fun v _ => by
      have hqS := Qrv_mem_Icc Ω S i v
      have hqP := Qrv_mem_Icc Ω P i v
      exact mul_nonneg (mul_nonneg (unifW_nonneg Ω v) hqS.1) (h_nonneg hqP.1 hqP.2)
    rw [← Real.sqrt_mul (fibreProb_nonneg Ω S y)]
    calc A y = Real.sqrt ((A y) ^ 2) := (Real.sqrt_sq hA_nn).symm
      _ ≤ Real.sqrt (fibreProb Ω S y * B y) := Real.sqrt_le_sqrt (hfib y hy)
  have hsumA_nn : 0 ≤ ∑ y ∈ Y, A y :=
    Finset.sum_nonneg fun y _ => Finset.sum_nonneg fun v _ =>
      mul_nonneg (unifW_nonneg Ω v) (Real.sqrt_nonneg _)
  have hsum_le : ∑ y ∈ Y, A y ≤ ∑ y ∈ Y, Real.sqrt (fibreProb Ω S y) * Real.sqrt (B y) :=
    Finset.sum_le_sum hA_le
  have hsq_le : (∑ y ∈ Y, A y) ^ 2 ≤ (∑ y ∈ Y, Real.sqrt (fibreProb Ω S y) * Real.sqrt (B y)) ^ 2 :=
    pow_le_pow_left₀ hsumA_nn hsum_le 2
  have hcs2 := Finset.sum_mul_sq_le_sq_mul_sq Y
    (fun y => Real.sqrt (fibreProb Ω S y)) (fun y => Real.sqrt (B y))
  have hfp_sq : ∑ y ∈ Y, Real.sqrt (fibreProb Ω S y) ^ 2 = 1 := by
    have h1 : ∀ y ∈ Y, Real.sqrt (fibreProb Ω S y) ^ 2 = fibreProb Ω S y := fun y _ =>
      Real.sq_sqrt (fibreProb_nonneg Ω S y)
    rw [Finset.sum_congr rfl h1]
    exact (sum_pushProb Ω (unifW Ω) (restrictVec S)).trans (sum_unifW hΩ)
  have hB_sq : ∑ y ∈ Y, Real.sqrt (B y) ^ 2 = ∑ y ∈ Y, B y := by
    apply Finset.sum_congr rfl; intro y _
    have hB_nn : 0 ≤ B y := Finset.sum_nonneg fun v _ => by
      have hqS := Qrv_mem_Icc Ω S i v
      have hqP := Qrv_mem_Icc Ω P i v
      exact mul_nonneg (mul_nonneg (unifW_nonneg Ω v) hqS.1) (h_nonneg hqP.1 hqP.2)
    exact Real.sq_sqrt hB_nn
  rw [hfp_sq, one_mul, hB_sq] at hcs2
  exact le_trans hsq_le hcs2

end UCBound
