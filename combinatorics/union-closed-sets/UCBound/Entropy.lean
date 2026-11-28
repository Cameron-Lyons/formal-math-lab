module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.BigOperators
public import UCBound.Basic

@[expose] public section

/-!
# Finite Shannon Entropy, Conditional Entropy, Chain Rule, and Total Correlation

Clean, self-contained finite-distribution Shannon entropy library for binary vectors `Fin n → Bool`.
Zero `sorry`, zero extra axioms.
-/

noncomputable section

namespace UCBound

open scoped BigOperators
open Real Finset

/-- Entropy summand `η(p) = -p log p` (with `η(0) = 0`). -/
def entTerm (p : ℝ) : ℝ := -p * Real.log p

@[simp] lemma entTerm_zero : entTerm 0 = 0 := by simp [entTerm]
@[simp] lemma entTerm_one : entTerm 1 = 0 := by simp [entTerm]

lemma entTerm_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : 0 ≤ entTerm p := by
  unfold entTerm
  rcases hp0.eq_or_lt with rfl | hp0'
  · simp
  · have := Real.log_nonpos hp0 hp1
    nlinarith

/-- Finite Shannon entropy of a weight function `p : α → ℝ` over a finite set `s`. -/
def shannonEnt {α : Type*} (s : Finset α) (p : α → ℝ) : ℝ :=
  ∑ a ∈ s, entTerm (p a)

lemma shannonEnt_nonneg {α : Type*} (s : Finset α) (p : α → ℝ)
    (hp0 : ∀ a ∈ s, 0 ≤ p a) (hp1 : ∀ a ∈ s, p a ≤ 1) :
    0 ≤ shannonEnt s p :=
  Finset.sum_nonneg fun a ha => entTerm_nonneg (hp0 a ha) (hp1 a ha)

/-- Gibbs / Jensen upper bound: `H(p) ≤ log |s|` for any probability distribution on `s`. -/
lemma shannonEnt_le_log_card {α : Type*} (s : Finset α) (p : α → ℝ)
    (hp0 : ∀ a ∈ s, 0 ≤ p a) (hsum : ∑ a ∈ s, p a = 1) (hs : s.Nonempty) :
    shannonEnt s p ≤ Real.log s.card := by
  have hcard_pos : (0 : ℝ) < s.card := Nat.cast_pos.mpr hs.card_pos
  have hkey : ∑ a ∈ s, (-p a * Real.log (p a) - p a * Real.log s.card) ≤ 0 := by
    have hterm : ∀ a ∈ s, -p a * Real.log (p a) - p a * Real.log s.card ≤ 1 / (s.card : ℝ) - p a := by
      intro a ha
      rcases (hp0 a ha).eq_or_lt with hpa0 | hpa_pos
      · rw [← hpa0]; simp
      · have hpos : 0 < (1 / (s.card : ℝ)) / p a := div_pos (one_div_pos.mpr hcard_pos) hpa_pos
        have hlog := Real.log_le_sub_one_of_pos hpos
        rw [Real.log_div (ne_of_gt (one_div_pos.mpr hcard_pos)) (ne_of_gt hpa_pos),
            Real.log_div one_ne_zero (ne_of_gt hcard_pos), Real.log_one, zero_sub] at hlog
        have hmul := mul_le_mul_of_nonneg_left hlog (le_of_lt hpa_pos)
        have hcancel : p a * (1 / (s.card : ℝ) / p a - 1) = 1 / (s.card : ℝ) - p a := by
          field_simp [ne_of_gt hpa_pos, ne_of_gt hcard_pos]
        rw [hcancel] at hmul
        linarith
    calc ∑ a ∈ s, (-p a * Real.log (p a) - p a * Real.log s.card)
        ≤ ∑ a ∈ s, (1 / (s.card : ℝ) - p a) := Finset.sum_le_sum hterm
      _ = (∑ _a ∈ s, (1 / (s.card : ℝ))) - ∑ a ∈ s, p a := by rw [Finset.sum_sub_distrib]
      _ = s.card * (1 / (s.card : ℝ)) - 1 := by rw [Finset.sum_const, nsmul_eq_mul, hsum]
      _ = 0 := by field_simp [ne_of_gt hcard_pos]; ring
  unfold shannonEnt entTerm
  have hsum2 : ∑ a ∈ s, (-p a * Real.log (p a) - p a * Real.log s.card)
      = (∑ a ∈ s, -p a * Real.log (p a)) - (∑ a ∈ s, p a) * Real.log s.card := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [hsum2, hsum, one_mul] at hkey
  linarith

/-- Uniform distribution on `s` has entropy `log |s|`. -/
lemma shannonEnt_unif {α : Type*} (s : Finset α) (hs : s.Nonempty) :
    shannonEnt s (fun _ => (1 : ℝ) / s.card) = Real.log s.card := by
  unfold shannonEnt entTerm
  have hcard_pos : (0 : ℝ) < s.card := Nat.cast_pos.mpr hs.card_pos
  rw [Finset.sum_const, nsmul_eq_mul, Real.log_div one_ne_zero (ne_of_gt hcard_pos), Real.log_one]
  field_simp [ne_of_gt hcard_pos]
  ring

/-- Log-sum inequality for nonnegative reals. -/
lemma sum_mul_log_div_nonneg {α : Type*} (s : Finset α) (x y : α → ℝ)
    (hx : ∀ a ∈ s, 0 ≤ x a) (hy : ∀ a ∈ s, 0 ≤ y a)
    (habs : ∀ a ∈ s, y a = 0 → x a = 0) :
    (∑ a ∈ s, x a) * Real.log ((∑ a ∈ s, x a) / (∑ a ∈ s, y a))
      ≤ ∑ a ∈ s, x a * Real.log (x a / y a) := by
  set X := ∑ a ∈ s, x a
  set Y := ∑ a ∈ s, y a
  have hX0 : 0 ≤ X := Finset.sum_nonneg hx
  have hY0 : 0 ≤ Y := Finset.sum_nonneg hy
  rcases hX0.eq_or_lt with hXeq | hX
  · have hx0 : ∀ a ∈ s, x a = 0 := fun a ha =>
      (Finset.sum_eq_zero_iff_of_nonneg hx).mp hXeq.symm a ha
    rw [← hXeq, zero_mul]
    exact le_of_eq (Finset.sum_eq_zero fun a ha => by rw [hx0 a ha, zero_mul]).symm
  have hY : 0 < Y := by
    rcases hY0.eq_or_lt with hYeq | hYpos
    · exfalso
      have hy0 : ∀ a ∈ s, y a = 0 := fun a ha =>
        (Finset.sum_eq_zero_iff_of_nonneg hy).mp hYeq.symm a ha
      have hx0 : X = 0 := Finset.sum_eq_zero fun a ha => habs a ha (hy0 a ha)
      linarith
    · exact hYpos
  have hterm : ∀ a ∈ s, x a - (X / Y) * y a ≤ x a * Real.log (x a / y a) - x a * Real.log (X / Y) := by
    intro a ha
    rcases (hx a ha).eq_or_lt with hxa0 | hxa_pos
    · rw [← hxa0]; simp
      exact mul_nonneg (div_nonneg (le_of_lt hX) (le_of_lt hY)) (hy a ha)
    · have hya_pos : 0 < y a := by
        rcases (hy a ha).eq_or_lt with hya0 | hya_pos
        · exfalso; exact ne_of_gt hxa_pos (habs a ha hya0.symm)
        · exact hya_pos
      have hr_pos : 0 < (y a * X) / (x a * Y) :=
        div_pos (mul_pos hya_pos hX) (mul_pos hxa_pos hY)
      have hlog := Real.log_le_sub_one_of_pos hr_pos
      have hlog_eq : Real.log ((y a * X) / (x a * Y))
          = Real.log (X / Y) - Real.log (x a / y a) := by
        rw [Real.log_div (ne_of_gt (mul_pos hya_pos hX)) (ne_of_gt (mul_pos hxa_pos hY)),
            Real.log_mul (ne_of_gt hya_pos) (ne_of_gt hX),
            Real.log_mul (ne_of_gt hxa_pos) (ne_of_gt hY),
            Real.log_div (ne_of_gt hX) (ne_of_gt hY),
            Real.log_div (ne_of_gt hxa_pos) (ne_of_gt hya_pos)]
        ring
      rw [hlog_eq] at hlog
      have hmul := mul_le_mul_of_nonneg_left hlog (le_of_lt hxa_pos)
      have hcancel : x a * (y a * X / (x a * Y) - 1) = (X / Y) * y a - x a := by
        field_simp [ne_of_gt hxa_pos, ne_of_gt hY]
      rw [hcancel] at hmul
      linarith
  have hsum := Finset.sum_le_sum hterm
  have hL : ∑ a ∈ s, (x a - (X / Y) * y a) = 0 := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    change X - (X / Y) * Y = 0
    field_simp [ne_of_gt hY]; ring
  have hR : ∑ a ∈ s, (x a * Real.log (x a / y a) - x a * Real.log (X / Y))
      = (∑ a ∈ s, x a * Real.log (x a / y a)) - X * Real.log (X / Y) := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [hL, hR] at hsum
  linarith

/-- Pushforward distribution of a function `f : Ω → β` under probability weights `w : Ω → ℝ`. -/
def pushProb {Ω β : Type*} [DecidableEq β] (s : Finset Ω) (w : Ω → ℝ) (f : Ω → β) (b : β) : ℝ :=
  ∑ ω ∈ s.filter (fun ω => f ω = b), w ω

lemma pushProb_nonneg {Ω β : Type*} [DecidableEq β] (s : Finset Ω) (w : Ω → ℝ)
    (hw : ∀ ω ∈ s, 0 ≤ w ω) (f : Ω → β) (b : β) :
    0 ≤ pushProb s w f b :=
  Finset.sum_nonneg fun ω hω => hw ω (Finset.mem_filter.mp hω).1

lemma pushProb_eq_zero_of_not_mem_image {Ω β : Type*} [DecidableEq β]
    (s : Finset Ω) (w : Ω → ℝ) (f : Ω → β) {b : β} (hb : b ∉ s.image f) :
    pushProb s w f b = 0 := by
  unfold pushProb
  apply Finset.sum_eq_zero
  intro ω hω
  exfalso
  have h := Finset.mem_filter.mp hω
  exact hb (Finset.mem_image.mpr ⟨ω, h.1, h.2⟩)

lemma sum_pushProb_superset {Ω β : Type*} [DecidableEq β]
    (s : Finset Ω) (w : Ω → ℝ) (f : Ω → β) (t : Finset β) (ht : s.image f ⊆ t) :
    ∑ b ∈ t, pushProb s w f b = ∑ ω ∈ s, w ω := by
  unfold pushProb
  rw [← Finset.sum_fiberwise_of_maps_to (g := f) (t := t)
        (fun ω hω => ht (Finset.mem_image_of_mem f hω))]

lemma sum_pushProb {Ω β : Type*} [DecidableEq β] (s : Finset Ω) (w : Ω → ℝ) (f : Ω → β) :
    ∑ b ∈ s.image f, pushProb s w f b = ∑ ω ∈ s, w ω :=
  sum_pushProb_superset s w f (s.image f) Subset.rfl

lemma pushProb_le_one {Ω β : Type*} [DecidableEq β] (s : Finset Ω) (w : Ω → ℝ)
    (hw : ∀ ω ∈ s, 0 ≤ w ω) (hsum : ∑ ω ∈ s, w ω = 1) (f : Ω → β) (b : β) :
    pushProb s w f b ≤ 1 := by
  unfold pushProb
  calc ∑ ω ∈ s.filter (fun ω => f ω = b), w ω
      ≤ ∑ ω ∈ s, w ω := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun ω hω _ => hw ω hω)
    _ = 1 := hsum

lemma sum_pushProb_pair {Ω β γ : Type*} [DecidableEq β] [DecidableEq γ]
    (s : Finset Ω) (w : Ω → ℝ) (f : Ω → β) (g : Ω → γ) (y : γ) :
    ∑ x ∈ s.image f, pushProb s w (fun ω => (f ω, g ω)) (x, y) = pushProb s w g y := by
  unfold pushProb
  have hrew : ∀ x, s.filter (fun ω => (f ω, g ω) = (x, y))
      = (s.filter (fun ω => g ω = y)).filter (fun ω => f ω = x) := by
    intro x; ext ω; simp only [Finset.mem_filter, Prod.mk.injEq]; tauto
  simp_rw [hrew]
  rw [← Finset.sum_fiberwise_of_maps_to (g := f) (t := s.image f)
        (fun ω hω => Finset.mem_image_of_mem f (Finset.mem_filter.mp hω).1)]

/-- Entropy of a random variable `f : Ω → β` under probability weights `w` on `s`. -/
def rvEnt {Ω β : Type*} [DecidableEq β] (s : Finset Ω) (w : Ω → ℝ) (f : Ω → β) : ℝ :=
  shannonEnt (s.image f) (pushProb s w f)

lemma rvEnt_eq_sum_superset {Ω β : Type*} [DecidableEq β]
    (s : Finset Ω) (w : Ω → ℝ) (f : Ω → β) (t : Finset β) (ht : s.image f ⊆ t) :
    rvEnt s w f = ∑ b ∈ t, entTerm (pushProb s w f b) := by
  unfold rvEnt shannonEnt
  apply Finset.sum_subset ht
  intro b _ hnot
  rw [pushProb_eq_zero_of_not_mem_image s w f hnot, entTerm_zero]

lemma rvEnt_nonneg {Ω β : Type*} [DecidableEq β] (s : Finset Ω) (w : Ω → ℝ)
    (hw : ∀ ω ∈ s, 0 ≤ w ω) (hsum : ∑ ω ∈ s, w ω = 1) (f : Ω → β) :
    0 ≤ rvEnt s w f :=
  shannonEnt_nonneg _ _ (fun b _ => pushProb_nonneg s w hw f b)
    (fun b _ => pushProb_le_one s w hw hsum f b)

lemma rvEnt_le_log_card {Ω β : Type*} [DecidableEq β] (s : Finset Ω) (w : Ω → ℝ)
    (hw : ∀ ω ∈ s, 0 ≤ w ω) (hsum : ∑ ω ∈ s, w ω = 1) (hs : s.Nonempty) (f : Ω → β) :
    rvEnt s w f ≤ Real.log (s.image f).card :=
  shannonEnt_le_log_card _ _ (fun b _ => pushProb_nonneg s w hw f b)
    (by rw [sum_pushProb, hsum]) (hs.image f)

/-- Entropy is invariant under injective post-composition. -/
lemma rvEnt_comp_injective {Ω β γ : Type*} [DecidableEq β] [DecidableEq γ]
    (s : Finset Ω) (w : Ω → ℝ) (f : Ω → β) {ψ : β → γ} (hψ : Function.Injective ψ) :
    rvEnt s w (fun ω => ψ (f ω)) = rvEnt s w f := by
  unfold rvEnt shannonEnt
  have himg : s.image (fun ω => ψ (f ω)) = (s.image f).image ψ := by
    ext c; simp
  rw [himg, Finset.sum_image (fun a _ b _ hab => hψ hab)]
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  unfold pushProb
  congr 1
  ext ω
  simp [hψ.eq_iff]

/-- Conditional entropy `H(X | Y) = H(X, Y) - H(Y)`. -/
def condRvEnt {Ω β γ : Type*} [DecidableEq β] [DecidableEq γ]
    (s : Finset Ω) (w : Ω → ℝ) (f : Ω → β) (g : Ω → γ) : ℝ :=
  rvEnt s w (fun ω => (f ω, g ω)) - rvEnt s w g

/-- Exact fibre sum formula for conditional entropy:
    `H(f | g) = ∑ y, ∑ x, -P(f=x, g=y) * log(P(f=x, g=y) / P(g=y))`. -/
lemma condRvEnt_eq_sum_fibres {Ω β γ : Type*} [DecidableEq β] [DecidableEq γ]
    (s : Finset Ω) (w : Ω → ℝ) (hw : ∀ ω ∈ s, 0 ≤ w ω) (f : Ω → β) (g : Ω → γ) :
    condRvEnt s w f g =
      ∑ y ∈ s.image g, ∑ x ∈ s.image f,
        -(pushProb s w (fun ω => (f ω, g ω)) (x, y))
          * Real.log (pushProb s w (fun ω => (f ω, g ω)) (x, y) / pushProb s w g y) := by
  unfold condRvEnt
  have hsub : s.image (fun ω => (f ω, g ω)) ⊆ (s.image f) ×ˢ (s.image g) := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨ω, hω, rfl⟩
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem f hω, Finset.mem_image_of_mem g hω⟩
  rw [rvEnt_eq_sum_superset s w (fun ω => (f ω, g ω)) ((s.image f) ×ˢ (s.image g)) hsub]
  rw [Finset.sum_product_right]
  unfold rvEnt shannonEnt
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro y _
  -- Goal: (∑ x, -P(x,y) log P(x,y)) - (-P(y) log P(y)) = ∑ x, -P(x,y) log(P(x,y)/P(y))
  have hpy_sum : ∑ x ∈ s.image f, pushProb s w (fun ω => (f ω, g ω)) (x, y) = pushProb s w g y :=
    sum_pushProb_pair s w f g y
  have hterm : ∀ x ∈ s.image f,
      entTerm (pushProb s w (fun ω => (f ω, g ω)) (x, y))
        - (-pushProb s w (fun ω => (f ω, g ω)) (x, y) * Real.log (pushProb s w g y))
      = -(pushProb s w (fun ω => (f ω, g ω)) (x, y))
          * Real.log (pushProb s w (fun ω => (f ω, g ω)) (x, y) / pushProb s w g y) := by
    intro x hx
    set pxy := pushProb s w (fun ω => (f ω, g ω)) (x, y)
    set py := pushProb s w g y
    have hpxy0 : 0 ≤ pxy := pushProb_nonneg s w hw _ _
    have hpy0 : 0 ≤ py := pushProb_nonneg s w hw _ _
    rcases hpxy0.eq_or_lt with h0 | hpxy_pos
    · rw [← h0]; simp [entTerm]
    · have hpy_pos : 0 < py := by
        have hle : pxy ≤ py := by
          rw [← hpy_sum]
          exact Finset.single_le_sum (f := fun x' => pushProb s w (fun ω => (f ω, g ω)) (x', y))
            (fun x' _ => pushProb_nonneg s w hw _ _) hx
        linarith
      unfold entTerm
      rw [Real.log_div (ne_of_gt hpxy_pos) (ne_of_gt hpy_pos)]
      ring
  have hsub2 : (∑ x ∈ s.image f, entTerm (pushProb s w (fun ω => (f ω, g ω)) (x, y)))
      - entTerm (pushProb s w g y)
      = ∑ x ∈ s.image f, (entTerm (pushProb s w (fun ω => (f ω, g ω)) (x, y))
          - (-pushProb s w (fun ω => (f ω, g ω)) (x, y) * Real.log (pushProb s w g y))) := by
    rw [Finset.sum_sub_distrib]
    congr 1
    unfold entTerm
    rw [← Finset.sum_mul, Finset.sum_neg_distrib, hpy_sum]
  rw [hsub2]
  exact Finset.sum_congr rfl hterm

/-- Conditional entropy is nonnegative. -/
lemma condRvEnt_nonneg {Ω β γ : Type*} [DecidableEq β] [DecidableEq γ]
    (s : Finset Ω) (w : Ω → ℝ) (hw : ∀ ω ∈ s, 0 ≤ w ω) (f : Ω → β) (g : Ω → γ) :
    0 ≤ condRvEnt s w f g := by
  rw [condRvEnt_eq_sum_fibres s w hw f g]
  apply Finset.sum_nonneg; intro y _
  apply Finset.sum_nonneg; intro x hx
  set pxy := pushProb s w (fun ω => (f ω, g ω)) (x, y)
  set py := pushProb s w g y
  have hpxy0 : 0 ≤ pxy := pushProb_nonneg s w hw _ _
  rcases hpxy0.eq_or_lt with h0 | hpxy_pos
  · rw [← h0]; simp
  · have hle : pxy ≤ py := by
      change pushProb s w (fun ω => (f ω, g ω)) (x, y) ≤ pushProb s w g y
      rw [← sum_pushProb_pair s w f g y]
      exact Finset.single_le_sum (f := fun x' => pushProb s w (fun ω => (f ω, g ω)) (x', y))
        (fun x' _ => pushProb_nonneg s w hw _ _) hx
    have hpy_pos : 0 < py := lt_of_lt_of_le hpxy_pos hle
    have hdiv1 : pxy / py ≤ 1 := (div_le_one hpy_pos).mpr hle
    have hlog : Real.log (pxy / py) ≤ 0 := Real.log_nonpos (div_nonneg hpxy0 (le_of_lt hpy_pos)) hdiv1
    nlinarith

/-- Conditioning reduces entropy: if `g = ψ ∘ t`, then `H(f | t) ≤ H(f | g)`. -/
lemma condRvEnt_le_of_comp {Ω β γ δ : Type*} [DecidableEq β] [DecidableEq γ] [DecidableEq δ]
    (s : Finset Ω) (w : Ω → ℝ) (hw : ∀ ω ∈ s, 0 ≤ w ω)
    (f : Ω → β) (t : Ω → δ) (ψ : δ → γ) :
    condRvEnt s w f t ≤ condRvEnt s w f (fun ω => ψ (t ω)) := by
  rw [condRvEnt_eq_sum_fibres s w hw f t, condRvEnt_eq_sum_fibres s w hw f (fun ω => ψ (t ω))]
  -- Swap sums: sum over x ∈ s.image f outside!
  rw [Finset.sum_comm, Finset.sum_comm (s := s.image (fun ω => ψ (t ω)))]
  apply Finset.sum_le_sum
  intro x _
  -- Group z ∈ s.image t by ψ z = y!
  have hmaps : ∀ z ∈ s.image t, ψ z ∈ s.image (fun ω => ψ (t ω)) := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨ω, hω, rfl⟩
    exact Finset.mem_image_of_mem _ hω
  rw [← Finset.sum_fiberwise_of_maps_to (g := ψ) hmaps]
  apply Finset.sum_le_sum
  intro y _
  -- Apply log-sum inequality to z ∈ (s.image t).filter (ψ z = y)!
  set Fz := (s.image t).filter (fun z => ψ z = y)
  have hsum_x : ∑ z ∈ Fz, pushProb s w (fun ω => (f ω, t ω)) (x, z)
      = pushProb s w (fun ω => (f ω, ψ (t ω))) (x, y) := by
    unfold pushProb
    have hrew : ∀ z, s.filter (fun ω => (f ω, t ω) = (x, z))
        = (s.filter (fun ω => (f ω, ψ (t ω)) = (x, y))).filter (fun ω => t ω = z) → True := fun _ _ => trivial
    -- Partition s.filter (f ω = x ∧ ψ (t ω) = y) by t ω ∈ Fz:
    have hpart : ∀ z ∈ Fz, s.filter (fun ω => (f ω, t ω) = (x, z))
        = (s.filter (fun ω => (f ω, ψ (t ω)) = (x, y))).filter (fun ω => t ω = z) := by
      intro z hz
      have hψz : ψ z = y := (Finset.mem_filter.mp hz).2
      ext ω; simp only [Finset.mem_filter, Prod.mk.injEq]
      constructor
      · rintro ⟨hω, hfx, htz⟩; exact ⟨⟨hω, hfx, htz ▸ hψz⟩, htz⟩
      · rintro ⟨⟨hω, hfx, _⟩, htz⟩; exact ⟨hω, hfx, htz⟩
    rw [Finset.sum_congr rfl fun z hz => by rw [hpart z hz]]
    rw [← Finset.sum_fiberwise_of_maps_to (g := t) (t := Fz)]
    intro ω hω
    have h := Finset.mem_filter.mp hω
    exact Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem t h.1, (Prod.mk.inj h.2).2⟩
  have hsum_y : ∑ z ∈ Fz, pushProb s w t z = pushProb s w (fun ω => ψ (t ω)) y := by
    unfold pushProb
    have hpart : ∀ z ∈ Fz, s.filter (fun ω => t ω = z)
        = (s.filter (fun ω => ψ (t ω) = y)).filter (fun ω => t ω = z) := by
      intro z hz
      have hψz : ψ z = y := (Finset.mem_filter.mp hz).2
      ext ω; simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hω, htz⟩; exact ⟨⟨hω, htz ▸ hψz⟩, htz⟩
      · rintro ⟨⟨hω, _⟩, htz⟩; exact ⟨hω, htz⟩
    rw [Finset.sum_congr rfl fun z hz => by rw [hpart z hz]]
    rw [← Finset.sum_fiberwise_of_maps_to (g := t) (t := Fz)]
    intro ω hω
    have h := Finset.mem_filter.mp hω
    exact Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem t h.1, h.2⟩
  have hls := sum_mul_log_div_nonneg Fz
    (fun z => pushProb s w (fun ω => (f ω, t ω)) (x, z))
    (fun z => pushProb s w t z)
    (fun z _ => pushProb_nonneg s w hw _ _)
    (fun z _ => pushProb_nonneg s w hw _ _)
    (fun z _ hy0 => by
      have hle : pushProb s w (fun ω => (f ω, t ω)) (x, z) ≤ pushProb s w t z := by
        unfold pushProb
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro ω hω; exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hω).1, (Prod.mk.inj (Finset.mem_filter.mp hω).2).2⟩
        · intro ω hω _; exact hw ω (Finset.mem_filter.mp hω).1
      linarith [pushProb_nonneg s w hw (fun ω => (f ω, t ω)) (x, z)])
  rw [hsum_x, hsum_y] at hls
  simp_rw [neg_mul]
  rw [Finset.sum_neg_distrib]
  linarith

/-- Binary conditional entropy formula: for `f : Ω → Bool`,
    `H(f | g) = ∑ y, P(g = y) * h(P(f = true | g = y))`. -/
lemma condRvEnt_bool_eq_sum_h {Ω γ : Type*} [DecidableEq γ]
    (s : Finset Ω) (w : Ω → ℝ) (hw : ∀ ω ∈ s, 0 ≤ w ω)
    (f : Ω → Bool) (g : Ω → γ) :
    condRvEnt s w f g =
      ∑ y ∈ s.image g,
        pushProb s w g y * h (pushProb s w (fun ω => (f ω, g ω)) (true, y) / pushProb s w g y) := by
  rw [condRvEnt_eq_sum_fibres s w hw f g]
  apply Finset.sum_congr rfl
  intro y _
  set py := pushProb s w g y
  set pT := pushProb s w (fun ω => (f ω, g ω)) (true, y)
  set pF := pushProb s w (fun ω => (f ω, g ω)) (false, y)
  have hsum_b : ∑ x ∈ (Finset.univ : Finset Bool),
      -(pushProb s w (fun ω => (f ω, g ω)) (x, y))
        * Real.log (pushProb s w (fun ω => (f ω, g ω)) (x, y) / py)
      = ∑ x ∈ s.image f,
      -(pushProb s w (fun ω => (f ω, g ω)) (x, y))
        * Real.log (pushProb s w (fun ω => (f ω, g ω)) (x, y) / py) := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro x _ hnot
    have hp0 : pushProb s w (fun ω => (f ω, g ω)) (x, y) = 0 := by
      unfold pushProb
      apply Finset.sum_eq_zero; intro ω hω; exfalso
      have h := Finset.mem_filter.mp hω
      exact hnot (Finset.mem_image.mpr ⟨ω, h.1, (Prod.mk.inj h.2).1⟩)
    rw [hp0]; simp
  rw [← hsum_b]
  have hTF : pT + pF = py := by
    have := sum_pushProb_pair s w f g y
    have hsub : ∑ x ∈ (Finset.univ : Finset Bool), pushProb s w (fun ω => (f ω, g ω)) (x, y)
        = ∑ x ∈ s.image f, pushProb s w (fun ω => (f ω, g ω)) (x, y) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro x _ hnot
      unfold pushProb; apply Finset.sum_eq_zero; intro ω hω; exfalso
      have h := Finset.mem_filter.mp hω
      exact hnot (Finset.mem_image.mpr ⟨ω, h.1, (Prod.mk.inj h.2).1⟩)
    rw [← hsub] at this
    simpa [Fintype.sum_bool, pT, pF, py] using this
  have hpT0 : 0 ≤ pT := pushProb_nonneg s w hw _ _
  have hpF0 : 0 ≤ pF := pushProb_nonneg s w hw _ _
  have hpy0 : 0 ≤ py := pushProb_nonneg s w hw _ _
  simp only [Fintype.sum_bool]
  change -pT * Real.log (pT / py) + -pF * Real.log (pF / py) = py * h (pT / py)
  rcases hpy0.eq_or_lt with h0 | hpy_pos
  · have hT0 : pT = 0 := by linarith
    have hF0 : pF = 0 := by linarith
    rw [← h0, hT0, hF0]; simp
  · have h1m : 1 - pT / py = pF / py := by
      field_simp [ne_of_gt hpy_pos]; linarith
    unfold h
    rw [h1m]
    field_simp [ne_of_gt hpy_pos]
    ring

/-- Unconditional binary entropy formula: `H(f) = h(P(f = true))`. -/
lemma rvEnt_bool_eq_h {Ω : Type*} (s : Finset Ω) (w : Ω → ℝ)
    (hw : ∀ ω ∈ s, 0 ≤ w ω) (hsum : ∑ ω ∈ s, w ω = 1) (f : Ω → Bool) :
    rvEnt s w f = h (pushProb s w f true) := by
  have hconst : rvEnt s w (fun _ : Ω => ()) = 0 := by
    rcases s.eq_empty_or_nonempty with rfl | hs
    · simp [rvEnt, shannonEnt]
    · unfold rvEnt shannonEnt
      have himg : s.image (fun _ : Ω => ()) = {()} := Finset.image_const hs ()
      rw [himg, Finset.sum_singleton]
      have hp : pushProb s w (fun _ : Ω => ()) () = 1 := by
        unfold pushProb; simp [hsum]
      rw [hp, entTerm_one]
  have hbij : rvEnt s w f = condRvEnt s w f (fun _ : Ω => ()) := by
    unfold condRvEnt
    rw [hconst, sub_zero]
    exact (rvEnt_comp_injective s w f (ψ := fun b => (b, ())) (fun a b h => (Prod.mk.inj h).1)).symm
  rw [hbij, condRvEnt_bool_eq_sum_h s w hw f (fun _ => ())]
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp [pushProb]
  · have himg : s.image (fun _ : Ω => ()) = {()} := Finset.image_const hs ()
    rw [himg, Finset.sum_singleton]
    have hp : pushProb s w (fun _ : Ω => ()) () = 1 := by unfold pushProb; simp [hsum]
    have hpT : pushProb s w (fun ω => (f ω, ())) (true, ()) = pushProb s w f true := by
      unfold pushProb; congr 1; ext ω; simp
    rw [hp, hpT, one_mul, div_one]

/-- Chain rule for three variables: `H(X, Y | Z) = H(Y | Z) + H(X | Y, Z)`. -/
lemma condRvEnt_pair {Ω α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (s : Finset Ω) (w : Ω → ℝ) (f : Ω → α) (g : Ω → β) (k : Ω → γ) :
    condRvEnt s w (fun ω => (f ω, g ω)) k =
      condRvEnt s w g k + condRvEnt s w f (fun ω => (g ω, k ω)) := by
  unfold condRvEnt
  have h1 : rvEnt s w (fun ω => ((f ω, g ω), k ω)) = rvEnt s w (fun ω => (f ω, (g ω, k ω))) := by
    let ψ : (α × β) × γ → α × (β × γ) := fun p => (p.1.1, (p.1.2, p.2))
    have hψ : Function.Injective ψ := by
      intro a b h; simp only [ψ, Prod.mk.injEq] at h
      ext <;> simp [h]
    exact (rvEnt_comp_injective s w (fun ω => ((f ω, g ω), k ω)) hψ).symm
  linarith

/-- Chain rule for restriction of a vector `A : Ω → Fin n → Bool` to a subset `S : Finset (Fin n)`. -/
def restrictVec {n : ℕ} (S : Finset (Fin n)) (v : Fin n → Bool) : Fin n → Bool :=
  fun i => if i ∈ S then v i else false

lemma restrictVec_empty {n : ℕ} (v : Fin n → Bool) :
    restrictVec (∅ : Finset (Fin n)) v = fun _ => false := by
  ext i; simp [restrictVec]

lemma restrictVec_univ {n : ℕ} (v : Fin n → Bool) :
    restrictVec (Finset.univ : Finset (Fin n)) v = v := by
  ext i; simp [restrictVec]

/-- Entropy of `A_S` under weights `w` on `s`. -/
def subEnt {Ω : Type*} {n : ℕ} (s : Finset Ω) (w : Ω → ℝ) (A : Ω → Fin n → Bool)
    (S : Finset (Fin n)) : ℝ :=
  rvEnt s w (fun ω => restrictVec S (A ω))

/-- Conditional entropy of `A_i` given `A_S`. -/
def coordCondEnt {Ω : Type*} {n : ℕ} (s : Finset Ω) (w : Ω → ℝ) (A : Ω → Fin n → Bool)
    (i : Fin n) (S : Finset (Fin n)) : ℝ :=
  condRvEnt s w (fun ω => A ω i) (fun ω => restrictVec S (A ω))

lemma subEnt_empty {Ω : Type*} {n : ℕ} (s : Finset Ω) (w : Ω → ℝ)
    (hsum : ∑ ω ∈ s, w ω = 1) (A : Ω → Fin n → Bool) :
    subEnt s w A ∅ = 0 := by
  unfold subEnt
  simp_rw [restrictVec_empty]
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp [rvEnt, shannonEnt]
  · unfold rvEnt shannonEnt
    have himg : s.image (fun _ : Ω => (fun _ : Fin n => false)) = {fun _ => false} :=
      Finset.image_const hs (fun _ => false)
    rw [himg, Finset.sum_singleton]
    have hp : pushProb s w (fun _ : Ω => (fun _ : Fin n => false)) (fun _ => false) = 1 := by
      unfold pushProb; simp [hsum]
    rw [hp, entTerm_one]

lemma subEnt_univ {Ω : Type*} {n : ℕ} (s : Finset Ω) (w : Ω → ℝ) (A : Ω → Fin n → Bool) :
    subEnt s w A Finset.univ = rvEnt s w A := by
  unfold subEnt; simp_rw [restrictVec_univ]

/-- Adding one coordinate `i ∉ S` to `S`: `H(A_{insert i S}) = H(A_S) + H(A_i | A_S)`. -/
lemma subEnt_insert {Ω : Type*} {n : ℕ} (s : Finset Ω) (w : Ω → ℝ) (A : Ω → Fin n → Bool)
    {i : Fin n} {S : Finset (Fin n)} (hi : i ∉ S) :
    subEnt s w A (insert i S) = subEnt s w A S + coordCondEnt s w A i S := by
  unfold subEnt coordCondEnt condRvEnt
  suffices heq : rvEnt s w (fun ω => restrictVec (insert i S) (A ω))
      = rvEnt s w (fun ω => (A ω i, restrictVec S (A ω))) by linarith
  -- Map (b, v) ↦ Function.update v i b is injective on the image (since v i = false when i ∉ S)!
  let ψ : Bool × (Fin n → Bool) → (Fin n → Bool) := fun p j => if j = i then p.1 else p.2 j
  have hcomp : (fun ω => restrictVec (insert i S) (A ω))
      = (fun ω => ψ (A ω i, restrictVec S (A ω))) := by
    ext ω j
    simp only [restrictVec, ψ, Finset.mem_insert]
    by_cases hji : j = i
    · subst hji; simp
    · simp [hji]
  rw [hcomp]
  -- Check injectivity of ψ on the image of (A ω i, restrictVec S (A ω)):
  unfold rvEnt shannonEnt
  have hψ_inj : Set.InjOn ψ (s.image (fun ω => (A ω i, restrictVec S (A ω))) : Set _) := by
    intro p1 hp1 p2 hp2 heq
    rcases Finset.mem_image.mp hp1 with ⟨ω1, _, rfl⟩
    rcases Finset.mem_image.mp hp2 with ⟨ω2, _, rfl⟩
    ext1
    · have := congr_fun heq i; simpa [ψ] using this
    · ext j
      by_cases hji : j = i
      · subst hji; simp [restrictVec, hi]
      · have := congr_fun heq j; simpa [ψ, hji] using this
  have himg : s.image (fun ω => ψ (A ω i, restrictVec S (A ω)))
      = (s.image (fun ω => (A ω i, restrictVec S (A ω)))).image ψ := by
    ext x; simp
  rw [himg, Finset.sum_image hψ_inj]
  apply Finset.sum_congr rfl
  intro p hp
  congr 1
  unfold pushProb
  congr 1
  ext ω
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hω, heq⟩
    exact ⟨hω, hψ_inj (Finset.mem_image_of_mem _ hω) hp heq⟩
  · rintro ⟨hω, rfl⟩
    exact ⟨hω, rfl⟩

/-- Monotonicity of conditional entropy: if `S ⊆ T`, then `H(A_i | A_T) ≤ H(A_i | A_S)`. -/
lemma coordCondEnt_anti {Ω : Type*} {n : ℕ} (s : Finset Ω) (w : Ω → ℝ)
    (hw : ∀ ω ∈ s, 0 ≤ w ω) (A : Ω → Fin n → Bool)
    (i : Fin n) {S T : Finset (Fin n)} (hST : S ⊆ T) :
    coordCondEnt s w A i T ≤ coordCondEnt s w A i S := by
  unfold coordCondEnt
  have hcomp : (fun ω => restrictVec S (A ω)) = (fun ω => restrictVec S (restrictVec T (A ω))) := by
    ext ω j
    simp only [restrictVec]
    by_cases hjS : j ∈ S
    · simp [hjS, hST hjS]
    · simp [hjS]
  rw [hcomp]
  exact condRvEnt_le_of_comp s w hw (fun ω => A ω i) (fun ω => restrictVec T (A ω)) (restrictVec S)

/-- Chain rule along a nodup list of coordinates `L : List (Fin n)` starting from prefix `S0`. -/
lemma subEnt_append_list {Ω : Type*} {n : ℕ} (s : Finset Ω) (w : Ω → ℝ)
    (A : Ω → Fin n → Bool) (S0 : Finset (Fin n)) :
    ∀ (ord : List (Fin n)), ord.Nodup → (∀ i ∈ ord, i ∉ S0) →
      subEnt s w A (S0 ∪ ord.toFinset) - subEnt s w A S0 =
        ∑ k : Fin ord.length,
          coordCondEnt s w A (ord[k]) (S0 ∪ (ord.take k).toFinset)
  | [], _, _ => by simp
  | a :: rest, hnd, hdisj => by
    rw [List.nodup_cons] at hnd
    have ha_not_S0 : a ∉ S0 := hdisj a List.mem_cons_self
    have hdisj_rest : ∀ i ∈ rest, i ∉ insert a S0 := by
      intro i hi
      simp only [Finset.mem_insert, not_or]
      exact ⟨fun h => hnd.1 (h ▸ hi), hdisj i (List.mem_cons_of_mem a hi)⟩
    have ih := subEnt_append_list s w A (insert a S0) rest hnd.2 hdisj_rest
    have hset : S0 ∪ (a :: rest).toFinset = insert a S0 ∪ rest.toFinset := by
      ext x; simp
    rw [hset]
    have hstep := subEnt_insert s w A ha_not_S0
    have hsum : ∑ k : Fin (a :: rest).length,
          coordCondEnt s w A ((a :: rest)[k]) (S0 ∪ ((a :: rest).take k).toFinset)
        = coordCondEnt s w A a S0 +
          ∑ k : Fin rest.length,
            coordCondEnt s w A (rest[k]) (insert a S0 ∪ (rest.take k).toFinset) := by
      simp only [List.length_cons]
      rw [Fin.sum_univ_succ]
      congr 1
      · simp
      · apply Finset.sum_congr rfl
        intro k _
        congr 1
        ext x
        simp [List.take_succ_cons]
    rw [hsum]
    linarith

/-- Total correlation of `G \ S` given `A_S`:
    `TC(A_{G \ S} | A_S) = ∑ i ∈ G \ S, H(A_i | A_S) - (H(A_G) - H(A_S))`. -/
def totalCorr {Ω : Type*} {n : ℕ} (s : Finset Ω) (w : Ω → ℝ) (A : Ω → Fin n → Bool)
    (G S : Finset (Fin n)) : ℝ :=
  (∑ i ∈ G \ S, coordCondEnt s w A i S) - (subEnt s w A G - subEnt s w A S)

end UCBound
