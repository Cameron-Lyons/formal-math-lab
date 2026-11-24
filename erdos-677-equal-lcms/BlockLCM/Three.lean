import BlockLCM.CubeRootTwo
import BlockLCM.Defect

/-!
# Length three

Call `n` the start of the block `n + 1, n + 2, n + 3`. Two blocks with different starts
have the same LCM only for the starts `2` and `3`, that is, for the blocks `3, 4, 5` and
`4, 5, 6`, whose LCMs are both `60`. Those blocks overlap, so disjoint blocks of length
three never share an LCM.

A collision forces the later product to be twice the earlier one, with the earlier
start even and the later start odd. With `x = n + 2` and `y = m + 2` this reads
`y³ - y = 2(x³ - x)`. Dividing out `g = gcd(x, y)` leaves `y₁³ - 2x₁³ ∈ {±1, ±3}`, so
`y₁ - x₁θ` is `±(θ - 1)^k` or `±(1 + θ)(θ - 1)^k` in `ℤ[θ]`, where `θ³ = 2`. Its
coefficient of `θ²` is zero. Writing `k = k₀ ± 9n` with `0 ≤ k₀ < 9` and expanding
`(θ - 1)^(±9) = 1 + 9D`, that coefficient vanishes only for `n = 0`: otherwise each
power of three dividing `n` would force a higher one.
-/

namespace Erdos677

namespace Three

theorem two_mul_choose_two_add (n : ℕ) : 2 * n.choose 2 + n = n * n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have : (n + 1).choose 2 = n + n.choose 2 := by
      rw [Nat.choose_succ_succ, Nat.choose_one_right]
    rw [this]; nlinarith

theorem choose_two_three_mul (n : ℕ) : (3 * n).choose 2 = 9 * n.choose 2 + 3 * n := by
  have h1 := two_mul_choose_two_add (3 * n)
  have h2 := two_mul_choose_two_add n
  nlinarith

theorem pow_three_dvd_choose_two {v n : ℕ} (h : 3 ^ v ∣ n) : 3 ^ v ∣ n.choose 2 := by
  have h2 := two_mul_choose_two_add n
  have hd : 3 ^ v ∣ n.choose 2 * 2 := by
    have : 3 ^ v ∣ n * n := Dvd.dvd.mul_right h n
    have h3 : 3 ^ v ∣ 2 * n.choose 2 + n := h2 ▸ this
    have := (Nat.dvd_add_left h).mp h3
    rwa [mul_comm]
  exact (Nat.Coprime.pow_left v (by norm_num : Nat.Coprime 3 2)).dvd_of_dvd_mul_right hd

/-- If `3^v` divides `n`, then `(1 + 9D)^n` agrees with its first three binomial terms
modulo `3^(v+5)`. -/
theorem second_order {R : Type*} [CommRing R] (D : R) : ∀ v n : ℕ, 3 ^ v ∣ n →
    ∃ γ : R, (1 + 9 * D) ^ n
      = 1 + 9 * (n : R) * D + 81 * ((n.choose 2 : ℕ) : R) * D ^ 2 + 3 ^ (v + 5) * γ := by
  intro v
  induction v with
  | zero =>
    intro n _
    induction n with
    | zero => exact ⟨0, by simp⟩
    | succ n ih =>
      obtain ⟨γ, h⟩ := ih (by simp)
      refine ⟨γ * (1 + 9 * D) + 3 * ((n.choose 2 : ℕ) : R) * D ^ 3, ?_⟩
      have hc : (n + 1).choose 2 = n + n.choose 2 := by
        rw [Nat.choose_succ_succ, Nat.choose_one_right]
      rw [pow_succ, h, hc]
      push_cast
      ring
  | succ v ih =>
    intro n hn
    obtain ⟨n', rfl⟩ : 3 ∣ n := Dvd.dvd.trans (dvd_pow_self 3 (Nat.succ_ne_zero v)) hn
    have hn' : 3 ^ v ∣ n' := by
      rw [pow_succ, mul_comm] at hn
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) hn
    obtain ⟨γ, h⟩ := ih n' hn'
    obtain ⟨c, hc⟩ := pow_three_dvd_choose_two hn'
    obtain ⟨q, hq⟩ := hn'
    have hrel : ((n' : ℕ) : R) ^ 2 = n' + 2 * ((n'.choose 2 : ℕ) : R) := by
      have := two_mul_choose_two_add n'
      have h' : ((2 * n'.choose 2 + n' : ℕ) : R) = ((n' * n' : ℕ) : R) := by rw [this]
      push_cast at h'
      linear_combination -h'
    rw [pow_mul', h, choose_two_three_mul]
    have hcR : ((n'.choose 2 : ℕ) : R) = 3 ^ v * (c : R) := by rw [hc]; push_cast; ring
    have hqR : ((n' : ℕ) : R) = 3 ^ v * (q : R) := by rw [hq]; push_cast; ring
    refine ⟨γ + 6 * (3 : R) ^ v * q * D * (c * D ^ 2 + 3 * γ)
      + 27 * 3 ^ v * (c * D ^ 2 + 3 * γ) ^ 2
      + (3 ^ v) ^ 2 * (q * D + 9 * c * D ^ 2 + 27 * γ) ^ 3, ?_⟩
    rw [hcR, hqR] at hrel
    push_cast
    rw [hcR, hqR]
    have e5 : (3 : R) ^ (v + 5) = 243 * 3 ^ v := by ring
    have e6 : (3 : R) ^ (v + 1 + 5) = 729 * 3 ^ v := by ring
    rw [e5, e6]
    linear_combination (243 * D ^ 2) * hrel

/-- An integer is zero if every power of three dividing it forces the next one. -/
theorem eq_zero_of_gain (n : ℤ) (h : ∀ v : ℕ, (3 : ℤ) ^ v ∣ n → (3 : ℤ) ^ (v + 1) ∣ n) :
    n = 0 := by
  have hall : ∀ v : ℕ, (3 : ℤ) ^ v ∣ n := by
    intro v
    induction v with
    | zero => simp
    | succ v ih => exact h v ih
  by_contra hne
  have hlt : n.natAbs < 3 ^ n.natAbs := Nat.lt_pow_self (by norm_num)
  have hd : (3 : ℤ) ^ n.natAbs ∣ n := hall _
  have : (3 ^ n.natAbs : ℕ) ∣ n.natAbs := by
    have := Int.natAbs_dvd_natAbs.mpr hd
    simpa [Int.natAbs_pow] using this
  exact absurd (Nat.le_of_dvd (Int.natAbs_pos.mpr hne) this) (by omega)

end Three

namespace Zcbrt2
open Three

@[simp] theorem natCast_a (n : ℕ) : ((n : Zcbrt2)).a = n := by
  induction n with
  | zero => simp
  | succ n ih => simp [ih]

@[simp] theorem natCast_b (n : ℕ) : ((n : Zcbrt2)).b = 0 := by
  induction n with
  | zero => simp
  | succ n ih => simp [ih]

@[simp] theorem natCast_c (n : ℕ) : ((n : Zcbrt2)).c = 0 := by
  induction n with
  | zero => simp
  | succ n ih => simp [ih]

/-- The `θ²` coefficient of `ν·(1 + 9nD + 81·C·D² + N·γ)`. -/
theorem c_expand (ν D γ : Zcbrt2) (n C N : ℕ) :
    (ν * (1 + 9 * (n : Zcbrt2) * D + 81 * ((C : ℕ) : Zcbrt2) * D ^ 2 + (N : Zcbrt2) * γ)).c
      = ν.c + 9 * n * (ν * D).c + 81 * C * (ν * D * D).c + N * (ν * γ).c := by
  have h9 : (9 : Zcbrt2) = ((9 : ℕ) : Zcbrt2) := by norm_num
  have h81 : (81 : Zcbrt2) = ((81 : ℕ) : Zcbrt2) := by norm_num
  rw [h9, h81, pow_two]
  simp only [mul_a, mul_b, mul_c, add_a, add_b, add_c, natCast_a, natCast_b, natCast_c,
    one_a, one_b, one_c]
  push_cast
  ring

/-- A condition on `ν` and `D` that is decidable and forces the `θ²` coefficient of
`ν·(1 + 9D)^n` to be nonzero for every `n > 0`. -/
def Good (ν D : Zcbrt2) : Prop :=
  ¬ (9 : ℤ) ∣ ν.c ∨ (¬ (81 : ℤ) ∣ ν.c ∧ (9 : ℤ) ∣ (ν * D).c) ∨
  (ν.c = 0 ∧ ¬ (3 : ℤ) ∣ (ν * D).c) ∨
  (ν.c = 0 ∧ (9 : ℤ) ∣ (ν * D).c ∧ ¬ (27 : ℤ) ∣ (ν * D).c ∧ (3 : ℤ) ∣ (ν * D * D).c)

instance (ν D : Zcbrt2) : Decidable (Good ν D) := by unfold Good; infer_instance

theorem coprime_three_pow {u : ℤ} (hu : ¬ (3 : ℤ) ∣ u) (v : ℕ) : IsCoprime ((3 : ℤ) ^ v) u :=
  IsCoprime.pow_left ((Int.prime_three.irreducible.coprime_iff_not_dvd).mpr hu)

theorem eq_zero_of_good (ν D : Zcbrt2) (hg : Good ν D) (n : ℕ)
    (h : (ν * (1 + 9 * D) ^ n).c = 0) : n = 0 ∧ ν.c = 0 := by
  rcases hg with hA | ⟨hB1, hB2⟩ | ⟨hC0, hC1⟩ | ⟨hC0, hC1, hC2, hC3⟩
  · exfalso
    obtain ⟨γ, hγ⟩ := second_order D 0 n (one_dvd _)
    have e : ((3 : Zcbrt2) ^ (0 + 5)) = ((243 : ℕ) : Zcbrt2) := by norm_num
    rw [hγ, e, c_expand] at h
    exact hA ⟨-(n * (ν * D).c + 9 * (n.choose 2) * (ν * D * D).c + 27 * (ν * γ).c),
      by push_cast at h ⊢; linarith⟩
  · exfalso
    obtain ⟨γ, hγ⟩ := second_order D 0 n (one_dvd _)
    have e : ((3 : Zcbrt2) ^ (0 + 5)) = ((243 : ℕ) : Zcbrt2) := by norm_num
    rw [hγ, e, c_expand] at h
    obtain ⟨d, hd⟩ := hB2
    exact hB1 ⟨-(n * d + (n.choose 2) * (ν * D * D).c + 3 * (ν * γ).c),
      by push_cast at h ⊢; rw [hd] at h; linarith⟩
  · refine ⟨?_, hC0⟩
    have : (n : ℤ) = 0 := by
      apply eq_zero_of_gain
      intro v hv
      have hv' : 3 ^ v ∣ n := by exact_mod_cast hv
      obtain ⟨γ, hγ⟩ := second_order D v n hv'
      obtain ⟨c', hc'⟩ := pow_three_dvd_choose_two hv'
      have e : ((3 : Zcbrt2) ^ (v + 5)) = ((3 ^ (v + 5) : ℕ) : Zcbrt2) := by push_cast; ring
      rw [hγ, e, c_expand, hC0, hc'] at h
      have hd : (3 : ℤ) ^ (v + 1) ∣ n * (ν * D).c := by
        refine ⟨-(3 * c' * (ν * D * D).c + 9 * (ν * γ).c), ?_⟩
        push_cast at h
        have e2 : (3 : ℤ) ^ (v + 5) = 243 * 3 ^ v := by ring
        have e3 : (3 : ℤ) ^ (v + 1) = 3 * 3 ^ v := by ring
        rw [e2] at h; rw [e3]
        linarith
      exact (coprime_three_pow hC1 (v + 1)).dvd_of_dvd_mul_right hd
    exact_mod_cast this
  · refine ⟨?_, hC0⟩
    have : (n : ℤ) = 0 := by
      apply eq_zero_of_gain
      intro v hv
      have hv' : 3 ^ v ∣ n := by exact_mod_cast hv
      obtain ⟨γ, hγ⟩ := second_order D v n hv'
      obtain ⟨c', hc'⟩ := pow_three_dvd_choose_two hv'
      have e : ((3 : Zcbrt2) ^ (v + 5)) = ((3 ^ (v + 5) : ℕ) : Zcbrt2) := by push_cast; ring
      rw [hγ, e, c_expand, hC0, hc'] at h
      obtain ⟨u, hu⟩ := hC1
      obtain ⟨w, hw⟩ := hC3
      have hu3 : ¬ (3 : ℤ) ∣ u := by
        rintro ⟨u', rfl⟩
        exact hC2 ⟨u', by rw [hu]; ring⟩
      have hd : (3 : ℤ) ^ (v + 1) ∣ n * u := by
        refine ⟨-(c' * w + (ν * γ).c), ?_⟩
        push_cast at h
        have e2 : (3 : ℤ) ^ (v + 5) = 243 * 3 ^ v := by ring
        have e3 : (3 : ℤ) ^ (v + 1) = 3 * 3 ^ v := by ring
        rw [e2, hu, hw] at h; rw [e3]
        linarith
      exact (coprime_three_pow hu3 (v + 1)).dvd_of_dvd_mul_right hd
    exact_mod_cast this

/-- `θ - 1`. -/
def E : Zcbrt2 := ⟨-1, 1, 0⟩

/-- `1 + θ + θ²`, the inverse of `θ - 1`. -/
def E' : Zcbrt2 := ⟨1, 1, 1⟩

/-- `(θ - 1)^9 = 1 + 9·D9`. -/
def D9 : Zcbrt2 := ⟨-18, -11, 20⟩

/-- `(θ - 1)^(-9) = 1 + 9·D9'`. -/
def D9' : Zcbrt2 := ⟨6840, 5429, 4309⟩

theorem E_pow_nine : E ^ 9 = 1 + 9 * D9 := by decide
theorem E'_pow_nine : E' ^ 9 = 1 + 9 * D9' := by decide

/-- If all nine residue classes of the exponent are good in both directions, a zero
`θ²` coefficient of `μ·(θ - 1)^k` occurs only for `0 ≤ k < 9`. -/
theorem zero_class (μ : Zcbrt2)
    (hg : ∀ k0 : Fin 9, Good (μ * E ^ k0.val) D9 ∧ Good (μ * E ^ k0.val) D9')
    (k : ℤ) (h : (μ * ((eps ^ k : Zcbrt2ˣ) : Zcbrt2)).c = 0) :
    ∃ k0 : Fin 9, k = k0.val ∧ (μ * E ^ k0.val).c = 0 := by
  have hk : k % 9 + 9 * (k / 9) = k := by omega
  have h0 : 0 ≤ k % 9 := Int.emod_nonneg k (by norm_num)
  have h9 : k % 9 < 9 := Int.emod_lt_of_pos k (by norm_num)
  obtain ⟨k0, hk0⟩ : ∃ k0 : ℕ, k % 9 = k0 := ⟨(k % 9).toNat, by omega⟩
  have hk0lt : k0 < 9 := by omega
  obtain ⟨n, hn | hn⟩ := Int.eq_nat_or_neg (k / 9)
  · have hk' : k = (k0 : ℤ) + 9 * (n : ℤ) := by rw [← hk0, ← hn]; omega
    have : ((eps ^ k : Zcbrt2ˣ) : Zcbrt2) = E ^ k0 * (1 + 9 * D9) ^ n := by
      rw [hk', zpow_add, zpow_mul, Units.val_mul, zpow_natCast, zpow_natCast, ← E_pow_nine]
      simp only [Units.val_pow_eq_pow_val]
      rfl
    rw [this, ← mul_assoc] at h
    obtain ⟨hn0, hc⟩ := eq_zero_of_good _ _ (hg ⟨k0, hk0lt⟩).1 n h
    exact ⟨⟨k0, hk0lt⟩, by simp [hk', hn0], hc⟩
  · have hk' : k = (k0 : ℤ) + 9 * (-(n : ℤ)) := by rw [← hk0, ← hn]; omega
    have : ((eps ^ k : Zcbrt2ˣ) : Zcbrt2) = E ^ k0 * (1 + 9 * D9') ^ n := by
      rw [hk', zpow_add, zpow_mul, Units.val_mul, zpow_neg, ← inv_zpow, zpow_natCast,
        zpow_natCast, ← E'_pow_nine]
      simp only [Units.val_pow_eq_pow_val, inv_pow]
      rfl
    rw [this, ← mul_assoc] at h
    obtain ⟨hn0, hc⟩ := eq_zero_of_good _ _ (hg ⟨k0, hk0lt⟩).2 n h
    exact ⟨⟨k0, hk0lt⟩, by simp [hk', hn0], hc⟩

theorem good_one :
    ∀ k0 : Fin 9, Good (1 * E ^ k0.val) D9 ∧ Good (1 * E ^ k0.val) D9' := by decide

theorem good_one_add_theta :
    ∀ k0 : Fin 9, Good (⟨1, 1, 0⟩ * E ^ k0.val) D9 ∧ Good (⟨1, 1, 0⟩ * E ^ k0.val) D9' := by
  decide

/-- The `θ²` coefficient of `(θ - 1)^k` vanishes only for `k = 0, 1`. -/
theorem eps_zpow_c (k : ℤ) (h : ((eps ^ k : Zcbrt2ˣ) : Zcbrt2).c = 0) : k = 0 ∨ k = 1 := by
  obtain ⟨k0, hk, hc⟩ := zero_class 1 good_one k (by simpa using h)
  have : ∀ k0 : Fin 9, ((1 : Zcbrt2) * E ^ k0.val).c = 0 → k0.val = 0 ∨ k0.val = 1 := by
    decide
  rcases this k0 hc with h | h <;> simp [hk, h]

/-- The `θ²` coefficient of `(1 + θ)(θ - 1)^k` vanishes only for `k = 0, 3`. -/
theorem one_add_theta_mul_eps_zpow_c (k : ℤ)
    (h : ((⟨1, 1, 0⟩ : Zcbrt2) * ((eps ^ k : Zcbrt2ˣ) : Zcbrt2)).c = 0) : k = 0 ∨ k = 3 := by
  obtain ⟨k0, hk, hc⟩ := zero_class _ good_one_add_theta k h
  have : ∀ k0 : Fin 9,
      ((⟨1, 1, 0⟩ : Zcbrt2) * E ^ k0.val).c = 0 → k0.val = 0 ∨ k0.val = 3 := by decide
  rcases this k0 hc with h | h <;> simp [hk, h]

/-- Solutions of `y³ - 2x³ = ±1`. -/
theorem thue_one (x y : ℤ) (h : y ^ 3 - 2 * x ^ 3 = 1 ∨ y ^ 3 - 2 * x ^ 3 = -1) :
    x = 0 ∨ x = 1 ∨ x = -1 := by
  have hn : norm ⟨y, -x, 0⟩ = y ^ 3 - 2 * x ^ 3 := by simp only [norm]; ring
  obtain ⟨k, hk⟩ := units ⟨y, -x, 0⟩ (by rw [hn]; exact h)
  have hc : ((eps ^ k : Zcbrt2ˣ) : Zcbrt2).c = 0 := by
    rcases hk with hk | hk
    · have := congrArg Zcbrt2.c hk; simpa using this.symm
    · have := congrArg Zcbrt2.c hk; simp only [neg_c] at this; linarith
  have hb : ((eps ^ k : Zcbrt2ˣ) : Zcbrt2).b = 0 ∨ ((eps ^ k : Zcbrt2ˣ) : Zcbrt2).b = 1 := by
    rcases eps_zpow_c k hc with rfl | rfl
    · left; simp
    · right; rw [zpow_one]; rfl
  rcases hk with hk | hk
  · have := congrArg Zcbrt2.b hk; simp only at this; rcases hb with hb | hb <;> omega
  · have := congrArg Zcbrt2.b hk; simp only [neg_b] at this; rcases hb with hb | hb <;> omega

/-- Solutions of `y³ - 2x³ = ±3`. -/
theorem thue_three (x y : ℤ) (h : y ^ 3 - 2 * x ^ 3 = 3 ∨ y ^ 3 - 2 * x ^ 3 = -3) :
    x = 1 ∨ x = -1 ∨ (x = 4 ∧ y = 5) ∨ (x = -4 ∧ y = -5) := by
  have hn : norm ⟨y, -x, 0⟩ = y ^ 3 - 2 * x ^ 3 := by simp only [norm]; ring
  obtain ⟨w, hw⟩ := dvd_of_three_dvd_norm ⟨y, -x, 0⟩
    (by rw [hn]; rcases h with h | h <;> rw [h]; norm_num)
  have hnw : norm w = 1 ∨ norm w = -1 := by
    have h3 : norm (⟨1, 1, 0⟩ : Zcbrt2) = 3 := by decide
    have := congrArg norm hw
    rw [hn, norm_mul, h3] at this
    rcases h with h | h
    · left; omega
    · right; omega
  obtain ⟨k, hk⟩ := units w hnw
  have hc : ((⟨1, 1, 0⟩ : Zcbrt2) * ((eps ^ k : Zcbrt2ˣ) : Zcbrt2)).c = 0 := by
    rcases hk with hk | hk
    · rw [← hk, ← hw]
    · have := congrArg Zcbrt2.c hw
      rw [hk, mul_neg] at this
      simp only [neg_c] at this
      linarith
  have e3 : ((⟨1, 1, 0⟩ : Zcbrt2) * ((eps ^ (3 : ℤ) : Zcbrt2ˣ) : Zcbrt2)) = ⟨-5, 4, 0⟩ := by
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast, Units.val_pow_eq_pow_val]
    decide
  rcases one_add_theta_mul_eps_zpow_c k hc with rfl | rfl
  · rcases hk with hk | hk
    · rw [hk] at hw
      have hb := congrArg Zcbrt2.b hw
      simp at hb
      right; left; omega
    · rw [hk] at hw
      have hb := congrArg Zcbrt2.b hw
      simp at hb
      left; omega
  · rcases hk with hk | hk
    · rw [hk, e3] at hw
      have hb := congrArg Zcbrt2.b hw
      have ha := congrArg Zcbrt2.a hw
      simp only at hb ha
      right; right; right; constructor <;> omega
    · rw [hk, mul_neg, e3] at hw
      have hb := congrArg Zcbrt2.b hw
      have ha := congrArg Zcbrt2.a hw
      simp only [neg_a, neg_b] at hb ha
      right; right; left; constructor <;> omega

theorem odd_dvd_six (c : ℤ) (h1 : Odd c) (h2 : c ∣ 6) : c = 1 ∨ c = -1 ∨ c = 3 ∨ c = -3 := by
  have hpos : c.natAbs ∣ 6 := by simpa using Int.natAbs_dvd_natAbs.mpr h2
  have hle : c.natAbs ≤ 6 := Nat.le_of_dvd (by norm_num) hpos
  obtain ⟨j, rfl⟩ := h1
  have h3 : -4 ≤ j := by omega
  have h4 : j ≤ 2 := by omega
  interval_cases j <;> first | (norm_num at h2; done) | norm_num

/-- The integer points of `y³ - y = 2(x³ - x)` with `x ≥ 2` even and `y` odd. -/
theorem cubic_points (x y : ℤ) (hx : 2 ≤ x) (hxe : Even x) (hyo : Odd y)
    (h : y ^ 3 - y = 2 * (x ^ 3 - x)) : x = 4 ∧ y = 5 := by
  have hg : 0 < Int.gcd x y := Int.gcd_pos_of_ne_zero_left _ (by omega)
  obtain ⟨x1, y1, hco, hx1, hy1⟩ := Int.exists_gcd_one hg
  generalize hgdef : (Int.gcd x y : ℤ) = g at hx1 hy1
  have hgpos : 0 < g := by rw [← hgdef]; exact_mod_cast hg
  have hkey : g ^ 2 * (y1 ^ 3 - 2 * x1 ^ 3) = y1 - 2 * x1 := by
    have : g * (g ^ 2 * (y1 ^ 3 - 2 * x1 ^ 3)) = g * (y1 - 2 * x1) := by
      rw [hx1, hy1] at h; linear_combination h
    exact mul_left_cancel₀ hgpos.ne' this
  have hgodd : Odd g := by rw [hy1] at hyo; exact (Int.odd_mul.mp hyo).2
  have hy1odd : Odd y1 := by rw [hy1] at hyo; exact (Int.odd_mul.mp hyo).1
  have hx1even : Even x1 := by
    rw [hx1] at hxe
    rcases Int.even_mul.mp hxe with h | h
    · exact h
    · exact absurd h (Int.not_even_iff_odd.mpr hgodd)
  have hcodd : Odd (y1 ^ 3 - 2 * x1 ^ 3) := Odd.sub_even hy1odd.pow (even_two_mul _)
  -- `y1³ - 2x1³` divides `y1 - 2x1`, hence `6x1³`, and it is coprime to `x1`.
  have hc6 : (y1 ^ 3 - 2 * x1 ^ 3) ∣ 6 := by
    have h1 : (y1 ^ 3 - 2 * x1 ^ 3) ∣ y1 - 2 * x1 := ⟨g ^ 2, by rw [← hkey]; ring⟩
    have h2 : (y1 ^ 3 - 2 * x1 ^ 3) ∣ 6 * x1 ^ 3 := by
      have : 6 * x1 ^ 3 = (y1 ^ 3 - 2 * x1 ^ 3)
          - (y1 - 2 * x1) * (y1 ^ 2 + 2 * x1 * y1 + 4 * x1 ^ 2) := by ring
      rw [this]; exact dvd_sub dvd_rfl (Dvd.dvd.mul_right h1 _)
    have hcop : IsCoprime (y1 ^ 3 - 2 * x1 ^ 3) (x1 ^ 3) := by
      have h0 : IsCoprime y1 x1 := (Int.isCoprime_iff_gcd_eq_one.mpr hco).symm
      have h1 : IsCoprime (y1 ^ 3) x1 := h0.pow_left
      have h2 : IsCoprime (y1 ^ 3 + x1 * (-2 * x1 ^ 2)) x1 := IsCoprime.add_mul_left_left h1 _
      have hc' : y1 ^ 3 - 2 * x1 ^ 3 = y1 ^ 3 + x1 * (-2 * x1 ^ 2) := by ring
      rw [hc']; exact h2.pow_right
    exact hcop.dvd_of_dvd_mul_right h2
  have hxne : x1 ≠ 0 := by rintro rfl; simp at hx1; omega
  rcases odd_dvd_six _ hcodd hc6 with hc | hc | hc | hc
  · rcases thue_one x1 y1 (Or.inl hc) with h0 | h0 | h0
    · exact absurd h0 hxne
    · rw [h0] at hx1even; exact absurd hx1even (by decide)
    · rw [h0] at hx1even; exact absurd hx1even (by decide)
  · rcases thue_one x1 y1 (Or.inr hc) with h0 | h0 | h0
    · exact absurd h0 hxne
    · rw [h0] at hx1even; exact absurd hx1even (by decide)
    · rw [h0] at hx1even; exact absurd hx1even (by decide)
  all_goals
    have h3 : y1 ^ 3 - 2 * x1 ^ 3 = 3 ∨ y1 ^ 3 - 2 * x1 ^ 3 = -3 := by
      first | exact Or.inl hc | exact Or.inr hc
    rcases thue_three x1 y1 h3 with h0 | h0 | ⟨hx4, hy5⟩ | ⟨hx4, hy5⟩
    · rw [h0] at hx1even; exact absurd hx1even (by decide)
    · rw [h0] at hx1even; exact absurd hx1even (by decide)
    · rw [hx4, hy5] at hkey
      have hg1 : g = 1 := by nlinarith
      rw [hx1, hy1, hx4, hy5, hg1]; norm_num
    · rw [hx4] at hx1; nlinarith

end Zcbrt2

open Finset

/-- Product of the three entries in a block. -/
def threeBlockProduct (n : ℕ) := (n+1)*(n+2)*(n+3)

theorem lcmInterval_three_mul_defect (n : ℕ) :
    lcmInterval n 3 * Nat.gcd 2 (n+3) = threeBlockProduct n := by
  have h := lcmInterval_mul_gcd_product n 3
  simp only [prod_range_succ, prod_range_zero, Nat.one_mul, Nat.add_zero] at h
  change _ * (Nat.gcd 1 _ * Nat.gcd 1 _ * Nat.gcd 2 _) = _ at h
  simpa only [threeBlockProduct, Nat.gcd_one_left, Nat.one_mul] using h

/-- Two distinct length-three blocks have the same LCM precisely for the starts 2 and 3. -/
theorem three_collision_iff {n m : ℕ} (hlt : n < m) :
    lcmInterval m 3 = lcmInterval n 3 ↔ (n,m) = (2,3) := by
  constructor
  · intro heq
    have hn := lcmInterval_three_mul_defect n
    have hm := lcmInterval_three_mul_defect m
    rw [heq] at hm
    have hp : threeBlockProduct n < threeBlockProduct m := by
      unfold threeBlockProduct
      repeat first | apply Nat.mul_lt_mul_of_lt_of_lt | omega
    have hd : ∀ j : ℕ, Nat.gcd 2 (j+3) = 1 ∨ Nat.gcd 2 (j+3) = 2 := fun j =>
      (Nat.dvd_prime Nat.prime_two).mp (Nat.gcd_dvd_left 2 (j+3))
    rcases hd n with hdn | hdn <;> rcases hd m with hdm | hdm <;>
      rw [hdn] at hn <;> rw [hdm] at hm
    · omega
    · -- The earlier start is even, the later start is odd, and the product doubles.
      obtain ⟨j, hj⟩ : Odd (n+3) := Nat.coprime_two_left.mp hdn
      obtain ⟨i, hi⟩ : 2 ∣ m+3 := hdm ▸ Nat.gcd_dvd_right 2 (m+3)
      have hP : threeBlockProduct m = 2 * threeBlockProduct n := by omega
      have hZ : ((m:ℤ)+2)^3 - ((m:ℤ)+2) = 2 * (((n:ℤ)+2)^3 - ((n:ℤ)+2)) := by
        unfold threeBlockProduct at hP
        have := congrArg (Nat.cast : ℕ → ℤ) hP
        push_cast at this
        linear_combination this
      obtain ⟨hx, hy⟩ := Zcbrt2.cubic_points ((n:ℤ)+2) ((m:ℤ)+2) (by omega)
        ⟨(j:ℤ), by omega⟩ ⟨(i:ℤ)-1, by omega⟩ hZ
      obtain rfl : n = 2 := by omega
      obtain rfl : m = 3 := by omega
      rfl
    · omega
    · omega
  · intro h; cases h; decide

/-- Disjoint blocks of length three have different LCMs. -/
theorem erdos_677_three (m n : ℕ) (hm : m ≥ n + 3) :
    lcmInterval m 3 ≠ lcmInterval n 3 := by
  intro heq
  have h := (three_collision_iff (show n < m by omega)).mp heq
  simp only [Prod.mk.injEq] at h
  omega

end Erdos677
