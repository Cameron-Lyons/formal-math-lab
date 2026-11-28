module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

@[expose] public section

/-!
# The ring ℤ[∛2]

Write `θ` for the cube root of two. An element `a + bθ + cθ²` is stored as the integer
triple `(a, b, c)`. Every element of norm `±1` is `±(θ - 1)^k` for an integer `k`, and
every element whose norm is divisible by three is a multiple of `1 + θ`.

The unit statement needs no general unit theorem. For `x = a + bθ + cθ²` with real
value `u`,

`2·N(x) = u·((a - bθ)² + (bθ - cθ²)² + (cθ² - a)²)`.

Multiplying a norm-one element by a power of `θ - 1` moves its real value into
`[1, 1 + θ + θ²)`. There the identity bounds the three squares by two, which leaves
`a, b, c ∈ {0, 1}`, and among those eight triples only `1` qualifies.
-/

namespace Erdos677

/-- The element `a + bθ + cθ²` of `ℤ[θ]`, where `θ³ = 2`. -/
@[ext] structure Zcbrt2 where
  a : ℤ
  b : ℤ
  c : ℤ
deriving DecidableEq

namespace Zcbrt2

instance : Zero Zcbrt2 := ⟨⟨0, 0, 0⟩⟩
instance : One Zcbrt2 := ⟨⟨1, 0, 0⟩⟩
instance : Add Zcbrt2 := ⟨fun x y => ⟨x.a + y.a, x.b + y.b, x.c + y.c⟩⟩
instance : Neg Zcbrt2 := ⟨fun x => ⟨-x.a, -x.b, -x.c⟩⟩
instance : Mul Zcbrt2 := ⟨fun x y =>
  ⟨x.a * y.a + 2 * x.b * y.c + 2 * x.c * y.b, x.a * y.b + x.b * y.a + 2 * x.c * y.c,
    x.a * y.c + x.b * y.b + x.c * y.a⟩⟩

@[simp] theorem zero_a : (0 : Zcbrt2).a = 0 := rfl
@[simp] theorem zero_b : (0 : Zcbrt2).b = 0 := rfl
@[simp] theorem zero_c : (0 : Zcbrt2).c = 0 := rfl
@[simp] theorem one_a : (1 : Zcbrt2).a = 1 := rfl
@[simp] theorem one_b : (1 : Zcbrt2).b = 0 := rfl
@[simp] theorem one_c : (1 : Zcbrt2).c = 0 := rfl
@[simp] theorem add_a (x y : Zcbrt2) : (x + y).a = x.a + y.a := rfl
@[simp] theorem add_b (x y : Zcbrt2) : (x + y).b = x.b + y.b := rfl
@[simp] theorem add_c (x y : Zcbrt2) : (x + y).c = x.c + y.c := rfl
@[simp] theorem neg_a (x : Zcbrt2) : (-x).a = -x.a := rfl
@[simp] theorem neg_b (x : Zcbrt2) : (-x).b = -x.b := rfl
@[simp] theorem neg_c (x : Zcbrt2) : (-x).c = -x.c := rfl
@[simp] theorem mul_a (x y : Zcbrt2) :
    (x * y).a = x.a * y.a + 2 * x.b * y.c + 2 * x.c * y.b := rfl
@[simp] theorem mul_b (x y : Zcbrt2) :
    (x * y).b = x.a * y.b + x.b * y.a + 2 * x.c * y.c := rfl
@[simp] theorem mul_c (x y : Zcbrt2) :
    (x * y).c = x.a * y.c + x.b * y.b + x.c * y.a := rfl

instance : CommRing Zcbrt2 where
  add_assoc x y z := by ext <;> simp <;> ring
  zero_add x := by ext <;> simp
  add_zero x := by ext <;> simp
  add_comm x y := by ext <;> simp <;> ring
  neg_add_cancel x := by ext <;> simp
  mul_assoc x y z := by ext <;> simp <;> ring
  one_mul x := by ext <;> simp
  mul_one x := by ext <;> simp
  left_distrib x y z := by ext <;> simp <;> ring
  right_distrib x y z := by ext <;> simp <;> ring
  mul_comm x y := by ext <;> simp <;> ring
  zero_mul x := by ext <;> simp
  mul_zero x := by ext <;> simp
  nsmul := nsmulRec
  zsmul := zsmulRec

/-- The norm `a³ + 2b³ + 4c³ - 6abc`. -/
def norm (x : Zcbrt2) : ℤ := x.a ^ 3 + 2 * x.b ^ 3 + 4 * x.c ^ 3 - 6 * x.a * x.b * x.c

theorem norm_mul (x y : Zcbrt2) : norm (x * y) = norm x * norm y := by
  simp only [norm, mul_a, mul_b, mul_c]; ring

theorem norm_neg (x : Zcbrt2) : norm (-x) = -norm x := by
  simp only [norm, neg_a, neg_b, neg_c]; ring

/-- The norm as a multiplicative map. -/
def normHom : Zcbrt2 →* ℤ where
  toFun := norm
  map_one' := by simp [norm]
  map_mul' := norm_mul

/-- The unit `θ - 1`, with inverse `1 + θ + θ²`. -/
def eps : Zcbrt2ˣ := ⟨⟨-1, 1, 0⟩, ⟨1, 1, 1⟩, by decide, by decide⟩

theorem norm_eps_zpow (k : ℤ) : norm ((eps ^ k : Zcbrt2ˣ) : Zcbrt2) = 1 := by
  have h : Units.map normHom eps = 1 := by ext; decide
  have h2 : Units.map normHom (eps ^ k) = 1 := by rw [map_zpow, h, one_zpow]
  exact congrArg Units.val h2

/-- A norm-one triple whose real value lies in `[1, 1 + t + t²)` is `(1, 0, 0)`.
Here `t` is any real number with `t³ = 2`. -/
theorem eq_one_of_fundamental (t : ℝ) (ht : t ^ 3 = 2) (a b c : ℤ)
    (hN : a ^ 3 + 2 * b ^ 3 + 4 * c ^ 3 - 6 * a * b * c = 1)
    (h1 : (1 : ℝ) ≤ a + b * t + c * t ^ 2)
    (h2 : (a : ℝ) + b * t + c * t ^ 2 < 1 + t + t ^ 2) :
    a = 1 ∧ b = 0 ∧ c = 0 := by
  have htpos : 0 < t := by
    by_contra h
    push Not at h
    have : t ^ 3 ≤ 0 := by
      have : t ^ 3 = t * t ^ 2 := by ring
      rw [this]; exact mul_nonpos_of_nonpos_of_nonneg h (sq_nonneg t)
    linarith
  have hlo : (5 / 4 : ℝ) < t := by
    by_contra h
    push Not at h
    have : t ^ 3 ≤ (5 / 4 : ℝ) ^ 3 := pow_le_pow_left₀ htpos.le h 3
    norm_num at this; linarith
  have hhi : t < (63 / 50 : ℝ) := by
    by_contra h
    push Not at h
    have : (63 / 50 : ℝ) ^ 3 ≤ t ^ 3 := pow_le_pow_left₀ (by norm_num) h 3
    norm_num at this; linarith
  set u : ℝ := a + b * t + c * t ^ 2 with hu
  have hNr : ((a : ℝ) ^ 3 + 2 * b ^ 3 + 4 * c ^ 3 - 6 * a * b * c) = 1 := by exact_mod_cast hN
  -- Twice the norm is the real value times a sum of three squares.
  have hfac : 2 * ((a : ℝ) ^ 3 + 2 * b ^ 3 + 4 * c ^ 3 - 6 * a * b * c) =
      u * ((a - b * t) ^ 2 + (b * t - c * t ^ 2) ^ 2 + (c * t ^ 2 - a) ^ 2) := by
    have h6 : t ^ 6 = 4 := by
      have : t ^ 6 = (t ^ 3) ^ 2 := by ring
      rw [this, ht]; norm_num
    simp only [hu]
    ring_nf
    rw [h6, ht]
    ring
  set S : ℝ := (a - b * t) ^ 2 + (b * t - c * t ^ 2) ^ 2 + (c * t ^ 2 - a) ^ 2 with hS
  have hS2 : u * S = 2 := by rw [← hfac, hNr]; norm_num
  have hSnn : 0 ≤ S := by positivity
  have hSle : S ≤ 2 := by nlinarith
  -- Any two of the three terms differ by at most two.
  have hA : ((a - b * t) - (c * t ^ 2 - a)) ^ 2 ≤ 4 := by
    nlinarith [sq_nonneg ((a - b * t) + (c * t ^ 2 - a)), sq_nonneg (b * t - c * t ^ 2)]
  have hB : ((b * t - c * t ^ 2) - (a - b * t)) ^ 2 ≤ 4 := by
    nlinarith [sq_nonneg ((a - b * t) + (b * t - c * t ^ 2)), sq_nonneg (c * t ^ 2 - a)]
  have hC : ((c * t ^ 2 - a) - (b * t - c * t ^ 2)) ^ 2 ≤ 4 := by
    nlinarith [sq_nonneg ((c * t ^ 2 - a) + (b * t - c * t ^ 2)), sq_nonneg (a - b * t)]
  have hA' : -2 ≤ (a - b * t) - (c * t ^ 2 - a) ∧ (a - b * t) - (c * t ^ 2 - a) ≤ 2 :=
    abs_le_of_sq_le_sq' (by norm_num; linarith) (by norm_num)
  have hB' : -2 ≤ (b * t - c * t ^ 2) - (a - b * t) ∧ (b * t - c * t ^ 2) - (a - b * t) ≤ 2 :=
    abs_le_of_sq_le_sq' (by norm_num; linarith) (by norm_num)
  have hC' : -2 ≤ (c * t ^ 2 - a) - (b * t - c * t ^ 2) ∧
      (c * t ^ 2 - a) - (b * t - c * t ^ 2) ≤ 2 :=
    abs_le_of_sq_le_sq' (by norm_num; linarith) (by norm_num)
  have ht2lo : (25 / 16 : ℝ) < t ^ 2 := by nlinarith
  have ht2hi : t ^ 2 < (3969 / 2500 : ℝ) := by nlinarith
  have hu2 : u < 1 + 63 / 50 + 3969 / 2500 := by linarith
  -- Each of `3a`, `3bt`, `3ct²` is the real value plus one of those differences.
  have ea : 3 * (a : ℝ) = u + ((a - b * t) - (c * t ^ 2 - a)) := by simp only [hu]; ring
  have eb : 3 * ((b : ℝ) * t) = u + ((b * t - c * t ^ 2) - (a - b * t)) := by
    simp only [hu]; ring
  have ec : 3 * ((c : ℝ) * t ^ 2) = u + ((c * t ^ 2 - a) - (b * t - c * t ^ 2)) := by
    simp only [hu]; ring
  have ha0 : 0 ≤ a := by
    by_contra h
    have h' : a ≤ -1 := by omega
    have : (a : ℝ) ≤ -1 := by exact_mod_cast h'
    linarith [hA'.1]
  have ha1 : a ≤ 1 := by
    by_contra h
    have h' : 2 ≤ a := by omega
    have : (2 : ℝ) ≤ a := by exact_mod_cast h'
    linarith [hA'.2]
  have hb0 : 0 ≤ b := by
    by_contra h
    have h' : b ≤ -1 := by omega
    have h'' : (b : ℝ) ≤ -1 := by exact_mod_cast h'
    have : (b : ℝ) * t ≤ -1 * t := mul_le_mul_of_nonneg_right h'' htpos.le
    linarith [hB'.1]
  have hb1 : b ≤ 1 := by
    by_contra h
    have h' : 2 ≤ b := by omega
    have h'' : (2 : ℝ) ≤ b := by exact_mod_cast h'
    have : 2 * t ≤ (b : ℝ) * t := mul_le_mul_of_nonneg_right h'' htpos.le
    linarith [hB'.2]
  have hc0 : 0 ≤ c := by
    by_contra h
    have h' : c ≤ -1 := by omega
    have h'' : (c : ℝ) ≤ -1 := by exact_mod_cast h'
    have : (c : ℝ) * t ^ 2 ≤ -1 * t ^ 2 := mul_le_mul_of_nonneg_right h'' (sq_nonneg t)
    linarith [hC'.1]
  have hc1 : c ≤ 1 := by
    by_contra h
    have h' : 2 ≤ c := by omega
    have h'' : (2 : ℝ) ≤ c := by exact_mod_cast h'
    have : 2 * t ^ 2 ≤ (c : ℝ) * t ^ 2 := mul_le_mul_of_nonneg_right h'' (sq_nonneg t)
    linarith [hC'.2]
  clear_value u S
  interval_cases a <;> interval_cases b <;> interval_cases c <;> simp_all

/-- The real cube root of two. -/
noncomputable def t : ℝ := (2 : ℝ) ^ ((3 : ℝ)⁻¹)

theorem t_cube : t ^ 3 = 2 := by
  unfold t
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  norm_num

/-- The real embedding sending `θ` to the real cube root of two. -/
noncomputable def phi : Zcbrt2 →+* ℝ where
  toFun x := x.a + x.b * t + x.c * t ^ 2
  map_one' := by simp
  map_zero' := by simp
  map_add' x y := by simp; ring
  map_mul' x y := by
    simp only [mul_a, mul_b, mul_c]
    push_cast
    linear_combination (-((x.b : ℝ) * y.c + x.c * y.b) - x.c * y.c * t) * t_cube

theorem phi_apply (x : Zcbrt2) : phi x = x.a + x.b * t + x.c * t ^ 2 := rfl

theorem two_norm_eq (x : Zcbrt2) : 2 * (norm x : ℝ) = phi x *
    ((x.a - x.b * t) ^ 2 + (x.b * t - x.c * t ^ 2) ^ 2 + (x.c * t ^ 2 - x.a) ^ 2) := by
  have h6 : t ^ 6 = 4 := by
    have : t ^ 6 = (t ^ 3) ^ 2 := by ring
    rw [this, t_cube]; norm_num
  simp only [norm, phi_apply]
  push_cast
  linear_combination (-2 * (x.b : ℝ) ^ 3 + 6 * x.a * x.b * x.c) * t_cube -
    2 * (x.c : ℝ) ^ 3 * h6

/-- Every element of norm one is a power of `θ - 1`. -/
theorem eq_eps_zpow_of_norm_one (x : Zcbrt2) (hx : norm x = 1) :
    ∃ k : ℤ, x = ((eps ^ k : Zcbrt2ˣ) : Zcbrt2) := by
  have hpos : 0 < phi x := by
    have h := two_norm_eq x
    rw [hx] at h
    by_contra hneg
    push Not at hneg
    have : phi x *
        ((x.a - x.b * t) ^ 2 + (x.b * t - x.c * t ^ 2) ^ 2 + (x.c * t ^ 2 - x.a) ^ 2) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hneg (by positivity)
    rw [← h] at this
    norm_num at this
  have htpos : 0 < t := by unfold t; positivity
  have hE' : phi ((eps⁻¹ : Zcbrt2ˣ) : Zcbrt2) = 1 + t + t ^ 2 := by
    change ((1 : ℤ) : ℝ) + ((1 : ℤ) : ℝ) * t + ((1 : ℤ) : ℝ) * t ^ 2 = _
    push_cast; ring
  have hE : (1 : ℝ) < phi ((eps⁻¹ : Zcbrt2ˣ) : Zcbrt2) := by
    rw [hE']; nlinarith [htpos]
  obtain ⟨n, hn1, hn2⟩ := exists_mem_Ico_zpow hpos hE
  -- `y = x * eps^n` has real value in `[1, 1 + t + t²)`.
  set y : Zcbrt2 := x * ((eps ^ n : Zcbrt2ˣ) : Zcbrt2) with hy
  have hphiE : phi ((eps ^ n : Zcbrt2ˣ) : Zcbrt2) =
      (phi ((eps⁻¹ : Zcbrt2ˣ) : Zcbrt2)) ^ (-n) := by
    have h1 : ((Units.map (phi : Zcbrt2 →* ℝ) (eps ^ n) : ℝˣ) : ℝ) =
        phi ((eps ^ n : Zcbrt2ˣ) : Zcbrt2) := rfl
    have h2 : ((Units.map (phi : Zcbrt2 →* ℝ) (eps⁻¹) : ℝˣ) : ℝ) =
        phi ((eps⁻¹ : Zcbrt2ˣ) : Zcbrt2) := rfl
    rw [← h1, ← h2, ← Units.val_zpow_eq_zpow_val, ← map_zpow, inv_zpow', neg_neg]
  have hEpos : 0 < phi ((eps⁻¹ : Zcbrt2ˣ) : Zcbrt2) := by linarith
  have hy1 : 1 ≤ phi y := by
    rw [hy, map_mul, hphiE, zpow_neg]
    rw [le_mul_inv_iff₀ (zpow_pos hEpos n)]
    simpa using hn1
  have hy2 : phi y < phi ((eps⁻¹ : Zcbrt2ˣ) : Zcbrt2) := by
    rw [hy, map_mul, hphiE, zpow_neg]
    rw [mul_inv_lt_iff₀ (zpow_pos hEpos n)]
    rw [zpow_add_one₀ hEpos.ne'] at hn2
    linarith
  have hNy : norm y = 1 := by rw [hy, norm_mul, hx, norm_eps_zpow, mul_one]
  obtain ⟨ha, hb, hc⟩ := eq_one_of_fundamental t t_cube y.a y.b y.c hNy
    (by simpa [phi_apply] using hy1) (by rw [hE'] at hy2; simpa [phi_apply] using hy2)
  have hy_one : y = 1 := by ext <;> simp [ha, hb, hc]
  refine ⟨-n, ?_⟩
  have : x = y * ((eps ^ (-n) : Zcbrt2ˣ) : Zcbrt2) := by
    rw [hy, mul_assoc, ← Units.val_mul, ← zpow_add]; simp
  rw [this, hy_one, one_mul]

/-- An element of norm `±1` is `±(θ - 1)^k`. -/
theorem units (x : Zcbrt2) (hx : norm x = 1 ∨ norm x = -1) :
    ∃ k : ℤ, x = ((eps ^ k : Zcbrt2ˣ) : Zcbrt2) ∨ x = -((eps ^ k : Zcbrt2ˣ) : Zcbrt2) := by
  rcases hx with h | h
  · obtain ⟨k, hk⟩ := eq_eps_zpow_of_norm_one x h
    exact ⟨k, Or.inl hk⟩
  · obtain ⟨k, hk⟩ := eq_eps_zpow_of_norm_one (-x) (by rw [norm_neg, h]; norm_num)
    exact ⟨k, Or.inr (by rw [← hk, neg_neg])⟩

/-- Since `N(x) ≡ a - b + c (mod 3)`, an element whose norm is divisible by three is a
multiple of `1 + θ`. -/
theorem dvd_of_three_dvd_norm (x : Zcbrt2) (h : (3 : ℤ) ∣ norm x) :
    ∃ w : Zcbrt2, x = ⟨1, 1, 0⟩ * w := by
  have h3 : (3 : ℤ) ∣ x.a - x.b + x.c := by
    have key : ∀ n : ℤ, (3 : ℤ) ∣ n ^ 3 - n := by
      intro n
      have : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
      rcases this with h | h | h <;>
        · apply Int.dvd_of_emod_eq_zero
          simp [pow_succ, Int.sub_emod, Int.mul_emod, h]
    have e : x.a - x.b + x.c =
        norm x - (x.a ^ 3 - x.a) - 2 * (x.b ^ 3 - x.b) - 4 * (x.c ^ 3 - x.c)
          + 3 * (2 * x.a * x.b * x.c - x.b - x.c) := by simp only [norm]; ring
    rw [e]
    exact dvd_add (dvd_sub (dvd_sub (dvd_sub h (key _)) (Dvd.dvd.mul_left (key _) _))
      (Dvd.dvd.mul_left (key _) _)) (dvd_mul_right _ _)
  obtain ⟨s, hs⟩ := h3
  -- The quotient is `(1 - θ + θ²)·x / 3`.
  refine ⟨⟨s + x.b - x.c, x.c - s, s⟩, ?_⟩
  ext <;> simp
  linarith

end Zcbrt2

end Erdos677
