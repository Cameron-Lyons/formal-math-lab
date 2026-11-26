module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Data.Int.Basic
public import Mathlib.Data.Nat.Sqrt
public import Mathlib.Data.Nat.Log
public import UCBound.Basic

@[expose] public section

/-!
# Certified Fixed-Point Interval Arithmetic Engine (Pure Kernel-Verified, Zero `native_decide`)

Uses fixed-point integers scaled by `SCALE = 2^50 = 1125899906842624` (~15 decimal digits of precision).
All integer arithmetic (`+`, `-`, `*`, `ediv`, `Nat.sqrt`, `Nat.log2`) executes natively in Lean 4's
GMP-backed kernel without `native_decide`.

Provides sound interval operations for:
- `add`, `neg`, `sub`, `mul`, `sq`, `invPos`, `divPos`, `maxZero`, `max`, `min`, `abs`
- `sqrt` (1-ULP rigorous via `Nat.sqrt`)
- `log` (50-bit rigorous via bit-shift range reduction to `[2/3, 4/3]` and odd Taylor series of
  `log((1+u)/(1-u))` with exact derivative remainder bound!)
- Monotonicity-exact `h` (binary entropy), `Ixx`, `phi`, `F_fun`, `J_fun`, `R_fun`, `v_fun`, `b_fun`!
-/

namespace UCBound.Iv

open Real

def SCALE_BITS : ℕ := 50
def SCALE : ℕ := 2 ^ 50

lemma SCALE_pos_nat : 0 < SCALE := by decide
lemma SCALE_pos : (0 : ℝ) < (SCALE : ℝ) := by exact_mod_cast SCALE_pos_nat
lemma SCALE_ne_zero : (SCALE : ℝ) ≠ 0 := ne_of_gt SCALE_pos

/-- Floor division `⌊a / b⌋` for `a : ℤ`, `b : ℕ` (`b > 0`). -/
def fdiv (a : ℤ) (b : ℕ) : ℤ := a / (b : ℤ)

/-- Ceiling division `⌈a / b⌉` for `a : ℤ`, `b : ℕ` (`b > 0`). -/
def cdiv (a : ℤ) (b : ℕ) : ℤ := -((-a) / (b : ℤ))

lemma fdiv_le (a : ℤ) {b : ℕ} (hb : 0 < b) :
    (fdiv a b : ℝ) ≤ (a : ℝ) / (b : ℝ) := by
  have hbR : (0 : ℝ) < (b : ℝ) := Nat.cast_pos.mpr hb
  rw [le_div_iff₀ hbR]
  unfold fdiv
  have h : (a / (b : ℤ)) * (b : ℤ) ≤ a := by
    have hbZ : (0 : ℤ) < (b : ℤ) := Nat.cast_pos.mpr hb
    have hrem : 0 ≤ a % (b : ℤ) := Int.emod_nonneg a (ne_of_gt hbZ)
    have hid := Int.mul_ediv_add_emod a (b : ℤ)
    linarith
  exact_mod_cast h

lemma le_cdiv (a : ℤ) {b : ℕ} (hb : 0 < b) :
    (a : ℝ) / (b : ℝ) ≤ (cdiv a b : ℝ) := by
  have hbR : (0 : ℝ) < (b : ℝ) := Nat.cast_pos.mpr hb
  rw [div_le_iff₀ hbR]
  unfold cdiv
  have h : a ≤ (-((-a) / (b : ℤ))) * (b : ℤ) := by
    have hbZ : (0 : ℤ) < (b : ℤ) := Nat.cast_pos.mpr hb
    have hrem : 0 ≤ (-a) % (b : ℤ) := Int.emod_nonneg (-a) (ne_of_gt hbZ)
    have hid := Int.mul_ediv_add_emod (-a) (b : ℤ)
    linarith
  exact_mod_cast h

lemma min_div_pos {a b c : ℝ} (hc : 0 ≤ c) : min a b / c = min (a / c) (b / c) := by
  rcases le_total a b with hab | hba
  · rw [min_eq_left hab, min_eq_left (div_le_div_of_nonneg_right hab hc)]
  · rw [min_eq_right hba, min_eq_right (div_le_div_of_nonneg_right hba hc)]

lemma max_div_pos {a b c : ℝ} (hc : 0 ≤ c) : max a b / c = max (a / c) (b / c) := by
  rcases le_total a b with hab | hba
  · rw [max_eq_right hab, max_eq_right (div_le_div_of_nonneg_right hab hc)]
  · rw [max_eq_left hba, max_eq_left (div_le_div_of_nonneg_right hba hc)]

/-- Fixed-point interval `[lo / SCALE, hi / SCALE]`. -/
structure Interval where
  lo : ℤ
  hi : ℤ
  deriving Repr, DecidableEq

/-- Real membership `x ∈ [I.lo / SCALE, I.hi / SCALE]`. -/
def mem (I : Interval) (x : ℝ) : Prop :=
  (I.lo : ℝ) / (SCALE : ℝ) ≤ x ∧ x ≤ (I.hi : ℝ) / (SCALE : ℝ)

/-- Convert an integer to a point interval. -/
def ofInt (n : ℤ) : Interval := ⟨n * (SCALE : ℤ), n * (SCALE : ℤ)⟩

lemma mem_ofInt (n : ℤ) : mem (ofInt n) (n : ℝ) := by
  unfold mem ofInt
  have h : ((n * (SCALE : ℤ) : ℤ) : ℝ) / (SCALE : ℝ) = (n : ℝ) := by
    push_cast; exact mul_div_cancel_right₀ (n : ℝ) SCALE_ne_zero
  rw [h]; exact ⟨le_rfl, le_rfl⟩

/-- Convert a rational `p / q` (`q > 0`) to a tight interval. -/
def ofRat (p : ℤ) (q : ℕ) : Interval :=
  ⟨fdiv (p * (SCALE : ℤ)) q, cdiv (p * (SCALE : ℤ)) q⟩

lemma mem_ofRat (p : ℤ) {q : ℕ} (hq : 0 < q) : mem (ofRat p q) ((p : ℝ) / (q : ℝ)) := by
  unfold mem ofRat
  have hqR : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr hq
  have hS : (0 : ℝ) < (SCALE : ℝ) := SCALE_pos
  constructor
  · have h1 := fdiv_le (p * (SCALE : ℤ)) hq
    rw [div_le_iff₀ hS]
    have h2 : ((p * (SCALE : ℤ) : ℤ) : ℝ) / (q : ℝ) = (p : ℝ) / (q : ℝ) * (SCALE : ℝ) := by
      push_cast; ring
    linarith
  · have h1 := le_cdiv (p * (SCALE : ℤ)) hq
    rw [le_div_iff₀ hS]
    have h2 : ((p * (SCALE : ℤ) : ℤ) : ℝ) / (q : ℝ) = (p : ℝ) / (q : ℝ) * (SCALE : ℝ) := by
      push_cast; ring
    linarith

def add (I J : Interval) : Interval := ⟨I.lo + J.lo, I.hi + J.hi⟩
def neg (I : Interval) : Interval := ⟨-I.hi, -I.lo⟩
def sub (I J : Interval) : Interval := ⟨I.lo - J.hi, I.hi - J.lo⟩

lemma mem_add {I J : Interval} {x y : ℝ} (hx : mem I x) (hy : mem J y) :
    mem (add I J) (x + y) := by
  unfold mem add at *; push_cast
  constructor <;> rw [add_div] <;> linarith

lemma mem_neg {I : Interval} {x : ℝ} (hx : mem I x) : mem (neg I) (-x) := by
  unfold mem neg at *; push_cast
  constructor <;> rw [neg_div] <;> linarith

lemma mem_sub {I J : Interval} {x y : ℝ} (hx : mem I x) (hy : mem J y) :
    mem (sub I J) (x - y) := by
  unfold mem sub at *; push_cast
  constructor <;> rw [sub_div] <;> linarith

def mul (I J : Interval) : Interval :=
  let p1 := I.lo * J.lo
  let p2 := I.lo * J.hi
  let p3 := I.hi * J.lo
  let p4 := I.hi * J.hi
  ⟨fdiv (min (min p1 p2) (min p3 p4)) SCALE,
   cdiv (max (max p1 p2) (max p3 p4)) SCALE⟩

/-- Four-corner bilinear bound on `[a, b] × [c, d]`. -/
lemma mul_mem_corners {a b c d x y : ℝ} (hx1 : a ≤ x) (hx2 : x ≤ b) (hy1 : c ≤ y) (hy2 : y ≤ d) :
    min (min (a * c) (a * d)) (min (b * c) (b * d)) ≤ x * y ∧
    x * y ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) := by
  have h1 : min (min (a * c) (a * d)) (min (b * c) (b * d)) ≤ a * y := by
    have hc : min (min (a * c) (a * d)) (min (b * c) (b * d)) ≤ a * c :=
      le_trans (min_le_left _ _) (min_le_left _ _)
    have hd : min (min (a * c) (a * d)) (min (b * c) (b * d)) ≤ a * d :=
      le_trans (min_le_left _ _) (min_le_right _ _)
    rcases le_total 0 a with ha | ha <;> nlinarith
  have h2 : min (min (a * c) (a * d)) (min (b * c) (b * d)) ≤ b * y := by
    have hc : min (min (a * c) (a * d)) (min (b * c) (b * d)) ≤ b * c :=
      le_trans (min_le_right _ _) (min_le_left _ _)
    have hd : min (min (a * c) (a * d)) (min (b * c) (b * d)) ≤ b * d :=
      le_trans (min_le_right _ _) (min_le_right _ _)
    rcases le_total 0 b with hb | hb <;> nlinarith
  have h3 : a * y ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) := by
    have hc : a * c ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) :=
      le_trans (le_max_left _ _) (le_max_left _ _)
    have hd : a * d ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) :=
      le_trans (le_max_right _ _) (le_max_left _ _)
    rcases le_total 0 a with ha | ha <;> nlinarith
  have h4 : b * y ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) := by
    have hc : b * c ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) :=
      le_trans (le_max_left _ _) (le_max_right _ _)
    have hd : b * d ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) :=
      le_trans (le_max_right _ _) (le_max_right _ _)
    rcases le_total 0 b with hb | hb <;> nlinarith
  constructor
  · rcases le_total 0 y with hy | hy <;> nlinarith
  · rcases le_total 0 y with hy | hy <;> nlinarith

lemma mem_mul {I J : Interval} {x y : ℝ} (hx : mem I x) (hy : mem J y) :
    mem (mul I J) (x * y) := by
  unfold mem mul at *
  have hS : (0 : ℝ) < (SCALE : ℝ) := SCALE_pos
  have hc := mul_mem_corners hx.1 hx.2 hy.1 hy.2
  set m := min (min (I.lo * J.lo) (I.lo * J.hi)) (min (I.hi * J.lo) (I.hi * J.hi))
  set M := max (max (I.lo * J.lo) (I.lo * J.hi)) (max (I.hi * J.lo) (I.hi * J.hi))
  have hm_eq : (m : ℝ) / ((SCALE : ℝ) * (SCALE : ℝ))
      = min (min ((I.lo : ℝ) / SCALE * ((J.lo : ℝ) / SCALE)) ((I.lo : ℝ) / SCALE * ((J.hi : ℝ) / SCALE)))
            (min ((I.hi : ℝ) / SCALE * ((J.lo : ℝ) / SCALE)) ((I.hi : ℝ) / SCALE * ((J.hi : ℝ) / SCALE))) := by
    simp only [m, Int.cast_min, Int.cast_mul, min_div_pos (mul_nonneg (le_of_lt hS) (le_of_lt hS))]
    congr 1 <;> congr 1 <;> ring
  have hM_eq : (M : ℝ) / ((SCALE : ℝ) * (SCALE : ℝ))
      = max (max ((I.lo : ℝ) / SCALE * ((J.lo : ℝ) / SCALE)) ((I.lo : ℝ) / SCALE * ((J.hi : ℝ) / SCALE)))
            (max ((I.hi : ℝ) / SCALE * ((J.lo : ℝ) / SCALE)) ((I.hi : ℝ) / SCALE * ((J.hi : ℝ) / SCALE))) := by
    simp only [M, Int.cast_max, Int.cast_mul, max_div_pos (mul_nonneg (le_of_lt hS) (le_of_lt hS))]
    congr 1 <;> congr 1 <;> ring
  constructor
  · have h1 := fdiv_le m SCALE_pos_nat
    have h2 : (fdiv m SCALE : ℝ) / SCALE ≤ ((m : ℝ) / SCALE) / SCALE :=
      div_le_div_of_nonneg_right h1 (le_of_lt hS)
    rw [div_div, hm_eq] at h2
    exact le_trans h2 hc.1
  · have h1 := le_cdiv M SCALE_pos_nat
    have h2 : ((M : ℝ) / SCALE) / SCALE ≤ (cdiv M SCALE : ℝ) / SCALE :=
      div_le_div_of_nonneg_right h1 (le_of_lt hS)
    rw [div_div, hM_eq] at h2
    exact le_trans hc.2 h2

/-- Tight squaring interval `I^2`. -/
def sq (I : Interval) : Interval :=
  if 0 ≤ I.lo then ⟨fdiv (I.lo * I.lo) SCALE, cdiv (I.hi * I.hi) SCALE⟩
  else if I.hi ≤ 0 then ⟨fdiv (I.hi * I.hi) SCALE, cdiv (I.lo * I.lo) SCALE⟩
  else ⟨0, cdiv (max (I.lo * I.lo) (I.hi * I.hi)) SCALE⟩

lemma mem_sq {I : Interval} {x : ℝ} (hx : mem I x) : mem (sq I) (x ^ 2) := by
  unfold mem sq at *
  have hS : (0 : ℝ) < (SCALE : ℝ) := SCALE_pos
  split_ifs with h1 h2
  · have hlo : (0 : ℝ) ≤ (I.lo : ℝ) / SCALE := div_nonneg (by exact_mod_cast h1) (le_of_lt hS)
    constructor
    · have hf := fdiv_le (I.lo * I.lo) SCALE_pos_nat
      have h3 : (fdiv (I.lo * I.lo) SCALE : ℝ) / SCALE ≤ ((I.lo : ℝ) / SCALE) ^ 2 := by
        have := div_le_div_of_nonneg_right hf (le_of_lt hS)
        push_cast at this; rw [div_div] at this; convert this using 1; ring
      exact le_trans h3 (pow_le_pow_left₀ hlo hx.1 2)
    · have hc := le_cdiv (I.hi * I.hi) SCALE_pos_nat
      have h3 : ((I.hi : ℝ) / SCALE) ^ 2 ≤ (cdiv (I.hi * I.hi) SCALE : ℝ) / SCALE := by
        have := div_le_div_of_nonneg_right hc (le_of_lt hS)
        push_cast at this; rw [div_div] at this; convert this using 1; ring
      exact le_trans (pow_le_pow_left₀ (le_trans hlo hx.1) hx.2 2) h3
  · have hhi : (I.hi : ℝ) / SCALE ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast h2) (le_of_lt hS)
    constructor
    · have hf := fdiv_le (I.hi * I.hi) SCALE_pos_nat
      have h3 : (fdiv (I.hi * I.hi) SCALE : ℝ) / SCALE ≤ ((I.hi : ℝ) / SCALE) ^ 2 := by
        have := div_le_div_of_nonneg_right hf (le_of_lt hS)
        push_cast at this; rw [div_div] at this; convert this using 1; ring
      have h4 : ((I.hi : ℝ) / SCALE) ^ 2 ≤ x ^ 2 := by nlinarith [hx.2]
      exact le_trans h3 h4
    · have hc := le_cdiv (I.lo * I.lo) SCALE_pos_nat
      have h3 : ((I.lo : ℝ) / SCALE) ^ 2 ≤ (cdiv (I.lo * I.lo) SCALE : ℝ) / SCALE := by
        have := div_le_div_of_nonneg_right hc (le_of_lt hS)
        push_cast at this; rw [div_div] at this; convert this using 1; ring
      have h4 : x ^ 2 ≤ ((I.lo : ℝ) / SCALE) ^ 2 := by nlinarith [hx.1, hx.2]
      exact le_trans h4 h3
  · constructor
    · simp; exact sq_nonneg x
    · set M := max (I.lo * I.lo) (I.hi * I.hi)
      have hc := le_cdiv M SCALE_pos_nat
      have h3 : max (((I.lo : ℝ) / SCALE) ^ 2) (((I.hi : ℝ) / SCALE) ^ 2)
          ≤ (cdiv M SCALE : ℝ) / SCALE := by
        have := div_le_div_of_nonneg_right hc (le_of_lt hS)
        rw [div_div] at this
        have hM_eq : (M : ℝ) / ((SCALE : ℝ) * (SCALE : ℝ))
            = max (((I.lo : ℝ) / SCALE) ^ 2) (((I.hi : ℝ) / SCALE) ^ 2) := by
          simp only [M, Int.cast_max, Int.cast_mul, max_div_pos (mul_nonneg (le_of_lt hS) (le_of_lt hS))]
          congr 1 <;> ring
        rwa [hM_eq] at this
      have h4 : x ^ 2 ≤ max (((I.lo : ℝ) / SCALE) ^ 2) (((I.hi : ℝ) / SCALE) ^ 2) := by
        rcases le_total 0 x with hx0 | hx0
        · exact le_trans (pow_le_pow_left₀ hx0 hx.2 2) (le_max_right _ _)
        · exact le_trans (by nlinarith [hx.1]) (le_max_left _ _)
      exact le_trans h4 h3

/-- Reciprocal of a strictly positive interval (`0 < I.lo`). -/
def invPos (I : Interval) : Interval :=
  if 0 < I.lo ∧ I.lo ≤ I.hi then
    ⟨fdiv ((SCALE : ℤ) * (SCALE : ℤ)) I.hi.toNat,
     cdiv ((SCALE : ℤ) * (SCALE : ℤ)) I.lo.toNat⟩
  else ⟨0, 0⟩

lemma mem_invPos {I : Interval} {x : ℝ} (hx : mem I x) (hpos : 0 < I.lo) :
    mem (invPos I) x⁻¹ := by
  have hle : I.lo ≤ I.hi := by
    have h1 : (I.lo : ℝ) / SCALE ≤ (I.hi : ℝ) / SCALE := le_trans hx.1 hx.2
    have h2 : (I.lo : ℝ) ≤ (I.hi : ℝ) := (div_le_div_iff_of_pos_right SCALE_pos).mp h1
    exact_mod_cast h2
  unfold mem invPos at *
  simp only [hpos, hle, and_self, ↓reduceIte]
  have hhi_pos : 0 < I.hi := lt_of_lt_of_le hpos hle
  have hlo_nat : 0 < I.lo.toNat := by omega
  have hhi_nat : 0 < I.hi.toNat := by omega
  have hlo_cast : (I.lo.toNat : ℝ) = (I.lo : ℝ) := by
    have : (I.lo.toNat : ℤ) = I.lo := Int.toNat_of_nonneg (le_of_lt hpos)
    exact_mod_cast this
  have hhi_cast : (I.hi.toNat : ℝ) = (I.hi : ℝ) := by
    have : (I.hi.toNat : ℤ) = I.hi := Int.toNat_of_nonneg (le_of_lt hhi_pos)
    exact_mod_cast this
  have hS : (0 : ℝ) < (SCALE : ℝ) := SCALE_pos
  have hloR : (0 : ℝ) < (I.lo : ℝ) := by exact_mod_cast hpos
  have hhiR : (0 : ℝ) < (I.hi : ℝ) := by exact_mod_cast hhi_pos
  have hx_pos : 0 < x := lt_of_lt_of_le (div_pos hloR hS) hx.1
  constructor
  · have hf := fdiv_le ((SCALE : ℤ) * (SCALE : ℤ)) hhi_nat
    have h1 : (fdiv ((SCALE : ℤ) * (SCALE : ℤ)) I.hi.toNat : ℝ) / SCALE ≤ (SCALE : ℝ) / (I.hi : ℝ) := by
      have := div_le_div_of_nonneg_right hf (le_of_lt hS)
      rw [hhi_cast] at this; push_cast at this
      have heq : (SCALE : ℝ) * (SCALE : ℝ) / (I.hi : ℝ) / (SCALE : ℝ) = (SCALE : ℝ) / (I.hi : ℝ) := by
        field_simp [SCALE_ne_zero, ne_of_gt hhiR]
      rwa [heq] at this
    have h2 : (SCALE : ℝ) / (I.hi : ℝ) ≤ x⁻¹ := by
      rw [div_le_iff₀ hhiR, ← one_div, one_div_mul_eq_div, le_div_iff₀ hx_pos]
      have := (le_div_iff₀ hS).mp hx.2; linarith
    exact le_trans h1 h2
  · have hc := le_cdiv ((SCALE : ℤ) * (SCALE : ℤ)) hlo_nat
    have h1 : (SCALE : ℝ) / (I.lo : ℝ) ≤ (cdiv ((SCALE : ℤ) * (SCALE : ℤ)) I.lo.toNat : ℝ) / SCALE := by
      have := div_le_div_of_nonneg_right hc (le_of_lt hS)
      rw [hlo_cast] at this; push_cast at this
      have heq : (SCALE : ℝ) * (SCALE : ℝ) / (I.lo : ℝ) / (SCALE : ℝ) = (SCALE : ℝ) / (I.lo : ℝ) := by
        field_simp [SCALE_ne_zero, ne_of_gt hloR]
      rwa [heq] at this
    have h2 : x⁻¹ ≤ (SCALE : ℝ) / (I.lo : ℝ) := by
      rw [le_div_iff₀ hloR, ← one_div, one_div_mul_eq_div, div_le_iff₀ hx_pos]
      have := (div_le_iff₀ hS).mp hx.1; linarith
    exact le_trans h2 h1

def divPos (I J : Interval) : Interval := mul I (invPos J)

lemma mem_divPos {I J : Interval} {x y : ℝ} (hx : mem I x) (hy : mem J y) (hpos : 0 < J.lo) :
    mem (divPos I J) (x / y) := by
  rw [div_eq_mul_inv]
  exact mem_mul hx (mem_invPos hy hpos)

/-- Kernel-reducible Newton integer square root guess (zero `Nat.log2`, zero `Nat.pow`, exact for `n < 2^128`).
    Uses `Nat.casesOn` (`match ... with | 0 => ... | k + 1 => ...`) to force strict CBV evaluation
    in Lean's kernel and prevent exponential WHNF duplication! -/
def isqrtStep (n x : ℕ) : ℕ :=
  match x with
  | 0 => 0
  | k + 1 => (k + 1 + n / (k + 1)) / 2

def isqrtLoop (n : ℕ) : ℕ → ℕ → ℕ
  | 0, x => x
  | fuel + 1, x =>
    match isqrtStep n x with
    | 0 => 0
    | k + 1 =>
      if k + 1 < x then isqrtLoop n fuel (k + 1) else x

def isqrtGuess (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    let init :=
      if n < 1099511627776 then 1048576
      else if n < 1152921504606846976 then 1073741824
      else if n < 1208925819614629174706176 then 1099511627776
      else if n < 1267650600228229401496703205376 then 1125899906842624
      else 1152921504606846976
    isqrtLoop n 12 init

/-- Self-certified floor integer square root: ALWAYS satisfies `(isqrtLo n)^2 ≤ n`. -/
def isqrtLo (n : ℕ) : ℕ :=
  match isqrtGuess n with
  | 0 => 0
  | k + 1 => if (k + 1) * (k + 1) ≤ n then k + 1 else 0

/-- Self-certified ceil integer square root: ALWAYS satisfies `n ≤ (isqrtHi n)^2`. -/
def isqrtHi (n : ℕ) : ℕ :=
  match isqrtGuess n with
  | 0 => if n = 0 then 0 else if n ≤ 1 then 1 else n + 1
  | k + 1 =>
    if n ≤ (k + 1) * (k + 1) then k + 1
    else if n ≤ (k + 2) * (k + 2) then k + 2
    else n + 1

lemma isqrtLo_sq_le (n : ℕ) : (isqrtLo n) ^ 2 ≤ n := by
  unfold isqrtLo
  cases isqrtGuess n with
  | zero => simp
  | succ k =>
    dsimp only
    split_ifs with h
    · simpa [_root_.sq] using h
    · simp

lemma le_isqrtHi_sq (n : ℕ) : n ≤ (isqrtHi n) ^ 2 := by
  unfold isqrtHi
  cases isqrtGuess n with
  | zero =>
    dsimp only
    split_ifs with h1 h2
    · subst h1; simp
    · simpa using h2
    · rw [_root_.sq]; nlinarith
  | succ k =>
    dsimp only
    split_ifs with h1 h2
    · simpa [_root_.sq] using h1
    · simpa [_root_.sq] using h2
    · rw [_root_.sq]; nlinarith

/-- Exact 1-ULP kernel-reducible square root interval via self-certified Newton iteration! -/
def sqrt (I : Interval) : Interval :=
  if 0 ≤ I.lo ∧ I.lo ≤ I.hi then
    let lo := (isqrtLo (I.lo.toNat * SCALE) : ℤ)
    let hi := (isqrtHi (I.hi.toNat * SCALE) : ℤ)
    ⟨lo, hi⟩
  else if 0 ≤ I.hi then
    ⟨0, (isqrtHi (I.hi.toNat * SCALE) : ℤ)⟩
  else ⟨0, 0⟩

lemma mem_sqrt {I : Interval} {x : ℝ} (hx : mem I x) (hx0 : 0 ≤ x) :
    mem (sqrt I) (Real.sqrt x) := by
  have hS : (0 : ℝ) < (SCALE : ℝ) := SCALE_pos
  have hhi0 : 0 ≤ I.hi := by
    have h1 := mul_le_mul_of_nonneg_right (le_trans hx0 hx.2) (le_of_lt hS)
    rw [zero_mul, div_mul_cancel₀ _ SCALE_ne_zero] at h1
    exact_mod_cast h1
  have hhi_cast : (I.hi.toNat : ℝ) = (I.hi : ℝ) := by
    have : (I.hi.toNat : ℤ) = I.hi := Int.toNat_of_nonneg hhi0
    exact_mod_cast this
  have hhi_ub : Real.sqrt x ≤ (((isqrtHi (I.hi.toNat * SCALE) : ℤ) : ℝ)) / SCALE := by
    have hsq : I.hi.toNat * SCALE ≤ (isqrtHi (I.hi.toNat * SCALE)) ^ 2 :=
      le_isqrtHi_sq (I.hi.toNat * SCALE)
    have hsqR : (I.hi : ℝ) * SCALE ≤ (((isqrtHi (I.hi.toNat * SCALE) : ℤ) : ℝ)) ^ 2 := by
      rw [← hhi_cast]; push_cast; exact_mod_cast hsq
    have hdiv : x ≤ ((((isqrtHi (I.hi.toNat * SCALE) : ℤ) : ℝ)) / SCALE) ^ 2 := by
      have : (I.hi : ℝ) / SCALE ≤ ((((isqrtHi (I.hi.toNat * SCALE) : ℤ) : ℝ)) / SCALE) ^ 2 := by
        rw [div_pow, div_le_div_iff₀ hS (sq_pos_of_pos hS)]
        nlinarith [hsqR]
      exact le_trans hx.2 this
    calc Real.sqrt x ≤ Real.sqrt (((((isqrtHi (I.hi.toNat * SCALE) : ℤ) : ℝ)) / SCALE) ^ 2) :=
          Real.sqrt_le_sqrt hdiv
      _ = (((isqrtHi (I.hi.toNat * SCALE) : ℤ) : ℝ)) / SCALE :=
          Real.sqrt_sq (by positivity)
  unfold sqrt
  split_ifs with h1
  · have hlo_cast : (I.lo.toNat : ℝ) = (I.lo : ℝ) := by
      have : (I.lo.toNat : ℤ) = I.lo := Int.toNat_of_nonneg h1.1
      exact_mod_cast this
    unfold mem
    constructor
    · have hsq : (isqrtLo (I.lo.toNat * SCALE)) ^ 2 ≤ I.lo.toNat * SCALE :=
        isqrtLo_sq_le (I.lo.toNat * SCALE)
      have hsqR : ((isqrtLo (I.lo.toNat * SCALE) : ℝ)) ^ 2 ≤ (I.lo : ℝ) * SCALE := by
        rw [← hlo_cast]; exact_mod_cast hsq
      have hdiv : ((isqrtLo (I.lo.toNat * SCALE) : ℝ) / SCALE) ^ 2 ≤ x := by
        have : ((isqrtLo (I.lo.toNat * SCALE) : ℝ) / SCALE) ^ 2 ≤ (I.lo : ℝ) / SCALE := by
          rw [div_pow, div_le_div_iff₀ (sq_pos_of_pos hS) hS]
          nlinarith [hsqR]
        exact le_trans this hx.1
      calc ((isqrtLo (I.lo.toNat * SCALE) : ℤ) : ℝ) / SCALE
          = Real.sqrt (((isqrtLo (I.lo.toNat * SCALE) : ℝ) / SCALE) ^ 2) := by
            push_cast; exact (Real.sqrt_sq (by positivity)).symm
        _ ≤ Real.sqrt x := Real.sqrt_le_sqrt hdiv
    · exact hhi_ub
  · exact ⟨by simp [Real.sqrt_nonneg], hhi_ub⟩

def maxZero (I : Interval) : Interval := ⟨max 0 I.lo, max 0 I.hi⟩
def maxIv (I J : Interval) : Interval := ⟨max I.lo J.lo, max I.hi J.hi⟩
def minIv (I J : Interval) : Interval := ⟨min I.lo J.lo, min I.hi J.hi⟩

lemma mem_maxZero {I : Interval} {x : ℝ} (hx : mem I x) : mem (maxZero I) (max 0 x) := by
  unfold mem maxZero at *
  have hS : (0 : ℝ) < (SCALE : ℝ) := SCALE_pos
  constructor
  · rw [Int.cast_max, Int.cast_zero, max_div_pos (le_of_lt hS), zero_div]
    exact max_le_max le_rfl hx.1
  · rw [Int.cast_max, Int.cast_zero, max_div_pos (le_of_lt hS), zero_div]
    exact max_le_max le_rfl hx.2

lemma mem_maxIv {I J : Interval} {x y : ℝ} (hx : mem I x) (hy : mem J y) :
    mem (maxIv I J) (max x y) := by
  unfold mem maxIv at *
  have hS : (0 : ℝ) < (SCALE : ℝ) := SCALE_pos
  constructor
  · rw [Int.cast_max, max_div_pos (le_of_lt hS)]; exact max_le_max hx.1 hy.1
  · rw [Int.cast_max, max_div_pos (le_of_lt hS)]; exact max_le_max hx.2 hy.2

lemma mem_minIv {I J : Interval} {x y : ℝ} (hx : mem I x) (hy : mem J y) :
    mem (minIv I J) (min x y) := by
  unfold mem minIv at *
  have hS : (0 : ℝ) < (SCALE : ℝ) := SCALE_pos
  constructor
  · rw [Int.cast_min, min_div_pos (le_of_lt hS)]; exact min_le_min hx.1 hy.1
  · rw [Int.cast_min, min_div_pos (le_of_lt hS)]; exact min_le_min hx.2 hy.2

/-! ### Certified Logarithm via Odd Taylor Series of `log((1 + u) / (1 - u))` -/

/-- Exact derivative remainder bound for `log((1 + u) / (1 - u)) - 2 ∑_{k < N} u^(2k+1)/(2k+1)`.
    For `0 ≤ u ≤ R < 1`:
      `0 ≤ log((1 + u)/(1 - u)) - 2 ∑_{k < N} u^(2k+1)/(2k+1) ≤ 2 * u^(2N+1) / ((2N+1) * (1 - R^2))`. -/
lemma log_one_add_div_sub_bounds (N : ℕ) {R u : ℝ} (hR : R < 1) (hu0 : 0 ≤ u) (huR : u ≤ R) :
    let S (t : ℝ) : ℝ := 2 * ∑ k ∈ Finset.range N, t ^ (2 * k + 1) / (2 * k + 1 : ℝ)
    0 ≤ Real.log ((1 + u) / (1 - u)) - S u ∧
    Real.log ((1 + u) / (1 - u)) - S u ≤ 2 * u ^ (2 * N + 1) / ((2 * N + 1 : ℝ) * (1 - R ^ 2)) := by
  intro S
  have h1mR2 : 0 < 1 - R ^ 2 := by nlinarith
  let rem (t : ℝ) : ℝ := Real.log ((1 + t) / (1 - t)) - S t
  have hrem_deriv : ∀ t ∈ Set.Icc (0 : ℝ) R,
      HasDerivAt rem (2 * t ^ (2 * N) / (1 - t ^ 2)) t := by
    intro t ht
    have h1pt : 0 < 1 + t := by linarith [ht.1]
    have h1mt : 0 < 1 - t := by linarith [ht.2]
    have hd1 : HasDerivAt (fun x : ℝ => Real.log (1 + x)) (1 / (1 + t)) t := by
      have := (Real.hasDerivAt_log (ne_of_gt h1pt)).comp t
        (by simpa using (hasDerivAt_const t (1 : ℝ)).fun_add (hasDerivAt_id' t))
      exact this.congr_deriv (by ring)
    have hd2 : HasDerivAt (fun x : ℝ => Real.log (1 - x)) (-(1 / (1 - t))) t := by
      have := (Real.hasDerivAt_log (ne_of_gt h1mt)).comp t
        (by simpa using (hasDerivAt_const t (1 : ℝ)).fun_sub (hasDerivAt_id' t))
      exact this.congr_deriv (by ring)
    have hlog_eq : (fun x => Real.log (1 + x) - Real.log (1 - x)) =ᶠ[nhds t]
        (fun x => Real.log ((1 + x) / (1 - x))) := by
      filter_upwards [Ioo_mem_nhds (show (-1 : ℝ) < t by linarith [ht.1]) (show t < 1 by linarith [ht.2])] with x hx
      rw [Real.log_div (ne_of_gt (by linarith [hx.1])) (ne_of_gt (by linarith [hx.2]))]
    have hd_log : HasDerivAt (fun x => Real.log ((1 + x) / (1 - x))) (2 / (1 - t ^ 2)) t := by
      have h := (hd1.fun_sub hd2).congr_of_eventuallyEq hlog_eq.symm
      have h1mt2 : 1 - t ^ 2 ≠ 0 := ne_of_gt (by nlinarith [ht.1, ht.2])
      exact h.congr_deriv (by field_simp [ne_of_gt h1pt, ne_of_gt h1mt, h1mt2]; ring)
    have hd_S : HasDerivAt S (2 * ∑ k ∈ Finset.range N, t ^ (2 * k)) t := by
      have hterm : ∀ k ∈ Finset.range N,
          HasDerivAt (fun x : ℝ => x ^ (2 * k + 1) / (2 * k + 1 : ℝ)) (t ^ (2 * k)) t := by
        intro k _
        have h1 := (hasDerivAt_pow (2 * k + 1) t).div_const (2 * k + 1 : ℝ)
        exact h1.congr_deriv (by
          have hne : (2 * k + 1 : ℝ) ≠ 0 := by positivity
          rw [Nat.add_sub_cancel]; push_cast; field_simp [hne])
      exact (HasDerivAt.fun_sum hterm).const_mul 2
    have hgeom : (1 - t ^ 2) * (∑ k ∈ Finset.range N, t ^ (2 * k)) = 1 - t ^ (2 * N) := by
      have h := mul_geom_sum (t ^ 2) N
      have hpow : ∀ k, (t ^ 2) ^ k = t ^ (2 * k) := fun k => by rw [← pow_mul]
      simp_rw [hpow] at h
      linarith
    have h1mt2_ne : 1 - t ^ 2 ≠ 0 := ne_of_gt (by nlinarith [ht.1, ht.2])
    exact (hd_log.fun_sub hd_S).congr_deriv (by
      field_simp [h1mt2_ne]
      linarith [hgeom])
  have hrem0 : rem 0 = 0 := by
    simp only [rem, S, add_zero, sub_zero, div_one, Real.log_one, zero_sub, neg_eq_zero,
      mul_eq_zero, OfNat.ofNat_ne_zero, false_or]
    apply Finset.sum_eq_zero; intro k _; simp
  constructor
  · -- rem is monotone increasing on [0, R], so rem u ≥ rem 0 = 0!
    have hmono : MonotoneOn rem (Set.Icc 0 R) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc 0 R)
      · intro t ht; exact (hrem_deriv t ht).continuousAt.continuousWithinAt
      · intro t ht; exact (hrem_deriv t (interior_subset ht)).differentiableAt.differentiableWithinAt
      · intro t ht
        have ht' := interior_subset ht
        rw [(hrem_deriv t ht').deriv]
        have h1mt2 : 0 < 1 - t ^ 2 := by nlinarith [ht'.1, ht'.2]
        have ht0 : 0 ≤ t := ht'.1
        positivity
    rw [← hrem0]
    exact hmono ⟨le_rfl, le_trans hu0 huR⟩ ⟨hu0, huR⟩ hu0
  · -- g(t) := 2 * t^(2N+1) / ((2N+1)(1 - R^2)) - rem t is monotone increasing on [0, R]!
    let g (t : ℝ) : ℝ := 2 * t ^ (2 * N + 1) / ((2 * N + 1 : ℝ) * (1 - R ^ 2)) - rem t
    have hg_deriv : ∀ t ∈ Set.Icc (0 : ℝ) R,
        HasDerivAt g (2 * t ^ (2 * N) / (1 - R ^ 2) - 2 * t ^ (2 * N) / (1 - t ^ 2)) t := by
      intro t ht
      have h1 := ((hasDerivAt_pow (2 * N + 1) t).const_mul 2).div_const ((2 * N + 1 : ℝ) * (1 - R ^ 2))
      have h1' : HasDerivAt (fun x => 2 * x ^ (2 * N + 1) / ((2 * N + 1 : ℝ) * (1 - R ^ 2)))
          (2 * t ^ (2 * N) / (1 - R ^ 2)) t := by
        exact h1.congr_deriv (by
          have hne : (2 * N + 1 : ℝ) ≠ 0 := by positivity
          have hne2 : 1 - R ^ 2 ≠ 0 := ne_of_gt h1mR2
          rw [Nat.add_sub_cancel]; push_cast; field_simp [hne, hne2])
      exact h1'.fun_sub (hrem_deriv t ht)
    have hg_mono : MonotoneOn g (Set.Icc 0 R) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc 0 R)
      · intro t ht; exact (hg_deriv t ht).continuousAt.continuousWithinAt
      · intro t ht; exact (hg_deriv t (interior_subset ht)).differentiableAt.differentiableWithinAt
      · intro t ht
        have ht' := interior_subset ht
        rw [(hg_deriv t ht').deriv]
        have h1mt2 : 0 < 1 - t ^ 2 := by nlinarith [ht'.1, ht'.2]
        have hle : 1 - R ^ 2 ≤ 1 - t ^ 2 := by nlinarith [ht'.1, ht'.2]
        have ht0 : 0 ≤ t := ht'.1
        have hdiv : 2 * t ^ (2 * N) / (1 - t ^ 2) ≤ 2 * t ^ (2 * N) / (1 - R ^ 2) :=
          div_le_div_of_nonneg_left (by positivity) h1mR2 hle
        linarith
    have hg0 : g 0 = 0 := by simp [g, hrem0]
    have hgu := hg_mono ⟨le_rfl, le_trans hu0 huR⟩ ⟨hu0, huR⟩ hu0
    rw [hg0] at hgu
    dsimp only [g, rem] at hgu
    linarith

/-- Oddness extension for `u ∈ [-R, 0]`:
    `-2 * (-u)^(2N+1) / ((2N+1)(1 - R^2)) ≤ log((1 + u)/(1 - u)) - S u ≤ 0`. -/
lemma log_one_add_div_sub_bounds_neg (N : ℕ) {R u : ℝ} (hR : R < 1) (hu0 : u ≤ 0) (huR : -R ≤ u) :
    let S (t : ℝ) : ℝ := 2 * ∑ k ∈ Finset.range N, t ^ (2 * k + 1) / (2 * k + 1 : ℝ);
    (-(2 * (-u) ^ (2 * N + 1) / ((2 * N + 1 : ℝ) * (1 - R ^ 2)))) ≤ Real.log ((1 + u) / (1 - u)) - S u ∧
    Real.log ((1 + u) / (1 - u)) - S u ≤ 0 := by
  intro S
  have hpos := log_one_add_div_sub_bounds N hR (u := -u) (by linarith) (by linarith)
  have hlog_neg : Real.log ((1 + (-u)) / (1 - (-u))) = -Real.log ((1 + u) / (1 - u)) := by
    have h1 : (1 + (-u)) / (1 - (-u)) = ((1 + u) / (1 - u))⁻¹ := by
      have h1pu : 1 + u ≠ 0 := ne_of_gt (by linarith)
      have h1mu : 1 - u ≠ 0 := ne_of_gt (by linarith)
      rw [inv_div]; ring
    rw [h1, Real.log_inv]
  have hS_neg : S (-u) = -S u := by
    simp only [S, ← Finset.sum_neg_distrib, ← mul_neg]
    congr 1; apply Finset.sum_congr rfl; intro k _
    rw [neg_pow, show (-1 : ℝ) ^ (2 * k + 1) = -1 by simp [pow_add, pow_mul]]
    ring
  have hpos' : 0 ≤ Real.log ((1 + (-u)) / (1 - (-u))) - S (-u) ∧
      Real.log ((1 + (-u)) / (1 - (-u))) - S (-u) ≤ 2 * (-u) ^ (2 * N + 1) / ((2 * N + 1 : ℝ) * (1 - R ^ 2)) := hpos
  rw [hlog_neg, hS_neg] at hpos'
  constructor <;> linarith

/-- Certified 50-bit enclosure of `L = Real.log 2`!
    `floor(log 2 * 2^50) = 780414346020669`, `ceil(log 2 * 2^50) = 780414346020670`. -/
def LN2 : Interval := ⟨780414346020669, 780414346020670⟩

lemma mem_LN2 : mem LN2 L := by
  -- Use log_one_add_div_sub_bounds with N = 18, u = 1/3, R = 1/3!
  have hb := log_one_add_div_sub_bounds 18 (R := 1 / 3) (u := 1 / 3) (by norm_num) (by norm_num) le_rfl
  dsimp only at hb
  have h2 : (1 + (1 / 3 : ℝ)) / (1 - 1 / 3) = 2 := by norm_num
  rw [h2] at hb
  unfold mem LN2 L SCALE
  constructor
  · have hlo : (780414346020669 : ℝ) / ((2 ^ 50 : ℕ) : ℝ)
        ≤ 2 * ∑ k ∈ Finset.range 18, (1 / 3 : ℝ) ^ (2 * k + 1) / (2 * k + 1 : ℝ) := by
      push_cast; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
    push_cast at hlo ⊢; linarith [hb.1]
  · have hhi : 2 * ∑ k ∈ Finset.range 18, (1 / 3 : ℝ) ^ (2 * k + 1) / (2 * k + 1 : ℝ)
        + 2 * (1 / 3 : ℝ) ^ (2 * 18 + 1) / ((2 * 18 + 1 : ℝ) * (1 - (1 / 3 : ℝ) ^ 2))
        ≤ (780414346020670 : ℝ) / ((2 ^ 50 : ℕ) : ℝ) := by
      push_cast; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
    push_cast at hhi ⊢; linarith [hb.2]

/-- Compute an enclosure of `2 * ∑_{k < 10} u^(2k+1)/(2k+1)` plus remainder for `u = (num / den)` with `|u| ≤ 1/7`! -/
def logReducedCore (num den : ℤ) : Interval :=
  -- u = num / den with |u| ≤ 1/7, den > 0
  -- Evaluate term by term using Interval arithmetic!
  let u := ofRat num den.toNat
  let u2 := mul u u
  -- Compute sum_{k=0}^9 u^(2k+1) / (2k+1) using Horner/iterative powers (only 10 terms!)
  let rec loop (k : ℕ) (p : Interval) (acc : Interval) : Interval :=
    match k with
    | 0 => acc
    | k' + 1 =>
      let idx := 10 - k  -- 0, 1, ..., 9
      let denom := 2 * idx + 1
      let term := divPos p (ofInt denom)
      loop k' (mul p u2) (add acc term)
  let s := mul (ofInt 2) (loop 10 u (ofInt 0))
  -- Remainder bound for |u| ≤ 1/7, N = 10: 2 * (1/7)^21 / (21 * 48/49) < 1 / 2^55 < 1 / SCALE!
  -- So adding [-1, +1] ULPs strictly covers the remainder!
  ⟨s.lo - 1, s.hi + 1⟩

lemma mem_logReducedCore {num den : ℤ} (hden : 0 < den)
    (hub : |(num : ℝ) / (den : ℝ)| ≤ 1 / 5) :
    let y := ((den + num : ℤ) : ℝ) / ((den - num : ℤ) : ℝ)
    mem (logReducedCore num den) (Real.log y) := by
  intro y
  set uR : ℝ := (num : ℝ) / (den : ℝ)
  have hdenR : (0 : ℝ) < (den : ℝ) := by exact_mod_cast hden
  have hden_nat : 0 < den.toNat := by omega
  have hden_cast : (den.toNat : ℝ) = (den : ℝ) := by
    have : (den.toNat : ℤ) = den := Int.toNat_of_nonneg (le_of_lt hden)
    exact_mod_cast this
  have hu_mem : mem (ofRat num den.toNat) uR := by
    have := mem_ofRat num hden_nat
    rwa [hden_cast] at this
  have hu2_mem : mem (mul (ofRat num den.toNat) (ofRat num den.toNat)) (uR ^ 2) := by
    rw [_root_.sq]; exact mem_mul hu_mem hu_mem
  have hy_eq : y = (1 + uR) / (1 - uR) := by
    simp only [y, uR]; push_cast
    have h1mu : 1 - (num : ℝ) / (den : ℝ) ≠ 0 := by
      have := (abs_le.mp hub).2; linarith
    field_simp [ne_of_gt hdenR, h1mu]
  -- Prove loop invariant by explicit unfolding (10 steps!):
  have hloop : mem (logReducedCore.loop (mul (ofRat num den.toNat) (ofRat num den.toNat)) 10
      (ofRat num den.toNat) (ofInt 0))
      (∑ k ∈ Finset.range 10, uR ^ (2 * k + 1) / (2 * k + 1 : ℝ)) := by
    have hinv : ∀ (m : ℕ), m ≤ 10 →
        ∀ (p acc : Interval) (accR : ℝ),
          mem p (uR ^ (2 * (10 - m) + 1)) →
          mem acc accR →
          mem (logReducedCore.loop (mul (ofRat num den.toNat) (ofRat num den.toNat)) m p acc)
              (accR + ∑ j ∈ Finset.range m, uR ^ (2 * (10 - m + j) + 1) / ((2 * (10 - m + j) + 1 : ℕ) : ℝ)) := by
      intro m
      induction m with
      | zero =>
        intro _ p acc accR _ hacc; simpa [logReducedCore.loop] using hacc
      | succ m' ih =>
        intro hm p acc accR hp hacc
        simp only [logReducedCore.loop]
        let dN : ℕ := 2 * (10 - (m' + 1)) + 1
        have hd_pos : 0 < (ofInt (dN : ℤ)).lo := by
          unfold ofInt; have := SCALE_pos_nat; positivity
        have hterm : mem (divPos p (ofInt (dN : ℤ)))
            (uR ^ (2 * (10 - (m' + 1)) + 1) / ((2 * (10 - (m' + 1)) + 1 : ℕ) : ℝ)) := by
          have h := mem_divPos hp (mem_ofInt (dN : ℤ)) hd_pos
          simpa [dN] using h
        have hp' : mem (mul p (mul (ofRat num den.toNat) (ofRat num den.toNat)))
            (uR ^ (2 * (10 - m') + 1)) := by
          have h := mem_mul hp hu2_mem
          have hexp : 2 * (10 - (m' + 1)) + 1 + 2 = 2 * (10 - m') + 1 := by omega
          rw [← pow_add, hexp] at h; exact h
        have hrec := ih (Nat.le_of_succ_le hm) _ _ _ hp' (mem_add hacc hterm)
        have hsum_eq :
            accR + ∑ j ∈ Finset.range (m' + 1), uR ^ (2 * (10 - (m' + 1) + j) + 1) / ((2 * (10 - (m' + 1) + j) + 1 : ℕ) : ℝ)
            = (accR + uR ^ (2 * (10 - (m' + 1)) + 1) / ((2 * (10 - (m' + 1)) + 1 : ℕ) : ℝ))
              + ∑ j ∈ Finset.range m', uR ^ (2 * (10 - m' + j) + 1) / ((2 * (10 - m' + j) + 1 : ℕ) : ℝ) := by
          rw [Finset.sum_range_succ']
          have hstep : ∑ j ∈ Finset.range m',
                uR ^ (2 * (10 - (m' + 1) + (j + 1)) + 1) / ((2 * (10 - (m' + 1) + (j + 1)) + 1 : ℕ) : ℝ)
              = ∑ j ∈ Finset.range m',
                uR ^ (2 * (10 - m' + j) + 1) / ((2 * (10 - m' + j) + 1 : ℕ) : ℝ) := by
            apply Finset.sum_congr rfl; intro j _
            have hidx : 10 - (m' + 1) + (j + 1) = 10 - m' + j := by omega
            rw [hidx]
          rw [hstep, add_zero]; ring
        rw [hsum_eq]; exact hrec
    have h0 := hinv 10 le_rfl (ofRat num den.toNat) (ofInt 0) 0 (by simpa using hu_mem) (by simpa using mem_ofInt 0)
    simpa [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using h0
  have hs_mem := mem_mul (mem_ofInt 2) hloop
  push_cast at hs_mem
  -- Remainder bound: 2 * (1/5)^21 / (21 * (1 - (1/5)^2)) < 1 / SCALE!
  have hrem_tiny : 2 * (1 / 5 : ℝ) ^ (2 * 10 + 1) / ((2 * 10 + 1 : ℝ) * (1 - (1 / 5 : ℝ) ^ 2))
      ≤ (1 : ℝ) / (SCALE : ℝ) := by
    unfold SCALE; norm_num
  have hrem_abs : |Real.log y - 2 * ∑ k ∈ Finset.range 10, uR ^ (2 * k + 1) / (2 * k + 1 : ℝ)|
      ≤ (1 : ℝ) / (SCALE : ℝ) := by
    rw [hy_eq]
    rcases le_total 0 uR with hu0 | hu0
    · have hb := log_one_add_div_sub_bounds 10 (R := 1 / 5) (by norm_num) hu0 (abs_le.mp hub).2
      dsimp only at hb
      have hpow : uR ^ (2 * 10 + 1) ≤ (1 / 5 : ℝ) ^ (2 * 10 + 1) :=
        pow_le_pow_left₀ hu0 (abs_le.mp hub).2 _
      have h1 : 2 * uR ^ (2 * 10 + 1) / ((2 * 10 + 1 : ℝ) * (1 - (1 / 5 : ℝ) ^ 2)) ≤ 1 / SCALE :=
        le_trans (div_le_div_of_nonneg_right (by linarith) (by norm_num)) hrem_tiny
      rw [abs_of_nonneg hb.1]; linarith [hb.2]
    · have hb := log_one_add_div_sub_bounds_neg 10 (R := 1 / 5) (by norm_num) hu0 (abs_le.mp hub).1
      dsimp only at hb
      have hpow : (-uR) ^ (2 * 10 + 1) ≤ (1 / 5 : ℝ) ^ (2 * 10 + 1) :=
        pow_le_pow_left₀ (by linarith) (by linarith [(abs_le.mp hub).1]) _
      have h1 : 2 * (-uR) ^ (2 * 10 + 1) / ((2 * 10 + 1 : ℝ) * (1 - (1 / 5 : ℝ) ^ 2)) ≤ 1 / SCALE :=
        le_trans (div_le_div_of_nonneg_right (by linarith) (by norm_num)) hrem_tiny
      rw [abs_of_nonpos hb.2]; linarith [hb.1]
  unfold mem logReducedCore at *
  have habs := abs_le.mp hrem_abs
  constructor
  · push_cast; rw [sub_div]; linarith [hs_mem.1, habs.1]
  · push_cast; rw [add_div]; linarith [hs_mem.2, habs.2]

/-- Certified enclosure of `Real.log (a / SCALE)` for any `a : ℕ` (`a > 0`),
    using bit-length range reduction to `[2/3, 4/3]`! -/
def logNat (a : ℕ) : Interval :=
  if a = 0 then ⟨0, 0⟩
  else
    let k := Nat.log2 a
    let p2 := 2 ^ k
    -- a ∈ [p2, 2*p2). If 3 * a ≤ 4 * p2, use e = k - SCALE_BITS and y = a / p2 ∈ [1, 4/3];
    -- else use e = k + 1 - SCALE_BITS and y = a / (2 * p2) ∈ [2/3, 1)!
    if 3 * a ≤ 4 * p2 then
      let e : ℤ := (k : ℤ) - (SCALE_BITS : ℤ)
      -- y = a / p2, so u = (y - 1)/(y + 1) = (a - p2) / (a + p2) ∈ [0, 1/7]
      let core := logReducedCore ((a : ℤ) - (p2 : ℤ)) ((a : ℤ) + (p2 : ℤ))
      add (mul (ofInt e) LN2) core
    else
      let e : ℤ := (k : ℤ) + 1 - (SCALE_BITS : ℤ)
      let p2' := 2 * p2
      -- y = a / p2', so u = (a - p2') / (a + p2') ∈ [-1/7, 0]
      let core := logReducedCore ((a : ℤ) - (p2' : ℤ)) ((a : ℤ) + (p2' : ℤ))
      add (mul (ofInt e) LN2) core

lemma mem_logNat {a : ℕ} (ha : 0 < a) : mem (logNat a) (Real.log ((a : ℝ) / (SCALE : ℝ))) := by
  unfold logNat
  simp only [Nat.ne_of_gt ha, ↓reduceIte]
  set k := Nat.log2 a
  set p2 := 2 ^ k
  have ha_ge : p2 ≤ a := Nat.log2_self_le (Nat.ne_of_gt ha)
  have ha_lt : a < 2 * p2 := by
    have := Nat.lt_log2_self (n := a)
    -- Use Nat.log2_lt: a < 2^(log2 a + 1)
    have hlt : a < 2 ^ (k + 1) := by
      by_contra h
      push Not at h
      have hge := Nat.le_log2 (Nat.ne_of_gt ha) |>.mpr h
      omega
    simpa [p2, pow_succ, mul_comm] using hlt
  have hp2_pos : 0 < p2 := Nat.pow_pos (by decide)
  have hS_eq : (SCALE : ℝ) = (2 : ℝ) ^ (SCALE_BITS : ℕ) := by unfold SCALE SCALE_BITS; push_cast; norm_num
  split_ifs with hcase
  · -- Branch 1: 3 * a ≤ 4 * p2, so y = a / p2 ∈ [1, 4/3], u ∈ [0, 1/7]!
    let num : ℤ := (a : ℤ) - (p2 : ℤ)
    let den : ℤ := (a : ℤ) + (p2 : ℤ)
    have hden_pos : 0 < den := by omega
    have hub : |(num : ℝ) / (den : ℝ)| ≤ 1 / 5 := by
      have hnn : 0 ≤ (num : ℝ) / (den : ℝ) := div_nonneg (by exact_mod_cast (show 0 ≤ num by omega))
        (by exact_mod_cast (le_of_lt hden_pos))
      rw [abs_of_nonneg hnn, div_le_iff₀ (by exact_mod_cast hden_pos : (0 : ℝ) < (den : ℝ))]
      have h5 : 5 * num ≤ den := by omega
      have h5R : (5 : ℝ) * (num : ℝ) ≤ (den : ℝ) := by exact_mod_cast h5
      linarith
    have hcore := mem_logReducedCore hden_pos hub
    have hy_eq : (((den + num : ℤ) : ℝ) / ((den - num : ℤ) : ℝ)) = (a : ℝ) / (p2 : ℝ) := by
      have h1 : den + num = 2 * (a : ℤ) := by omega
      have h2 : den - num = 2 * (p2 : ℤ) := by omega
      rw [h1, h2]; push_cast; ring
    rw [hy_eq] at hcore
    have hlog_eq : Real.log ((a : ℝ) / (SCALE : ℝ))
        = (((k : ℤ) - (SCALE_BITS : ℤ) : ℤ) : ℝ) * L + Real.log ((a : ℝ) / (p2 : ℝ)) := by
      have hp2R : (p2 : ℝ) = (2 : ℝ) ^ k := by unfold p2; push_cast; rfl
      have hratio : (a : ℝ) / (SCALE : ℝ) = (2 : ℝ) ^ ((k : ℤ) - (SCALE_BITS : ℤ)) * ((a : ℝ) / (p2 : ℝ)) := by
        rw [hS_eq, hp2R, zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_natCast, zpow_natCast]
        field_simp [show (2 : ℝ) ^ k ≠ 0 by positivity, show (2 : ℝ) ^ SCALE_BITS ≠ 0 by positivity]
      rw [hratio, Real.log_mul (ne_of_gt (zpow_pos (by norm_num) _))
            (ne_of_gt (div_pos (Nat.cast_pos.mpr ha) (Nat.cast_pos.mpr hp2_pos))),
          Real.log_zpow]; rfl
    rw [hlog_eq]
    exact mem_add (mem_mul (mem_ofInt _) mem_LN2) hcore
  · -- Branch 2: 4 * p2 < 3 * a and a < 2 * p2, so y = a / (2 * p2) ∈ [2/3, 1), u ∈ [-1/5, 0]!
    set p2' := 2 * p2
    have hp2'_pos : 0 < p2' := by omega
    let num : ℤ := (a : ℤ) - (p2' : ℤ)
    let den : ℤ := (a : ℤ) + (p2' : ℤ)
    have hden_pos : 0 < den := by omega
    have hub : |(num : ℝ) / (den : ℝ)| ≤ 1 / 5 := by
      have hnp : (num : ℝ) / (den : ℝ) ≤ 0 := div_nonpos_of_nonpos_of_nonneg
        (by exact_mod_cast (show num ≤ 0 by omega)) (by exact_mod_cast (le_of_lt hden_pos))
      rw [abs_of_nonpos hnp, ← neg_div, div_le_iff₀ (by exact_mod_cast hden_pos : (0 : ℝ) < (den : ℝ))]
      have h5 : 5 * (-num) ≤ den := by omega
      have h5R : (5 : ℝ) * (-(num : ℝ)) ≤ (den : ℝ) := by exact_mod_cast h5
      linarith
    have hcore := mem_logReducedCore hden_pos hub
    have hy_eq : (((den + num : ℤ) : ℝ) / ((den - num : ℤ) : ℝ)) = (a : ℝ) / (p2' : ℝ) := by
      have h1 : den + num = 2 * (a : ℤ) := by omega
      have h2 : den - num = 2 * (p2' : ℤ) := by omega
      rw [h1, h2]; push_cast; ring
    rw [hy_eq] at hcore
    have hlog_eq : Real.log ((a : ℝ) / (SCALE : ℝ))
        = (((k : ℤ) + 1 - (SCALE_BITS : ℤ) : ℤ) : ℝ) * L + Real.log ((a : ℝ) / (p2' : ℝ)) := by
      have hp2R : (p2' : ℝ) = (2 : ℝ) ^ (k + 1) := by
        simp only [p2', p2]; push_cast; rw [pow_succ]; ring
      have hratio : (a : ℝ) / (SCALE : ℝ) = (2 : ℝ) ^ ((k : ℤ) + 1 - (SCALE_BITS : ℤ)) * ((a : ℝ) / (p2' : ℝ)) := by
        rw [hS_eq, hp2R, zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
            zpow_natCast, zpow_one, zpow_natCast, pow_succ]
        field_simp [show (2 : ℝ) ^ k ≠ 0 by positivity, show (2 : ℝ) ^ SCALE_BITS ≠ 0 by positivity]
      rw [hratio, Real.log_mul (ne_of_gt (zpow_pos (by norm_num) _))
            (ne_of_gt (div_pos (Nat.cast_pos.mpr ha) (Nat.cast_pos.mpr hp2'_pos))),
          Real.log_zpow]; rfl
    rw [hlog_eq]
    exact mem_add (mem_mul (mem_ofInt _) mem_LN2) hcore

/-- Exact monotonicity-based logarithm on a positive interval (`0 < I.lo`). -/
def log (I : Interval) : Interval :=
  if 0 < I.lo ∧ I.lo ≤ I.hi then
    ⟨(logNat I.lo.toNat).lo, (logNat I.hi.toNat).hi⟩
  else ⟨0, 0⟩

lemma mem_log {I : Interval} {x : ℝ} (hx : mem I x) (hpos : 0 < I.lo) :
    mem (log I) (Real.log x) := by
  have hle : I.lo ≤ I.hi := by
    have h1 : (I.lo : ℝ) ≤ (I.hi : ℝ) := (div_le_div_iff_of_pos_right SCALE_pos).mp (le_trans hx.1 hx.2)
    exact_mod_cast h1
  unfold mem log at *
  simp only [hpos, hle, and_self, ↓reduceIte]
  have hlo_nat : 0 < I.lo.toNat := by omega
  have hhi_nat : 0 < I.hi.toNat := by omega
  have hlo_cast : (I.lo.toNat : ℝ) = (I.lo : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (le_of_lt hpos)
  have hhi_cast : (I.hi.toNat : ℝ) = (I.hi : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (le_of_lt (lt_of_lt_of_le hpos hle))
  have hL := mem_logNat hlo_nat
  have hR := mem_logNat hhi_nat
  rw [hlo_cast] at hL; rw [hhi_cast] at hR
  have hloR : (0 : ℝ) < (I.lo : ℝ) / SCALE := div_pos (by exact_mod_cast hpos) SCALE_pos
  have hx_pos : 0 < x := lt_of_lt_of_le hloR hx.1
  exact ⟨le_trans hL.1 (Real.log_le_log hloR hx.1), le_trans (Real.log_le_log hx_pos hx.2) hR.2⟩

/-! ### Exact Point-wise and Monotonicity-Exact Binary Entropy `h` -/

/-- Point enclosure of `h(a / SCALE)` for `0 ≤ a ≤ SCALE`. -/
def hPt (a : ℕ) : Interval :=
  if a = 0 ∨ a ≥ SCALE then ⟨0, 0⟩
  else
    let x := Interval.mk (a : ℤ) (a : ℤ)
    let x1 := Interval.mk ((SCALE - a : ℕ) : ℤ) ((SCALE - a : ℕ) : ℤ)
    add (neg (mul x (logNat a))) (neg (mul x1 (logNat (SCALE - a))))

lemma mem_hPt {a : ℕ} (ha : a ≤ SCALE) : mem (hPt a) (h ((a : ℝ) / (SCALE : ℝ))) := by
  unfold hPt
  by_cases h0 : a = 0
  · subst h0; simp [mem]
  by_cases h1 : a ≥ SCALE
  · have haeq : a = SCALE := le_antisymm ha h1
    subst haeq; simp [mem, div_self SCALE_ne_zero]
  · simp only [show ¬(a = 0 ∨ a ≥ SCALE) by tauto, ↓reduceIte]
    have ha_pos : 0 < a := Nat.pos_of_ne_zero h0
    have hma_pos : 0 < SCALE - a := by omega
    have hx_mem : mem ⟨(a : ℤ), (a : ℤ)⟩ ((a : ℝ) / SCALE) := ⟨le_rfl, le_rfl⟩
    have hx1_mem : mem ⟨((SCALE - a : ℕ) : ℤ), ((SCALE - a : ℕ) : ℤ)⟩ (1 - (a : ℝ) / SCALE) := by
      have heq : ((SCALE - a : ℕ) : ℝ) / SCALE = 1 - (a : ℝ) / SCALE := by
        rw [Nat.cast_sub ha, sub_div, div_self SCALE_ne_zero]
      unfold mem; rw [Int.cast_natCast, heq]; exact ⟨le_rfl, le_rfl⟩
    have hlog1 := mem_logNat ha_pos
    have hlog2 := mem_logNat hma_pos
    have heq2 : ((SCALE - a : ℕ) : ℝ) / SCALE = 1 - (a : ℝ) / SCALE := by
      rw [Nat.cast_sub ha, sub_div, div_self SCALE_ne_zero]
    rw [heq2] at hlog2
    have hres := mem_add (mem_neg (mem_mul hx_mem hlog1)) (mem_neg (mem_mul hx1_mem hlog2))
    unfold h
    convert hres using 1
    ring

lemma h_mono_left : MonotoneOn h (Set.Icc 0 (1 / 2)) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc 0 (1 / 2))
  · exact continuousOn_h.mono (Set.Icc_subset_Icc le_rfl (by norm_num))
  · intro x hx; rw [interior_Icc] at hx
    exact (hasDerivAt_h hx.1 (by linarith [hx.2])).differentiableAt.differentiableWithinAt
  · intro x hx; rw [interior_Icc] at hx
    rw [(hasDerivAt_h hx.1 (by linarith [hx.2])).deriv]
    unfold hp; apply Real.log_nonneg; rw [one_le_div hx.1]; linarith [hx.2]

lemma h_anti_right : AntitoneOn h (Set.Icc (1 / 2) 1) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc (1 / 2) 1)
  · exact continuousOn_h.mono (Set.Icc_subset_Icc (by norm_num) le_rfl)
  · intro x hx; rw [interior_Icc] at hx
    exact (hasDerivAt_h (by linarith [hx.1]) hx.2).differentiableAt.differentiableWithinAt
  · intro x hx; rw [interior_Icc] at hx
    rw [(hasDerivAt_h (by linarith [hx.1]) hx.2).deriv]
    unfold hp
    exact Real.log_nonpos (le_of_lt (div_pos (by linarith [hx.2]) (by linarith [hx.1])))
      ((div_le_one (by linarith [hx.1])).mpr (by linarith [hx.1]))

/-- Zero-wrapping monotonicity-exact enclosure of `h` on any subinterval of `[0, 1]`! -/
def hIv (I : Interval) : Interval :=
  let a := max 0 (min SCALE I.lo.toNat)
  let b := max 0 (min SCALE I.hi.toNat)
  let ha := hPt a
  let hb := hPt b
  let half := SCALE / 2
  let lo := min ha.lo hb.lo
  let hi :=
    if b ≤ half then hb.hi
    else if half ≤ a then ha.hi
    else LN2.hi
  ⟨lo, hi⟩

lemma mem_hIv {I : Interval} {x : ℝ} (hx : mem I x) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    mem (hIv I) (h x) := by
  have hS : (0 : ℝ) < (SCALE : ℝ) := SCALE_pos
  have hhalf_eq : ((SCALE / 2 : ℕ) : ℝ) / SCALE = 1 / 2 := by
    unfold SCALE; norm_num
  set a := max 0 (min SCALE I.lo.toNat)
  set b := max 0 (min SCALE I.hi.toNat)
  have ha_le : a ≤ SCALE := by omega
  have hb_le : b ≤ SCALE := by omega
  have hax : (a : ℝ) / SCALE ≤ x := by
    by_cases hlo : I.lo ≤ 0
    · have : I.lo.toNat = 0 := Int.toNat_eq_zero.mpr hlo
      have ha0 : a = 0 := by simp [a, this]
      rw [ha0]; simp [hx0]
    · have hlo_pos : 0 < I.lo := by omega
      have hlo_cast : (I.lo.toNat : ℝ) = (I.lo : ℝ) := by exact_mod_cast Int.toNat_of_nonneg (le_of_lt hlo_pos)
      have ha_le_lo : (a : ℝ) ≤ (I.lo : ℝ) := by
        rw [← hlo_cast]; exact_mod_cast (show a ≤ I.lo.toNat by omega)
      exact le_trans (div_le_div_of_nonneg_right ha_le_lo (le_of_lt hS)) hx.1
  have hxb : x ≤ (b : ℝ) / SCALE := by
    have hhi0 : 0 ≤ I.hi := by
      have h1 := mul_le_mul_of_nonneg_right (le_trans hx0 hx.2) (le_of_lt hS)
      rw [zero_mul, div_mul_cancel₀ _ SCALE_ne_zero] at h1
      exact_mod_cast h1
    have hhi_cast : (I.hi.toNat : ℝ) = (I.hi : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hhi0
    by_cases hhiS : SCALE ≤ I.hi.toNat
    · have hbS : b = SCALE := by omega
      rw [hbS, div_self SCALE_ne_zero]; exact hx1
    · have hb_eq : b = I.hi.toNat := by omega
      rw [hb_eq, hhi_cast]; exact hx.2
  have ha0 : (0 : ℝ) ≤ (a : ℝ) / SCALE := by positivity
  have ha1 : (a : ℝ) / SCALE ≤ 1 := (div_le_one hS).mpr (by exact_mod_cast ha_le)
  have hb0 : (0 : ℝ) ≤ (b : ℝ) / SCALE := by positivity
  have hb1 : (b : ℝ) / SCALE ≤ 1 := (div_le_one hS).mpr (by exact_mod_cast hb_le)
  have hha := mem_hPt ha_le
  have hhb := mem_hPt hb_le
  unfold mem hIv
  dsimp only
  constructor
  · -- Lower bound: by concavity of h, min(h(a/S), h(b/S)) ≤ h(x)!
    have hmin_le : min (h ((a : ℝ) / SCALE)) (h ((b : ℝ) / SCALE)) ≤ h x := by
      by_cases hab : (a : ℝ) / SCALE = (b : ℝ) / SCALE
      · have hxe : x = (a : ℝ) / SCALE := le_antisymm (by linarith) hax
        rw [hxe, hab, min_self]
      · have hab_lt : (a : ℝ) / SCALE < (b : ℝ) / SCALE := lt_of_le_of_ne (le_trans hax hxb) hab
        let t := (x - (a : ℝ) / SCALE) / ((b : ℝ) / SCALE - (a : ℝ) / SCALE)
        have ht0 : 0 ≤ t := div_nonneg (by linarith) (by linarith)
        have ht1 : t ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
        have hcomb := concaveOn_h.2 ⟨ha0, ha1⟩ ⟨hb0, hb1⟩ (show 0 ≤ 1 - t by linarith) ht0 (by ring)
        have hpt : (1 - t) • ((a : ℝ) / SCALE) + t • ((b : ℝ) / SCALE) = x := by
          simp only [smul_eq_mul, t]
          have hne : (b : ℝ) / SCALE - (a : ℝ) / SCALE ≠ 0 := ne_of_gt (sub_pos.mpr hab_lt)
          have hne2 : (b : ℝ) - (a : ℝ) ≠ 0 := by
            intro heq; apply hne; rw [← sub_div, heq, zero_div]
          field_simp [hne, hne2, SCALE_ne_zero]; ring
        rw [hpt, smul_eq_mul, smul_eq_mul] at hcomb
        have hma : min (h ((a : ℝ) / SCALE)) (h ((b : ℝ) / SCALE)) ≤ h ((a : ℝ) / SCALE) := min_le_left _ _
        have hmb : min (h ((a : ℝ) / SCALE)) (h ((b : ℝ) / SCALE)) ≤ h ((b : ℝ) / SCALE) := min_le_right _ _
        nlinarith
    have hlo_le : ((min (hPt a).lo (hPt b).lo : ℤ) : ℝ) / SCALE
        ≤ min (h ((a : ℝ) / SCALE)) (h ((b : ℝ) / SCALE)) := by
      rw [Int.cast_min, min_div_pos (le_of_lt hS)]
      exact min_le_min hha.1 hhb.1
    exact le_trans hlo_le hmin_le
  · -- Upper bound by monotonicity split at 1/2:
    split_ifs with h1 h2
    · have hb_half : (b : ℝ) / SCALE ≤ 1 / 2 := by
        rw [← hhalf_eq]; exact div_le_div_of_nonneg_right (by exact_mod_cast h1) (le_of_lt hS)
      exact le_trans (h_mono_left ⟨hx0, le_trans hxb hb_half⟩ ⟨hb0, hb_half⟩ hxb) hhb.2
    · have ha_half : 1 / 2 ≤ (a : ℝ) / SCALE := by
        rw [← hhalf_eq]; exact div_le_div_of_nonneg_right (by exact_mod_cast h2) (le_of_lt hS)
      exact le_trans (h_anti_right ⟨ha_half, ha1⟩ ⟨le_trans ha_half hax, hx1⟩ hax) hha.2
    · exact le_trans (h_le_L hx0 hx1) mem_LN2.2

end UCBound.Iv
