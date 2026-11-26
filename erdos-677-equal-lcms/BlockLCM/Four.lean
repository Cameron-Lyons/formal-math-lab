module

public import BlockLCM.Defect
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
public import Mathlib.NumberTheory.Zsqrtd.Basic
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic

@[expose] public section

/-!
# Length four

Call `n` the start of the block `n + 1, n + 2, n + 3, n + 4`. Two blocks with different
starts have the same LCM only for the starts `1` and `2`, that is, for the blocks
`2, 3, 4, 5` and `3, 4, 5, 6`, whose LCMs are both `60`. Those blocks overlap, so disjoint
blocks of length four never share an LCM.

A collision forces the later product to be three times the earlier one. With
`s = n² + 5n + 5` the product is `s² - 1`, so the two blocks give a solution of
`x² - 3y² = -2` in which `4x + 5` and `4y + 5` are both squares. The positive solutions
are `(1 + √3)(2 + √3)^k`. Residues modulo 3 and 13 leave `k ≡ 2 (mod 12)`, and a Jacobi
symbol excludes every such `k` except `2`, which is the pair of starts `(1, 2)`.
-/

namespace Erdos677
open Finset

/-- Product of the four entries in a block. -/
def fourBlockProduct (n : ℕ) := (n+1)*(n+2)*(n+3)*(n+4)

/-- Repeated factors in the product of four consecutive entries. -/
def fourDefect (n : ℕ) := Nat.gcd 2 (n+3) * Nat.gcd 6 (n+4)

theorem lcmInterval_four_mul_defect (n : ℕ) :
    lcmInterval n 4 * fourDefect n = fourBlockProduct n := by
  have h := lcmInterval_mul_gcd_product n 4
  simp only [prod_range_succ, prod_range_zero, Nat.one_mul, Nat.add_zero] at h
  change _ * (Nat.gcd 1 _ * Nat.gcd 1 _ * Nat.gcd 2 _ * Nat.gcd 6 _) = _ at h
  simpa only [fourDefect, fourBlockProduct, Nat.gcd_one_left, Nat.one_mul] using h

/-- The defect is 6 when the start is 2 modulo 3, and 2 otherwise. -/
theorem fourDefect_eq (n : ℕ) : fourDefect n = if n % 3 = 2 then 6 else 2 := by
  have common (d j : ℕ) (hd : d ∣ 6) : Nat.gcd d (n % 6 + j) = Nat.gcd d (n+j) := by
    simpa only [Nat.gcd_comm d] using (((Nat.mod_modEq n 6).of_dvd hd).add_right j).gcd_eq
  have h6 : fourDefect (n % 6) = fourDefect n := by
    simp only [fourDefect, common 2 3 (by decide), common 6 4 (by decide)]
  have hlt : n % 6 < 6 := Nat.mod_lt _ (by decide)
  have h3 : n % 3 = (n % 6) % 3 := by omega
  rw [← h6, h3]
  generalize n % 6 = r at hlt ⊢
  interval_cases r <;> decide

/-- The product strictly increases with the start, so a collision needs the defect to
rise from 2 to 6. The later product is then three times the earlier one. -/
theorem four_collision_product {n m : ℕ} (hnm : n < m)
    (heq : lcmInterval m 4 = lcmInterval n 4) :
    n % 3 ≠ 2 ∧ m % 3 = 2 ∧ fourBlockProduct m = 3 * fourBlockProduct n := by
  have hp : fourBlockProduct n < fourBlockProduct m := by
    unfold fourBlockProduct
    repeat first | apply Nat.mul_lt_mul_of_lt_of_lt | omega
  have hn := lcmInterval_four_mul_defect n
  have hm := lcmInterval_four_mul_defect m
  rw [fourDefect_eq] at hn hm
  rw [heq] at hm
  split_ifs at hn hm <;> omega

/-- Since `(n+1)(n+2)(n+3)(n+4) = (n² + 5n + 5)² - 1`, the two blocks solve
`x² - 3y² = -2`. -/
theorem four_collision_pell {n m : ℕ} (h : fourBlockProduct m = 3 * fourBlockProduct n) :
    ((m:ℤ)^2+5*m+5)^2 - 3*((n:ℤ)^2+5*n+5)^2 = -2 := by
  have h' : ((m:ℤ)+1)*(m+2)*(m+3)*(m+4) = 3*(((n:ℤ)+1)*(n+2)*(n+3)*(n+4)) := by
    unfold fourBlockProduct at h; exact_mod_cast h
  linear_combination h'

namespace Four

/-- The fundamental unit `2 + √3`. -/
abbrev α : ℤ√3 := ⟨2, 1⟩

/-- The smallest positive solution `1 + √3` of `x² - 3y² = -2`. -/
abbrev β : ℤ√3 := ⟨1, 1⟩

theorem mul_α (a b : ℤ) : (⟨a, b⟩ : ℤ√3) * α = ⟨2*a+3*b, a+2*b⟩ := by
  ext <;> simp <;> ring

/-- Coordinates of `β * α^k`. -/
def solution : ℕ → ℤ × ℤ
  | 0 => (1, 1)
  | k+1 => (2*(solution k).1 + 3*(solution k).2, (solution k).1 + 2*(solution k).2)

theorem solution_eq (k : ℕ) : β * α^k = ⟨(solution k).1, (solution k).2⟩ := by
  induction k with
  | zero => simp [solution]
  | succ k ih => rw [pow_succ, ← mul_assoc, ih, mul_α]; rfl

/-- Descent: dividing a positive solution with `y > 1` by `α` gives a smaller positive
solution, so every positive solution is `β * α^k`. -/
theorem pell_orbit : ∀ (N : ℕ) (x y : ℤ), y ≤ N → 0 < x → 0 < y → x^2 - 3*y^2 = -2 →
    ∃ k : ℕ, (⟨x, y⟩ : ℤ√3) = β * α^k := by
  intro N
  induction N with
  | zero => intro x y h1 h2 h3; omega
  | succ N ih =>
    intro x y hy hx hy0 h
    by_cases hy1 : y = 1
    · subst hy1
      have h0 : (x-1)*(x+1) = 0 := by linear_combination h
      have : x = 1 := by rcases mul_eq_zero.mp h0 with h|h <;> omega
      subst this
      exact ⟨0, by simp⟩
    · have hy2 : 2 ≤ y := by omega
      have hxy : y < x := by
        by_contra hc; push Not at hc
        nlinarith [mul_le_mul hc hc hx.le hy0.le]
      have hx2 : x < 2*y := by
        by_contra hc; push Not at hc
        nlinarith [mul_le_mul hc hc (by positivity : (0:ℤ) ≤ 2*y) hx.le]
      have h3 : 3*y < 2*x := by
        by_contra hc; push Not at hc
        nlinarith [mul_le_mul hc hc (by positivity : (0:ℤ) ≤ 2*x) (by positivity : (0:ℤ) ≤ 3*y),
          mul_le_mul hy2 hy2 (by norm_num) hy0.le]
      obtain ⟨k, hk⟩ := ih (2*x - 3*y) (2*y - x) (by push_cast at hy; omega) (by omega) (by omega)
        (by linear_combination h)
      refine ⟨k+1, ?_⟩
      rw [pow_succ, ← mul_assoc, ← hk, mul_α]
      ext <;> simp <;> ring

theorem α_pow_twelve : ((39:ℤ) : ℤ√3) ∣ α^12 - 1 := by
  refine ⟨⟨93600, 54040⟩, ?_⟩
  have h : α^12 = ⟨3650401, 2107560⟩ := by
    simp only [pow_succ, pow_zero, one_mul, mul_α]
    norm_num
  rw [h]
  ext <;> simp

/-- Modulo 39 the solutions repeat with period twelve. -/
theorem solution_period (q r : ℕ) : ((39:ℤ) : ℤ√3) ∣ β * α^(12*q + r) - β * α^r := by
  have h1 : ((39:ℤ) : ℤ√3) ∣ (α^12)^q - 1 := by
    simpa using α_pow_twelve.trans (sub_dvd_pow_sub_pow (α^12) 1 q)
  have : β * α^(12*q + r) - β * α^r = β * α^r * ((α^12)^q - 1) := by
    rw [pow_add, pow_mul]; ring
  rw [this]; exact Dvd.dvd.mul_left h1 _

theorem sq_mod_thirteen (z : ℤ) : z^2 % 13 ≠ 7 := by
  have h : z^2 % 13 = (z % 13)^2 % 13 := ((Int.mod_modEq z 13).pow 2).symm
  have h0 := Int.emod_nonneg z (show (13:ℤ) ≠ 0 by norm_num)
  have h1 := Int.emod_lt_of_pos z (show (0:ℤ) < 13 by norm_num)
  rw [h]
  generalize z % 13 = w at h0 h1 ⊢
  interval_cases w <;> decide

/-- The residues of `x` and `y` modulo 3 leave `k ≡ 2, 8 (mod 12)`. At `k ≡ 8` the number
`4x + 5` is `7` modulo 13, which is not a square. -/
theorem index_mod_twelve {k : ℕ} {x y z : ℤ} (hk : (⟨x,y⟩ : ℤ√3) = β * α^k)
    (hx : x % 3 = 1) (hy : y % 3 = 2) (hz : 4*x + 5 = z^2) : k % 12 = 2 := by
  have hper := solution_period (k / 12) (k % 12)
  rw [Nat.div_add_mod, ← hk, solution_eq, Zsqrtd.intCast_dvd] at hper
  have hlt : k % 12 < 12 := Nat.mod_lt _ (by decide)
  have h13 := sq_mod_thirteen z
  generalize k % 12 = r at hper hlt ⊢
  obtain ⟨h1, h2⟩ := hper
  simp only [Zsqrtd.re_sub, Zsqrtd.im_sub] at h1 h2
  interval_cases r <;> simp [solution] at h1 h2 ⊢ <;> omega

/-- Rational part of `α^(2^t)`. -/
def u : ℕ → ℕ
  | 0 => 2
  | t+1 => 2 * (u t)^2 - 1

/-- Coefficient of `√3` in `α^(2^t)`. -/
def w : ℕ → ℕ
  | 0 => 1
  | t+1 => 2 * u t * w t

theorem u_pos (t : ℕ) : 1 ≤ u t := by
  induction t with
  | zero => decide
  | succ t ih =>
    have : 1 ≤ (u t)^2 := Nat.one_le_pow _ _ ih
    simp only [u]; omega

theorem u_succ (t : ℕ) : ((u (t+1) : ℕ) : ℤ) = 2 * (u t : ℤ)^2 - 1 := by
  have : 1 ≤ (u t)^2 := Nat.one_le_pow _ _ (u_pos t)
  simp only [u]
  rw [Nat.cast_sub (by omega)]; push_cast; ring

theorem α_pow_two_pow (t : ℕ) :
    α^(2^t) = ⟨u t, w t⟩ ∧ ((u t : ℤ))^2 - 3*(w t : ℤ)^2 = 1 := by
  induction t with
  | zero => simp [u, w]
  | succ t ih =>
    obtain ⟨h1, h2⟩ := ih
    have hu := u_succ t
    have hw : ((w (t+1) : ℕ) : ℤ) = 2 * u t * w t := by simp [w]
    constructor
    · rw [pow_succ, pow_mul, h1, hu, hw, pow_two]
      ext
      · simp; linear_combination (-1 : ℤ) * h2
      · simp; ring
    · rw [hu, hw]; linear_combination 4 * (u t : ℤ)^2 * h2

theorem u_mod (t : ℕ) : u (t+1) % 156 = 7 ∨ u (t+1) % 156 = 97 := by
  induction t with
  | zero => left; decide
  | succ t ih =>
    right
    have h : u (t+1+1) = 2 * (u (t+1))^2 - 1 := rfl
    have hm : (2 * (u (t+1))^2) % 156 = 98 := by
      rcases ih with h|h <;> simp [Nat.mul_mod, Nat.pow_mod, h]
    have : 1 ≤ (u (t+1))^2 := Nat.one_le_pow _ _ (u_pos _)
    omega

/-- `α^(2N) + 1 = 2u·α^N` for `N = 2^t`, and `x + 1` divides `x^j + 1` for odd `j`. -/
theorem u_dvd (t j : ℕ) (hj : Odd j) : ((u t : ℤ) : ℤ√3) ∣ α^(2 * 2^t * j) + 1 := by
  obtain ⟨h1, h2⟩ := α_pow_two_pow t
  have hd : ((u t : ℤ) : ℤ√3) ∣ α^(2 * 2^t) + 1 := by
    refine ⟨⟨2 * u t, 2 * w t⟩, ?_⟩
    rw [mul_comm 2 (2^t), pow_mul, h1, pow_two]
    ext
    · simp; linear_combination (-1 : ℤ) * h2
    · simp; ring
  have := hj.add_dvd_pow_add_pow (α^(2 * 2^t)) 1
  rw [one_pow, ← pow_mul] at this
  exact hd.trans this

theorem jacobiSym_u (t : ℕ) : jacobiSym (-39) (u (t+1)) = -1 := by
  have hodd : Odd (u (t+1)) := by
    rcases u_mod t with h|h <;> exact Nat.odd_iff.mpr (by omega)
  rw [jacobiSym.mod_right _ hodd]
  change jacobiSym (-39) (u (t+1) % 156) = -1
  rcases u_mod t with h|h <;> rw [h] <;> norm_num

/-- For `k = 2 + 2·2^t·j` with `j` odd and `t ≥ 1`, the number `u t` divides `y + 11`,
so `4y + 5 ≡ -39`. That is not a square modulo `u t`. -/
theorem index_eq_two {k : ℕ} {x y z : ℤ} (hk : (⟨x,y⟩ : ℤ√3) = β * α^k)
    (hk12 : k % 12 = 2) (hz : 4*y + 5 = z^2) : k = 2 := by
  by_contra hk2
  obtain ⟨l, hl⟩ : ∃ l, k = 2 + 12 * l := ⟨k/12, by omega⟩
  have hl0 : l ≠ 0 := by omega
  obtain ⟨t, j, hj, htj⟩ := Nat.exists_eq_two_pow_mul_odd (show 6 * l ≠ 0 by omega)
  obtain ⟨t, rfl⟩ : ∃ t', t = t'+1 := by
    cases t with
    | zero => exfalso; obtain ⟨c, hc⟩ := hj; omega
    | succ t' => exact ⟨t', rfl⟩
  have hkk : k = 2 + 2 * 2^(t+1) * j := by rw [hl, mul_assoc 2, ← htj]; omega
  have hdiv := u_dvd (t+1) j hj
  have hb : β * α^2 = ⟨19, 11⟩ := by rw [solution_eq]; rfl
  have hsol : (⟨x,y⟩ : ℤ√3) + ⟨19,11⟩ = β * α^2 * (α^(2 * 2^(t+1) * j) + 1) := by
    rw [hk, hkk, pow_add, ← hb]; ring
  have h2 : ((u (t+1) : ℤ) : ℤ√3) ∣ ⟨x,y⟩ + ⟨19,11⟩ := hsol ▸ Dvd.dvd.mul_left hdiv _
  rw [Zsqrtd.intCast_dvd] at h2
  have h3 : (u (t+1) : ℤ) ∣ y + 11 := by simpa using h2.2
  have h4 : (u (t+1) : ℤ) ∣ z^2 + 39 := by
    have : z^2 + 39 = 4 * (y + 11) := by linarith
    rw [this]; exact Dvd.dvd.mul_left h3 4
  have hsq : IsSquare (((-39 : ℤ)) : ZMod (u (t+1))) := by
    refine ⟨(z : ZMod _), ?_⟩
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (z^2+39) (u (t+1))).mpr h4
    push_cast at this ⊢
    linear_combination (-1 : ZMod (u (t+1))) * this
  exact ZMod.nonsquare_of_jacobiSym_eq_neg_one (jacobiSym_u t) hsq

end Four

open Four in
/-- Two distinct length-four blocks have the same LCM precisely for the starts 1 and 2. -/
theorem four_collision_iff {n m : ℕ} (hlt : n < m) :
    lcmInterval m 4 = lcmInterval n 4 ↔ (n,m) = (1,2) := by
  constructor
  · intro heq
    obtain ⟨hn3, hm3, hP⟩ := four_collision_product hlt heq
    have hpell := four_collision_pell hP
    have hxm : ((m:ℤ)^2+5*m+5) % 3 = 1 := by
      obtain ⟨q, rfl⟩ : ∃ q, m = 3*q+2 := ⟨m/3, by omega⟩
      have : ((3*q+2 : ℕ) : ℤ)^2 + 5*((3*q+2 : ℕ):ℤ) + 5 = 3*(3*(q:ℤ)^2+9*q+6) + 1 := by
        push_cast; ring
      rw [this]; omega
    have hym : ((n:ℤ)^2+5*n+5) % 3 = 2 := by
      obtain ⟨q, rfl | rfl⟩ : ∃ q, n = 3*q ∨ n = 3*q+1 := ⟨n/3, by omega⟩
      · have : ((3*q : ℕ) : ℤ)^2 + 5*((3*q : ℕ):ℤ) + 5 = 3*(3*(q:ℤ)^2+5*q+1) + 2 := by
          push_cast; ring
        rw [this]; omega
      · have : ((3*q+1 : ℕ) : ℤ)^2 + 5*((3*q+1 : ℕ):ℤ) + 5 = 3*(3*(q:ℤ)^2+7*q+3) + 2 := by
          push_cast; ring
        rw [this]; omega
    obtain ⟨k, hk⟩ := pell_orbit (n^2+5*n+5) _ _ (by push_cast; exact le_rfl)
      (by positivity) (by positivity) hpell
    have hk12 := index_mod_twelve hk hxm hym (z := 2*(m:ℤ)+5) (by ring)
    obtain rfl := index_eq_two hk hk12 (z := 2*(n:ℤ)+5) (by ring)
    have hb : β * α^2 = ⟨19, 11⟩ := by rw [solution_eq]; rfl
    rw [hb] at hk
    have h19 : (m:ℤ)^2+5*m+5 = 19 := congrArg Zsqrtd.re hk
    have h11 : (n:ℤ)^2+5*n+5 = 11 := congrArg Zsqrtd.im hk
    have hn : (n:ℤ) = 1 := by nlinarith [sq_nonneg ((n:ℤ)-1), Int.natCast_nonneg n]
    have hm : (m:ℤ) = 2 := by nlinarith [sq_nonneg ((m:ℤ)-2), Int.natCast_nonneg m]
    obtain rfl : n = 1 := by exact_mod_cast hn
    obtain rfl : m = 2 := by exact_mod_cast hm
    rfl
  · intro h; cases h; decide

/-- Disjoint blocks of length four have different LCMs. -/
theorem erdos_677_four (m n : ℕ) (hm : m ≥ n + 4) :
    lcmInterval m 4 ≠ lcmInterval n 4 := by
  intro heq
  have h := (four_collision_iff (show n < m by omega)).mp heq
  simp only [Prod.mk.injEq] at h
  omega

end Erdos677
