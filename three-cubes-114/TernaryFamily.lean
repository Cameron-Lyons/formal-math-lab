module

public import TernaryNorm
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.ModCases
import Mathlib.Tactic.Ring

@[expose] public section

namespace ThreeCubes114.TernaryNorm

/-- Dividing a cube minus 114 by 19 gives arbitrarily large positive
    root moduli outside the full norm family. -/
theorem unbounded_normalized_moduli (L : ℤ) : ∃ M : ℤ, L < M ∧ 0 < M ∧
    (∃ r : ℤ, M ∣ r^3-114) ∧ ∀ a b c : ℤ, |norm 114 a b c| ≠ M := by
  let n := max L 1
  let M := 19^2 * n^3 + 6
  have hn : 1 ≤ n := le_max_right ..
  have hgrow : n ≤ n^3 := le_self_pow₀ hn (by decide)
  have hM : n < M := by dsimp [M]; omega
  refine ⟨M, lt_of_le_of_lt (le_max_left ..) hM, by omega, ⟨-19*n, -19, by dsimp [M]; ring⟩, ?_⟩
  intro a b c he
  obtain ⟨r, hr⟩ := full_norm_cube_mod_19 a b c
  have h6 : r^3 % 19 = 6 := by rw [← hr.eq, he]; dsimp [M]; omega
  mod_cases h : r % 19 <;> rw [(h.pow 3).eq] at h6 <;> contradiction

/-- A one-parameter family with primitive coefficient vector `(1,b,1)`. -/
def familyB (t : ℤ) : ℤ := 4 + 324875*t

/-- Every member has cofactor content exactly five. -/
theorem family_content (t : ℤ) :
    content (1-114*familyB t) (114-familyB t) ((familyB t)^2-1) = 5 := by
  let b := familyB t
  have h : Int.gcd (1-114*b) (114-b) = 5 := by
    rw [show 1-114*b = -12995 + 114*(114-b) by ring, Int.gcd_add_mul_right_left,
        show 114-b = 110 + (25*t)*(-12995) by dsimp [b, familyB]; ring,
        Int.gcd_add_mul_right_right]
    decide
  unfold content
  rw [h]
  apply (Int.gcd_eq_left_iff_dvd (by decide : (0:ℤ) ≤ 5)).mpr
  unfold familyB
  ring_nf
  omega

/-- The two normalized signed quantities have fixed, invertible residue classes.
The combined modulus tends to infinity with nonnegative `t`. -/
theorem family_quotients (t : ℤ) :
    let N := norm 114 1 (familyB t) 1
    (N/25)%5 = 2 ∧ (N/5)%19 = 4 ∧ N/5 = 5*(N/25) ∧ (0 ≤ t → t < N/5) := by
  dsimp [norm, familyB]
  ring_nf
  refine ⟨by omega, by omega, by omega, ?_⟩
  intro ht
  have ht₂ := sq_nonneg t
  have ht₃ := pow_nonneg ht 3
  omega

/-- Neither sign of the combined modulus can be a cube modulo 19. -/
theorem family_noncubes (t r : ℤ) :
    let M := norm 114 1 (familyB t) 1 / 5
    r^3%19 ≠ M%19 ∧ r^3%19 ≠ (-M)%19 := by
  dsimp only
  have h := (family_quotients t).2.1
  have hp := cube_ne_four_mod_19 r
  have hm := cube_ne_four_mod_19 (-r)
  rw [show (-r)^3 = -(r^3) by ring] at hm
  omega

/-- Bezout coefficients give a root of the linear congruence in `rootRule`. -/
private theorem linear_class {k m b c : ℤ} (h : rootRule k m b c) :
    ∃ r : ℤ, m ∣ c*r-b := by
  obtain ⟨u,v,huv⟩ := Int.isCoprime_iff_gcd_eq_one.mpr h.1
  exact ⟨v*b, -u*b, by linear_combination b*huv⟩

/-- Every combined modulus in this family actually admits a cube root of 114. -/
theorem family_cube_root (t : ℤ) :
    ∃ r : ℤ, norm 114 1 (familyB t) 1 / 5 ∣ r^3-114 := by
  let b := familyB t
  let B := 114-b
  let C := b^2-1
  obtain ⟨d,hN,hg,hd⟩ := normalized_roots 114 1 b 1 (by simp [content])
    (1-114*b) B C (by ring) (by dsimp [B]; ring) (by dsimp [C])
    5 (family_content t).symm (by decide)
  have norms := family_quotients t
  change (norm 114 1 b 1 / 25)%5 = 2 ∧ _ at norms
  have hd5 : d%5 = 2 := by have := norms.1; omega
  have hm : norm 114 1 b 1 / 5 = 5*d := by omega
  obtain ⟨q,hq⟩ : (5:ℤ) ∣ 3*d-1 := Int.dvd_iff_emod_eq_zero.mpr (by omega)
  have hcop : Int.gcd 5 d = 1 := Int.isCoprime_iff_gcd_eq_one.mp
    ⟨-q,3,by linear_combination hq⟩
  obtain ⟨r₀,j,hj⟩ := linear_class hd
  let r := r₀+3*d*(b-r₀)
  refine ⟨r, ?_⟩
  change norm 114 1 b 1 / 5 ∣ r^3-114
  rw [hm]
  apply combined_root hg hd hcop
  · exact ⟨q*(b-r₀), by dsimp [r]; linear_combination (b-r₀)*hq⟩
  · exact ⟨j+3*(C/5)*(b-r₀), by dsimp [r]; linear_combination hj⟩

end ThreeCubes114.TernaryNorm
