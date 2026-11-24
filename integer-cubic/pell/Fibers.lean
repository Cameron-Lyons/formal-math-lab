module

public import Mathlib.Basic.Finite.Prod
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

public section

namespace SmallCubic

private theorem two_sub_cube_ne_zero (x : ℤ) : 2 - x ^ 3 ≠ 0 := by
  have mono : Monotone (fun x : ℤ => x ^ 3) := (show Odd 3 by decide).strictMono_pow.monotone
  rcases le_or_gt x 1 with hx | hx
  · have := mono hx
    norm_num at this
    omega
  · have := mono (show (2 : ℤ) ≤ x by omega)
    norm_num at this
    omega

private theorem mem_interval_of_natAbs_le {t : ℤ} {M : ℕ} (h : t.natAbs ≤ M) :
    t ∈ Set.Icc (-(M : ℤ)) (M : ℤ) := by
  have positiveSide := Int.le_natAbs (a := t)
  have negativeSide := Int.le_natAbs (a := -t)
  rw [Int.natAbs_neg] at negativeSide
  constructor <;> omega

/-- Bounding the first coordinate bounds both factors of 2 − x³, hence both remaining
coordinates. The set of triples in such a slice is finite. -/
theorem finite_bounded_x (B : ℕ) :
    {p : ℤ × ℤ × ℤ | p.1.natAbs ≤ B ∧
      p.2.2 ^ 2 + p.2.1 ^ 2 * p.2.2 + p.1 ^ 3 = 2}.Finite := by
  let M := 2 + B ^ 3
  refine ((Set.finite_Icc (-(B : ℤ)) (B : ℤ)).prod
    ((Set.finite_Icc (-((2 * M : ℕ) : ℤ)) ((2 * M : ℕ) : ℤ)).prod
      (Set.finite_Icc (-(M : ℤ)) (M : ℤ)))).subset ?_
  rintro ⟨x, y, z⟩ ⟨hx, h⟩
  change x.natAbs ≤ B at hx
  change z ^ 2 + y ^ 2 * z + x ^ 3 = 2 at h
  have factor : z * (z + y ^ 2) = 2 - x ^ 3 := by nlinarith only [h]
  have bound : (2 - x ^ 3).natAbs ≤ M := by
    calc
      _ ≤ (2 : ℤ).natAbs + (x ^ 3).natAbs := Int.natAbs_sub_le _ _
      _ = 2 + x.natAbs ^ 3 := by rw [Int.natAbs_pow]; rfl
      _ ≤ M := Nat.add_le_add_left (Nat.pow_le_pow_left hx 3) _
  have nz := two_sub_cube_ne_zero x
  have hz : z.natAbs ≤ M := (Int.natAbs_le_of_dvd_ne_zero
    (factor ▸ dvd_mul_right z (z + y ^ 2)) nz).trans bound
  have hw : (z + y ^ 2).natAbs ≤ M := (Int.natAbs_le_of_dvd_ne_zero
    (factor ▸ dvd_mul_left (z + y ^ 2) z) nz).trans bound
  have hy : y.natAbs ≤ 2 * M := by
    have hsum := Int.natAbs_sub_le (z + y ^ 2) z
    rw [add_sub_cancel_left, Int.natAbs_pow] at hsum
    have := Nat.le_pow (a := y.natAbs) (b := 2) (by decide)
    omega
  exact ⟨mem_interval_of_natAbs_le hx, mem_interval_of_natAbs_le hy,
    mem_interval_of_natAbs_le hz⟩

/-- Infinitude of the surface's integral points is equivalent to unbounded
absolute values of their first coordinates. -/
theorem infinite_iff_unbounded_x :
    {p : ℤ × ℤ × ℤ | p.2.2 ^ 2 + p.2.1 ^ 2 * p.2.2 + p.1 ^ 3 = 2}.Infinite ↔
      ∀ B : ℕ, ∃ x y z : ℤ, B < x.natAbs ∧ z ^ 2 + y ^ 2 * z + x ^ 3 = 2 := by
  constructor
  · intro hinf B
    by_contra! bounded
    apply hinf
    refine (finite_bounded_x B).subset ?_
    rintro ⟨x, y, z⟩ h
    exact ⟨le_of_not_gt (fun hgt => bounded x y z hgt h), h⟩
  · intro unbounded hfin
    obtain ⟨B, hB⟩ := (hfin.image (fun p : ℤ × ℤ × ℤ => p.1.natAbs)).bddAbove
    obtain ⟨x, y, z, hx, h⟩ := unbounded B
    exact hx.not_ge (hB (show x.natAbs ∈ _ from ⟨(x, y, z), h, rfl⟩))

end SmallCubic
