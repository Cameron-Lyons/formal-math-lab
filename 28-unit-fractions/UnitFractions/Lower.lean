import UnitFractions.Basic

namespace UnitFractions28

private theorem reciprocal_antitone {x y : Nat} (hx : 0 < x) (hxy : x ≤ y) :
    reciprocal y ≤ reciprocal x := by
  -- Multiply by both positive denominators. The inequality becomes x ≤ y.
  have px := Rat.natCast_pos.mpr hx
  have py := Rat.natCast_pos.mpr (by omega : 0 < y)
  apply Rat.le_of_mul_le_mul_right (c := (x : Rat)) _ px
  apply Rat.le_of_mul_le_mul_right (c := (y : Rat)) _ py
  have := Rat.natCast_le_natCast.mpr hxy
  grind [reciprocal]

private abbrev total (xs : List Nat) := (xs.map reciprocal).sum

/-- Adding a lower bound for each summand gives a lower bound for the sum. -/
private theorem sum_lower (xs : List Nat) (q : Rat) (bound : ∀ d ∈ xs, q ≤ reciprocal d) :
    (xs.length : Rat) * q ≤ total xs := by
  induction xs with
  | nil => simp [total]
  | cons d ds ih =>
    have := bound d (.head ds)
    have := ih (fun x hx => bound x (.tail d hx))
    simp only [total, List.length_cons, List.map_cons, List.sum_cons,
      Rat.natCast_add, Rat.natCast_ofNat] at *
    grind

private def blue (d : Nat) : Prop := d = 1 ∨ d = 2 ∨ 84 ≤ d

/-- Write twice the blue sum as `m + r`. A denominator 1 or 2 contributes 2 or 1
to the integer `m`. Every other denominator contributes at most `2/84` to `r`. -/
private theorem split_blue (xs : List Nat) (terms : ∀ d ∈ xs, blue d) :
    ∃ (m : Nat) (r : Rat), 2 * total xs = (m : Rat) + r ∧
      0 ≤ r ∧ r ≤ (xs.length : Rat) * (2 * reciprocal 84) ∧
      (r = 0 → xs.length ≤ m) := by
  induction xs with
  | nil => exact ⟨0, 0, by decide +kernel⟩
  | cons d ds ih =>
    obtain ⟨m, r, split, remainder_nonneg, bound, count⟩ := ih (fun x hx => terms x (.tail d hx))
    have nonneg : 0 ≤ reciprocal 84 := by decide +kernel
    simp only [total, List.length_cons, List.map_cons, List.sum_cons,
      Rat.natCast_add, Rat.natCast_ofNat] at *
    rcases terms d (.head ds) with rfl | rfl | large
    · have : reciprocal 1 = 1 := by decide +kernel
      refine ⟨m + 2, r, ?_⟩
      simp only [Rat.natCast_add, Rat.natCast_ofNat]
      grind
    · have : 2 * reciprocal 2 = 1 := by decide +kernel
      refine ⟨m + 1, r, ?_⟩
      simp only [Rat.natCast_add, Rat.natCast_ofNat]
      grind
    · have term_bound := reciprocal_antitone (by decide : 0 < 84) large
      have hd : 0 < d := by omega
      have term_pos : 0 < reciprocal d := by
        simp [reciprocal, Rat.div_def, Rat.inv_pos, Rat.natCast_pos, hd]
      exact ⟨m, r + 2 * reciprocal d, by grind⟩

/-- If a sum of 28 blue terms is an integer number of half-units, it has at least 28
half-units. Indeed, the contribution from large denominators must itself be an
integer after doubling, and it is at most 28 · 2/84 < 1. -/
private theorem blue_integer_sum {xs : List Nat} {k : Nat} (length : xs.length = 28)
    (terms : ∀ d ∈ xs, blue d) (whole : 2 * total xs = (k : Rat)) : 28 ≤ k := by
  obtain ⟨m, r, split, nonneg, bound, count⟩ := split_blue xs terms
  rw [length] at bound count
  have gap : 28 * (2 * reciprocal 84) < 1 := by decide +kernel
  have lower : m ≤ k := Rat.natCast_le_natCast.mp (by grind)
  have upper : k < m + 1 := by
    apply Rat.natCast_lt_natCast.mp
    simp [Rat.natCast_add]
    grind
  have equal : k = m := by omega
  subst k
  have zero : r = 0 := by grind
  exact count zero

private def red (n : Nat) := decide (3 ≤ n ∧ n ≤ 83)

/-- Color 3 through 83 red, and all other denominators blue. -/
theorem lower : ¬ Forces 2351 := by
  intro force
  obtain ⟨y, xs, hy, _, length, terms, sum⟩ := force red
  change total xs = reciprocal y at sum
  -- With every summand denominator at most M, we have 28/M ≤ 1/y.
  have target_bound (M : Nat) (pos : 0 < M) (bound : ∀ d ∈ xs, d ≤ M) : 28 * y ≤ M := by
    have minSum := sum_lower xs (reciprocal M) fun d hd =>
      reciprocal_antitone (terms d hd).1 (bound d hd)
    rw [length, sum] at minSum
    have factor := Rat.mul_pos (Rat.natCast_pos.mpr hy) (Rat.natCast_pos.mpr pos)
    have := Rat.mul_le_mul_of_nonneg_right minSum (Rat.le_of_lt factor)
    apply Rat.natCast_le_natCast.mp
    grind [reciprocal]
  have endpoint := target_bound 2351 (by decide) fun d hd => (terms d hd).2.1
  by_cases is_red : 3 ≤ y ∧ y ≤ 83
  · have red_bound (d : Nat) (hd : d ∈ xs) : d ≤ 83 := by
      have same : 3 ≤ d ∧ d ≤ 83 := by simpa [red, is_red] using (terms d hd).2.2
      exact same.2
    have := target_bound 83 (by decide) red_bound
    omega
  · have blue_terms (d : Nat) (hd : d ∈ xs) : blue d := by
      obtain ⟨hp, hu, hc⟩ := terms d hd
      simp [red, is_red] at hc
      unfold blue
      omega
    -- The only possible blue targets are 1 and 1/2.
    have target : y = 1 ∨ y = 2 := by omega
    rcases target with rfl | rfl
    · have := blue_integer_sum (k := 2) length blue_terms (sum ▸ by decide +kernel)
      omega
    · have := blue_integer_sum (k := 1) length blue_terms (sum ▸ by decide +kernel)
      omega

end UnitFractions28
