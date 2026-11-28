import EvenUnitFractions.Basic

namespace EvenUnitFractions

private theorem reciprocal_antitone {x y : Nat} (hx : 0 < x) (hxy : x ≤ y) :
    reciprocal y ≤ reciprocal x := by
  have px := Rat.natCast_pos.mpr hx
  have py := Rat.natCast_pos.mpr (by omega : 0 < y)
  apply Rat.le_of_mul_le_mul_right (c := (x : Rat)) _ px
  apply Rat.le_of_mul_le_mul_right (c := (y : Rat)) _ py
  have := Rat.natCast_le_natCast.mpr hxy
  grind [reciprocal]

private abbrev total (xs : List Nat) := (xs.map reciprocal).sum

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

private def blue (k d : Nat) : Prop := d = 1 ∨ d = 2 ∨ 3 * k ≤ d

private theorem split_blue (k : Nat) (hk : 0 < k) (xs : List Nat)
    (terms : ∀ d ∈ xs, blue k d) :
    ∃ (m : Nat) (r : Rat), 2 * total xs = (m : Rat) + r ∧
      0 ≤ r ∧ r ≤ (xs.length : Rat) * (2 * reciprocal (3 * k)) ∧
      (r = 0 → xs.length ≤ m) := by
  induction xs with
  | nil =>
    refine ⟨0, 0, by decide +kernel, by decide +kernel, by simp, fun _ => Nat.le_refl 0⟩
  | cons d ds ih =>
    obtain ⟨m, r, split, remainder_nonneg, bound, count⟩ := ih (fun x hx => terms x (.tail d hx))
    have h3k : 0 < 3 * k := by omega
    have h3k_pos : (0 : Rat) < ((3 * k : Nat) : Rat) := Rat.natCast_pos.mpr h3k
    have nonneg : 0 ≤ reciprocal (3 * k) := by
      have : (0 : Rat) < reciprocal (3 * k) := by
        rw [reciprocal, Rat.div_def, Rat.one_mul]
        exact Rat.inv_pos.mpr h3k_pos
      exact Rat.le_of_lt this
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
    · have term_bound := reciprocal_antitone h3k large
      have hd : 0 < d := by omega
      have term_pos : 0 < reciprocal d := by
        rw [reciprocal, Rat.div_def, Rat.one_mul]
        exact Rat.inv_pos.mpr (Rat.natCast_pos.mpr hd)
      exact ⟨m, r + 2 * reciprocal d, by grind⟩

private theorem blue_integer_sum {k : Nat} (hk : 0 < k) {xs : List Nat} {t : Nat}
    (length : xs.length = k) (terms : ∀ d ∈ xs, blue k d) (whole : 2 * total xs = (t : Rat)) :
    k ≤ t := by
  obtain ⟨m, r, split, nonneg, bound, count⟩ := split_blue k hk xs terms
  rw [length] at bound count
  have gap : (k : Rat) * (2 * reciprocal (3 * k)) < 1 := by
    have hk_pos : (0 : Rat) < (k : Rat) := Rat.natCast_pos.mpr hk
    have h3k_pos : (0 : Rat) < ((3 * k : Nat) : Rat) := Rat.natCast_pos.mpr (by omega)
    have hcast : ((3 * k : Nat) : Rat) = 3 * (k : Rat) := by
      rw [Rat.natCast_mul]; rfl
    have hne : ((3 * k : Nat) : Rat) ≠ 0 := fun h => by
      rw [h] at h3k_pos; exact Rat.lt_irrefl h3k_pos
    have hmul : reciprocal (3 * k) * ((3 * k : Nat) : Rat) = 1 := by
      rw [reciprocal, Rat.div_def, Rat.one_mul]
      exact Rat.inv_mul_cancel _ hne
    have hprod : (k : Rat) * (2 * reciprocal (3 * k)) * ((3 * k : Nat) : Rat) = 2 * (k : Rat) := by
      calc (k : Rat) * (2 * reciprocal (3 * k)) * ((3 * k : Nat) : Rat)
          = 2 * (k : Rat) * (reciprocal (3 * k) * ((3 * k : Nat) : Rat)) := by grind
        _ = 2 * (k : Rat) * 1 := by rw [hmul]
        _ = 2 * (k : Rat) := Rat.mul_one _
    apply Rat.lt_of_mul_lt_mul_right (c := ((3 * k : Nat) : Rat)) _ (Rat.le_of_lt h3k_pos)
    rw [hprod, Rat.one_mul, hcast]
    grind
  have lower : m ≤ t := Rat.natCast_le_natCast.mp (by grind)
  have upper : t < m + 1 := by
    apply Rat.natCast_lt_natCast.mp
    simp [Rat.natCast_add]
    grind
  have equal : t = m := by omega
  subst t
  have zero : r = 0 := by grind
  exact count zero

private def red (k n : Nat) := decide (3 ≤ n ∧ n ≤ 3 * k - 1)

/-- For every `k ≥ 3`, coloring `3` through `3k - 1` red and all other denominators
in `{1, ..., 3k² - 1}` blue avoids monochromatic solutions (Gaiser–Ramezanpour Theorem 1.1). -/
theorem lower {k : Nat} (hk : 3 ≤ k) : ¬ Forces k (3 * k * k - 1) := by
  intro force
  obtain ⟨y, xs, hy, _, length, terms, sum⟩ := force (red k)
  change total xs = reciprocal y at sum
  have target_bound (M : Nat) (pos : 0 < M) (bound : ∀ d ∈ xs, d ≤ M) : k * y ≤ M := by
    have minSum := sum_lower xs (reciprocal M) fun d hd =>
      reciprocal_antitone (terms d hd).1 (bound d hd)
    rw [length, sum] at minSum
    have factor := Rat.mul_pos (Rat.natCast_pos.mpr hy) (Rat.natCast_pos.mpr pos)
    have := Rat.mul_le_mul_of_nonneg_right minSum (Rat.le_of_lt factor)
    apply Rat.natCast_le_natCast.mp
    rw [Rat.natCast_mul]
    grind [reciprocal]
  have hMpos : 0 < 3 * k * k - 1 := by
    have : 3 * 3 * 3 ≤ 3 * k * k := Nat.mul_le_mul (Nat.mul_le_mul_left 3 hk) hk
    omega
  have endpoint := target_bound (3 * k * k - 1) hMpos fun d hd => (terms d hd).2.1
  by_cases is_red : 3 ≤ y ∧ y ≤ 3 * k - 1
  · have red_bound (d : Nat) (hd : d ∈ xs) : d ≤ 3 * k - 1 := by
      have same : 3 ≤ d ∧ d ≤ 3 * k - 1 := by simpa [red, is_red] using (terms d hd).2.2
      exact same.2
    have hbound := target_bound (3 * k - 1) (by omega) red_bound
    have : 3 * k ≤ k * y := by
      calc 3 * k = k * 3 := Nat.mul_comm 3 k
        _ ≤ k * y := Nat.mul_le_mul_left k is_red.1
    omega
  · have blue_terms (d : Nat) (hd : d ∈ xs) : blue k d := by
      obtain ⟨hp, hu, hc⟩ := terms d hd
      simp [red, is_red] at hc
      unfold blue
      omega
    have hy_lt : y < 3 * k := by
      cases Nat.lt_or_ge y (3 * k) with
      | inl hlt => exact hlt
      | inr hge =>
        have h2 : k * (3 * k) ≤ k * y := Nat.mul_le_mul_left k hge
        have h3 : k * (3 * k) = 3 * k * k := by
          rw [← Nat.mul_assoc, Nat.mul_comm k 3]
        omega
    have target : y = 1 ∨ y = 2 := by omega
    rcases target with rfl | rfl
    · have := blue_integer_sum (k := k) (by omega) (t := 2) length blue_terms (sum ▸ by decide +kernel)
      omega
    · have := blue_integer_sum (k := k) (by omega) (t := 1) length blue_terms (sum ▸ by decide +kernel)
      omega

end EvenUnitFractions
