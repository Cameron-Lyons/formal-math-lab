import Std

/-! Search filters for the integer equation x³ + y³ + z³ = 114. -/

namespace ThreeCubes114

/-- Allowed values of `(x+y)/19 mod 19` when 19 divides the signed sum `x+y`. -/
def ramified19Residues : List Int := [2, 3, 8, 10, 12, 13, 14, 15, 18]

private def residue (m : Nat) (a : Int) (hm : 0 < m := by decide) : Fin m :=
  ⟨(a % (m : Int)).toNat, by
    have h := Int.emod_lt_of_pos a (show 0 < (m : Int) by omega)
    omega⟩

private theorem residue_val (m : Nat) (a : Int) (hm : 0 < m) :
    ((residue m a hm).val : Int) = a % (m : Int) := by
  simp only [residue]
  have h := Int.emod_nonneg a (show (m : Int) ≠ 0 by omega)
  omega

private theorem mul_congr {m a b c d : Int}
    (ha : a % m = c % m) (hb : b % m = d % m) : (a*b) % m = (c*d) % m := by
  rw [Int.mul_emod a b, Int.mul_emod c d, ha, hb]

private theorem pow_congr {m a b : Int} (h : a % m = b % m) (n : Nat) :
    a ^ n % m = b ^ n % m := by
  induction n with
  | zero => simp
  | succ n ih => simp only [Int.pow_succ]; exact mul_congr ih h

private theorem residue19_val (a : Int) : ((residue 19 a).val : Int) = a % 19 := by
  exact residue_val 19 a (by decide)

private theorem residue19_congr (a : Int) : a % 19 = ((residue 19 a).val : Int) % 19 := by
  simp [residue_val]

private theorem cube_sum_reduced (x y z m : Int) :
    ((x % m)^3 + (y % m)^3 + (z % m)^3) % m = (x^3 + y^3 + z^3) % m := by
  have cube (t : Int) : (t % m)^3 % m = t^3 % m := pow_congr (by simp) 3
  rw [Int.add_emod, Int.add_emod ((x%m)^3), cube, cube, cube]
  rw [← Int.add_emod (x^3) (y^3), ← Int.add_emod]

private theorem cube_zero_table : ∀ r : Fin 19, (r.val : Int)^3 % 19 = 0 → r.val = 0 := by
  decide

private theorem square_table : ∀ r : Fin 19,
    (r.val : Int) ∈ ramified19Residues ↔
    ∃ u : Fin 19, (3 * (r.val : Int) * (u.val : Int)^2) % 19 = 6 := by
  decide

/-- If the signed sum is `19*t`, the equation forces `3*t*x² ≡ 6 (mod 19)`.
This excludes ten of the nineteen classes of `t` before considering any `z`. -/
theorem ramified19_of_solution (x y z t : Int) (hs : x + y = 19*t)
    (h : x^3 + y^3 + z^3 = 114) : t % 19 ∈ ramified19Residues := by
  have hc : z^3 = 19*(6 - t*(x^2 - x*y + y^2)) := by grind
  have hz3 : z^3 % 19 = 0 := by rw [hc]; simp
  have hzr := cube_zero_table (residue 19 z) ((pow_congr (residue19_congr z) 3).symm.trans hz3)
  have hz : z % 19 = 0 := by rw [← residue19_val z, hzr]; rfl
  obtain ⟨w, hw⟩ := Int.dvd_of_emod_eq_zero hz
  have hy : y = 19*t - x := by omega
  have he : 19 * (3*t*x^2 + 19*(19*t^3 - 3*t^2*x + 19*w^3)) = 19*6 := by
    rw [hy, hw] at h
    grind
  have he' : 3*t*x^2 + 19*(19*t^3 - 3*t^2*x + 19*w^3) = 6 := by omega
  have hm := congrArg (fun n : Int => n % 19) he'
  simp only [Int.add_mul_emod_self_left] at hm
  have hr := mul_congr (mul_congr (a := 3) rfl (residue19_congr t))
    (pow_congr (residue19_congr x) 2)
  have ht := (square_table (residue 19 t)).mpr ⟨residue 19 x, hr.symm.trans hm⟩
  simpa only [residue19_val] using ht

/-- Each surviving class actually occurs modulo 361, even with `z = 0`.
Thus the table captures exactly the obstruction modulo 19² on this branch. -/
theorem ramified19_local_witness (t : Int) (h : t % 19 ∈ ramified19Residues) :
    ∃ x : Int, (x^3 + (19*t-x)^3) % 361 = 114 := by
  rw [← residue19_val t] at h
  obtain ⟨u, hu⟩ := (square_table (residue 19 t)).mp h
  let x : Int := u.val
  refine ⟨x, ?_⟩
  have hr := mul_congr (mul_congr (a := 3) rfl (residue19_congr t)) (b := x^2) rfl
  have hm : 3*t*x^2 % 19 = 6 := hr.trans hu
  have hi : x^3 + (19*t-x)^3 = 19*(3*t*x^2) + 361*(19*t^3 - 3*t^2*x) := by grind
  rw [hi, Int.add_mul_emod_self_left]
  omega

/-- A whole-divisor test. Its value depends only on the signed sum modulo 361. -/
def pass19 (s : Int) : Bool :=
  s % 19 != 0 || ramified19Residues.contains (s / 19 % 19)

theorem pass19_of_solution (x y z : Int) (h : x^3 + y^3 + z^3 = 114) : pass19 (x+y) = true := by
  by_cases hd : (x+y) % 19 = 0
  · have hs : x+y = 19*((x+y)/19) := by omega
    simpa [pass19, hd, List.contains_iff_mem] using ramified19_of_solution x y z _ hs h
  · simp [pass19, hd]

/-- For the signed pair sum `a`, write a candidate as `z = r + j*a`,
with `(k - r^3) / a = c`. Any divisor of `a` gives a square test on `j`. -/
theorem divisor_step_filter (k x y z a r j c p : Int)
    (hsol : x^3 + y^3 + z^3 = k) (ha : a = x + y) (hne : a ≠ 0)
    (hz : z = r + j*a) (hc : k - r^3 = a*c) (hp : p ∣ a) :
    p ∣ c - 3*r^2*j - 3*x^2 := by
  have hy : y = a - x := by omega
  have heq : c - 3*r^2*j - 3*x^2 = a * (a - 3*x + 3*r*j^2 + j^3*a) := by
    apply Int.eq_of_mul_eq_mul_left hne
    subst y z k
    grind
  obtain ⟨b, hb⟩ := hp
  exact ⟨b * (a - 3*x + 3*r*j^2 + j^3*a), by rw [heq, hb, Int.mul_assoc]⟩

private theorem scaled_squares_mod_five (x : Int) :
    (3*x^2) % 5 = 0 ∨ (3*x^2) % 5 = 2 ∨ (3*x^2) % 5 = 3 := by
  have red : (3*x^2) % 5 = (3*((x%5)*(x%5)%5))%5 := by
    rw [Int.mul_emod, Int.pow_succ, Int.pow_one, Int.mul_emod x x]
    rfl
  rw [red]
  have hr : x%5 = 0 ∨ x%5 = 1 ∨ x%5 = 2 ∨ x%5 = 3 ∨ x%5 = 4 := by omega
  rcases hr with h | h | h | h | h <;> simp [h]

/-- The division by `a` retains information at 5 even when `5 ∣ a`. -/
theorem five_step_filter (x y z a r j c : Int)
    (hsol : x^3 + y^3 + z^3 = 114) (ha : a = x + y) (hne : a ≠ 0)
    (hz : z = r + j*a) (hc : 114 - r^3 = a*c) (hp : 5 ∣ a) :
    (c - 3*r^2*j) % 5 = 0 ∨ (c - 3*r^2*j) % 5 = 2 ∨
    (c - 3*r^2*j) % 5 = 3 := by
  obtain ⟨b, hb⟩ := divisor_step_filter 114 x y z a r j c 5 hsol ha hne hz hc hp
  have h := scaled_squares_mod_five x
  omega

/-- For *any* signed pair sum 5 modulo 25, the root progression `z = 4 + 5*j`
loses classes 2 and 3 modulo 5, i.e. `z = 14, 19` modulo 25. -/
private theorem five_lift (x y j n : Int) (ha : x + y = 5 + 25*n)
    (hs : x^3 + y^3 + (4 + 5*j)^3 = 114) :
    j % 5 = 0 ∨ j % 5 = 1 ∨ j % 5 = 4 := by
  let u := 1 + 5*n
  have hy : y = 5*u - x := by dsimp [u]; omega
  -- Expand the two cubes about the pair sum, then divide the equation by 5.
  have h : 3*x^2 + 48*j = 5*(2 - 3*n*x^2 + 3*u^2*x - 5*u^3 - 12*j^2 - 5*j^3) := by
    subst y
    dsimp [u] at *
    grind
  have hsq := scaled_squares_mod_five x
  omega

/-- A signed pair sum of 5 modulo 25 restricts `z` to three classes modulo 25. -/
theorem five_example (x y z : Int) (ha : (x+y) % 25 = 5)
    (hs : x^3 + y^3 + z^3 = 114) :
    z % 25 = 4 ∨ z % 25 = 9 ∨ z % 25 = 24 := by
  let n := (x+y) / 25
  have hsum : x+y = 5+25*n := by dsimp [n]; omega
  have hcube : z^3 % 5 = 4 := by
    have h : z^3 - 114 = -5*((1 + 5*n)*(x^2-x*y+y^2)) := by grind
    omega
  have hred : (z^3) % 5 = ((z%5 * (z%5) %5) * (z%5)) % 5 := by
    rw [show z^3 = z*z*z by grind, Int.mul_emod (z*z) z 5, Int.mul_emod z z 5]
  rw [hred] at hcube
  have hz : z % 5 = 4 := by
    have hr : z%5 = 0 ∨ z%5 = 1 ∨ z%5 = 2 ∨ z%5 = 3 ∨ z%5 = 4 := by omega
    rcases hr with h | h | h | h | h <;> simp_all
  have hz' : 4 + 5*(z/5) = z := by omega
  have hj := five_lift x y (z/5) n hsum (by rw [hz']; exact hs)
  omega

/-- Rows use the signed pair sum modulo 32 and the remaining coordinate modulo 8. -/
def evenPairAllowed (a z : Int) : Bool :=
  match a % 32 with
  | 2  => z % 8 == 6
  | 10 => z % 8 == 0 || z % 8 == 4 || z % 8 == 6
  | 18 => z % 8 == 0 || z % 8 == 2 || z % 8 == 4
  | 26 => z % 8 == 2
  | _  => false

private theorem finite_even_pair :
    ∀ x y z : Fin 32,
      let a := (x.val : Int) + y.val
      a % 2 = 0 →
      ((x.val : Int)^3 + (y.val : Int)^3 + (z.val : Int)^3) % 32 = 114 % 32 →
      evenPairAllowed a z.val = true := by
  decide +kernel

/-- An even pair sum has only eight possible (sum mod 32, third coordinate mod 8)
    combinations. This holds for any ordering and for either sign of each integer. -/
theorem even_pair_sieve {x y z : Int} (h : x^3 + y^3 + z^3 = 114)
    (heven : (x + y) % 2 = 0) : evenPairAllowed (x + y) z = true := by
  have red := finite_even_pair (residue 32 x) (residue 32 y) (residue 32 z)
  have val32 (t : Int) : ((residue 32 t).val : Int) = t % 32 := residue_val 32 t (by decide)
  simp only [val32] at red
  have hred : ((x % 32)^3 + (y % 32)^3 + (z % 32)^3) % 32 = 114 % 32 := by
    rw [cube_sum_reduced, h]
  have htable := red (by omega) hred
  have ha : (x % 32 + y % 32) % 32 = (x + y) % 32 := (Int.add_emod ..).symm
  have hz : z % 32 % 8 = z % 8 := by omega
  simpa only [evenPairAllowed, ha, hz] using htable

private theorem mod27_table : ∀ x y z : Fin 27,
    ((x.val : Int)^3 + (y.val : Int)^3 + (z.val : Int)^3) % 27 = 114 % 27 →
    ((x.val : Int) + y.val) % 3 = 1 ∧ ((x.val : Int) + y.val + z.val) % 9 = 0 := by
  decide +kernel

/-- These congruences determine the sign of x+y from its magnitude and
    the residue of z modulo 18 from the signed sum. -/
theorem progression_congruences {x y z : Int} (h : x^3 + y^3 + z^3 = 114) :
    (x+y) % 3 = 1 ∧ (x+y+z) % 18 = 0 := by
  have h27 := mod27_table (residue 27 x) (residue 27 y) (residue 27 z)
  have val27 (t : Int) : ((residue 27 t).val : Int) = t % 27 := residue_val 27 t (by decide)
  simp only [val27, cube_sum_reduced, h, true_implies] at h27
  have parity (t : Int) : (t % 2)^3 = t % 2 := by
    have hr : t % 2 = 0 ∨ t % 2 = 1 := by omega
    rcases hr with hr | hr <;> simp [hr]
  have h2 := cube_sum_reduced x y z 2
  rw [parity, parity, parity, h] at h2
  omega

/-- Recover the pair from the signed sum, and check the original equation exactly. -/
def recoverPair (a z : Int) : Option (Int × Int) := do
  let numerator := 4 * (114 - z^3) - a^3
  let denominator := 3 * a
  guard (a != 0 && numerator % denominator == 0)
  let square := numerator / denominator
  guard (square >= 0)
  let diff : Int := square.toNat.sqrt
  guard (diff^2 == square && (a + diff) % 2 == 0)
  let x := (a + diff) / 2
  let y := a - x
  guard (x^3 + y^3 + z^3 == 114)
  return (x, y)

private theorem sqrt_product (n : Nat) : (n*n).sqrt = n := by
  have hlo := Nat.mul_self_le_mul_self_iff.mp (Nat.sqrt_le (n*n))
  have hhi := Nat.mul_self_lt_mul_self_iff.mp (Nat.lt_succ_sqrt (n*n))
  omega

/-- The exact candidate check recovers every solution in descending order of x and y. -/
theorem recoverPair_complete (x y z : Int) (h : x^3 + y^3 + z^3 = 114)
    (hne : x + y ≠ 0) (horder : y ≤ x) : recoverPair (x+y) z = some (x,y) := by
  have hid : 4 * (114 - z^3) - (x+y)^3 = (3*(x+y)) * (x-y)^2 := by grind
  have hden : 3 * (x+y) ≠ 0 := by omega
  have hdiff : x - y = ((x-y).toNat : Int) := by omega
  have hsquare : 0 ≤ (x-y)^2 := Int.pow_nonneg (by omega)
  have hsqrt : (((x-y)^2).toNat.sqrt : Int) = x-y := by
    let n := (x-y).toNat
    have hcast : x-y = (n : Int) := hdiff
    rw [hcast, Int.pow_succ, Int.pow_one, ← Int.natCast_mul, Int.toNat_natCast, sqrt_product]
  have hpar : (x + y + (x - y)) % 2 = 0 := by omega
  have hx : (x + y + (x - y)) / 2 = x := by omega
  have hy : x+y-x = y := by omega
  simp [guard, recoverPair, hid, hne, Int.mul_ediv_cancel_left _ hden, hsquare, hsqrt, hpar, hx, hy, h]

end ThreeCubes114
