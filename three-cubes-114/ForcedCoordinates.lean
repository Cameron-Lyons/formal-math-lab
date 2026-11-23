module

import Mathlib.Data.Nat.Sqrt
public import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Primality
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

@[expose] public section

namespace ThreeCubes114

/-- When p ≡ 2 mod 3 is prime, cubing permutes the residues modulo p. -/
private theorem cube_injective (p : ℕ) (hp : p.Prime) (hr : p % 3 = 2) :
    Function.Injective (fun t : ZMod p => t^3) := by
  let : Fact p.Prime := ⟨hp⟩
  let e := (2*p-1)/3
  have inv (t : ZMod p) : (t^3)^e = t := by
    have he : 3*e = p + (p-1) := by dsimp [e]; omega
    rw [← pow_mul, he, pow_add, ZMod.pow_card]
    by_cases ht : t = 0
    · simp [ht]
    · simp [ZMod.pow_card_sub_one_eq_one ht]
  intro u v heq
  exact (inv u).symm.trans ((congrArg (fun t : ZMod p => t^e) heq).trans (inv v))

/-- Any such prime divisor of 114-z³ is forced to divide the signed pair sum. -/
theorem forced_prime (p : ℕ) (hp : p.Prime) (hr : p % 3 = 2) (x y z : ℤ)
    (hs : x^3 + y^3 + z^3 = 114) (hd : (p : ℤ) ∣ 114-z^3) : (p : ℤ) ∣ x+y := by
  have id : x^3 - (-y)^3 = 114-z^3 := by linarith
  have hm := (ZMod.intCast_zmod_eq_zero_iff_dvd (x^3 - (-y)^3) p).mpr (id ▸ hd)
  push_cast at hm
  have hxy := cube_injective p hp hr (sub_eq_zero.mp hm)
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd (x+y) p).mp
  push_cast
  rw [hxy, neg_add_cancel]

/-- The size bound holds for either sign and every ordering of x,y,z. -/
theorem pair_sum_cube_bound (x y z : ℤ) (hs : x^3 + y^3 + z^3 = 114) :
    |x+y|^3 ≤ 4*|114-z^3| := by
  have hid : 4*(114-z^3) = (x+y)*((x+y)^2 + 3*(x-y)^2) := by
    rw [show 114-z^3 = x^3+y^3 by omega]
    ring
  have hr := congrArg (fun n : ℤ => |n|) hid
  simp only [abs_mul, abs_of_nonneg (by decide : (0:ℤ) ≤ 4),
    abs_of_nonneg (show 0 ≤ (x+y)^2 + 3*(x-y)^2 by positivity)] at hr
  rw [hr, pow_succ, sq_abs, mul_comm ((x+y)^2)]
  exact mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (x-y)]) (abs_nonneg _)

/-- A fixed coordinate is impossible at any height once its forced divisor
    is bigger than the exact cube bound. -/
theorem coordinate_excluded {p : ℕ} (hp : p.Prime) (hr : p % 3 = 2) {z : ℤ}
    (hd : (p : ℤ) ∣ 114-z^3) (hsize : 4*|114-z^3| < (p : ℤ)^3) (x y : ℤ) :
    x^3 + y^3 + z^3 ≠ 114 := by
  intro hs
  have ha : x+y ≠ 0 := by
    intro hzero
    have hz : z^3 = 114 := by grind
    by_cases hsmall : z ≤ 4
    · have : z^3 ≤ (4:ℤ)^3 := (Odd.strictMono_pow (by decide : Odd 3)).monotone hsmall
      omega
    · have : (5:ℤ)^3 ≤ z^3 := (Odd.strictMono_pow (by decide : Odd 3)).monotone (by omega)
      omega
  have hpabs : (p : ℤ) ≤ |x+y| :=
    Int.le_of_dvd (abs_pos.mpr ha) ((dvd_abs _ _).mpr (forced_prime p hp hr x y z hs hd))
  have h := pow_le_pow_left₀ (by positivity : 0 ≤ (p:ℤ)) hpabs 3
  linarith [pair_sum_cube_bound x y z hs]

/-- In particular the centered cube root of 114 modulo every prime p ≥ 11,
    p ≡ 2 (mod 3), is excluded as a coordinate. -/
theorem centered_root_excluded {p : ℕ} (hp : p.Prime) (hr : p % 3 = 2) (h11 : 11 ≤ p)
    {z : ℤ} (hd : (p : ℤ) ∣ 114-z^3) (hcenter : 2*|z| ≤ (p:ℤ)) (x y : ℤ) :
    x^3 + y^3 + z^3 ≠ 114 := by
  apply coordinate_excluded hp hr hd _ x y
  have h1 : |114-z^3| ≤ 114 + |z|^3 := by
    calc
      _ ≤ |(114:ℤ)| + |z^3| := abs_sub _ _
      _ = _ := by rw [abs_pow z 3, abs_of_nonneg (by decide : 0 ≤ (114:ℤ))]
  have h2 := pow_le_pow_left₀ (by positivity : 0 ≤ 2*|z|) hcenter 3
  have h3 := pow_le_pow_left₀ (by decide : 0 ≤ (11:ℤ)) (show (11:ℤ) ≤ p by omega) 3
  nlinarith

/-- A coordinate four above the published |z| bound, excluded for every x,y.
The Lucas witnesses let Lean verify primality without a primality oracle. -/
theorem exclude_example (x y : ℤ) : x^3 + y^3 + (10000000000000000004:ℤ)^3 ≠ 114 := by
  apply centered_root_excluded (p := 235074455284844477681) _ (by decide) (by decide)
      (by decide) (by decide)
  primality (cert := .witnesses [
    .lucas { root := 6, primeFactors := [2, 5, 7, 4079, 15641, 94219, 69833] },
    .lucas { root := 11, primeFactors := [2, 2039] },
    .lucas { root := 7, primeFactors := [2, 1019] },
    .lucas { root := 3, primeFactors := [2, 5, 17, 23] },
    .lucas { root := 3, primeFactors := [2, 3, 41, 383] },
    .lucas { root := 5, primeFactors := [2, 7, 29, 43] }])

/-- The possible residues of any one coordinate, using cubes modulo 9 and 7. -/
def localAllowed (z : ℤ) : Bool :=
  z % 3 == 2 && ([0, 1, 2, 4] : List ℤ).contains (z % 7)

theorem local_coordinate_pass {x y z : ℤ} (h : x^3+y^3+z^3=114) : localAllowed z = true := by
  have casts (m : ℕ) : (x : ZMod m)^3 + (y : ZMod m)^3 + (z : ZMod m)^3 = 114 := by
    exact_mod_cast congrArg (fun n : ℤ => (n : ZMod m)) h
  have nine : ∀ x y z : ZMod 9, x^3 + y^3 + z^3 = 114 → (z.val : ℤ) % 3 = 2 := by decide
  have seven : ∀ x y z : ZMod 7, x^3 + y^3 + z^3 = 114 →
      (z.val : ℤ) ∈ ([0,1,2,4] : List ℤ) := by decide
  have h9 := nine _ _ _ (casts 9)
  have h7 := seven _ _ _ (casts 7)
  rw [ZMod.val_intCast] at h9 h7
  have h3 : z % 3 = 2 := by omega
  simpa [localAllowed, h3, List.contains_iff_mem] using h7

/-- Enumerate products of sublists of a supplied prime factorization. -/
def factorDivisors : List ℕ → List ℕ
  | [] => [1]
  | p :: rest =>
    let ds := factorDivisors rest
    ds ++ ds.map (p * ·)

private theorem divisor_mem {factors : List ℕ} (hprime : ∀ p ∈ factors, Nat.Prime p)
    {d : ℕ} (hd : d ∣ factors.prod) : d ∈ factorDivisors factors := by
  induction factors generalizing d with
  | nil => simpa [factorDivisors] using Nat.dvd_one.mp hd
  | cons p rest ih =>
    have hp : p.Prime := hprime p (by simp)
    have hrest (q) (hq : q ∈ rest) := hprime q (by simp [hq])
    rw [List.prod_cons] at hd
    simp only [factorDivisors, List.mem_append, List.mem_map]
    by_cases hpd : p ∣ d
    · obtain ⟨b, rfl⟩ := hpd
      exact Or.inr ⟨b, ih hrest ((Nat.mul_dvd_mul_iff_left hp.pos).mp hd), rfl⟩
    · exact Or.inl (ih hrest (((hp.coprime_iff_not_dvd.mpr hpd).symm.dvd_mul_left).mp hd))

/-- Each candidate must have a nonnegative square discriminant. -/
def noPairForFactors (m : ℕ) (factors : List ℕ) : Bool :=
  (factorDivisors factors).all fun d =>
    let delta := 3*d*(4*m - d^3)
    d^3 > 4*m || delta.sqrt^2 != delta

theorem exclude_by_factors {z : ℤ} {factors : List ℕ}
    (hprime : ∀ p ∈ factors, Nat.Prime p) (hprod : factors.prod = (114-z^3).natAbs)
    (hcheck : noPairForFactors (114-z^3).natAbs factors = true) (x y : ℤ) :
    x^3+y^3+z^3 ≠ 114 := by
  intro hs
  let d := (x+y).natAbs
  let t := (x-y).natAbs
  let m := (114-z^3).natAbs
  have hfac : 114-z^3 = (x+y)*(x^2-x*y+y^2) := by linear_combination -hs
  have hd : d ∈ factorDivisors factors := by
    apply divisor_mem hprime
    rw [hprod]
    exact Int.natAbs_dvd_natAbs.mpr ⟨_, hfac⟩
  have hid : 4*(114-z^3) = (x+y)*((x+y)^2 + 3*(x-y)^2) := by rw [hfac]; ring
  have hab := congrArg (fun n : ℤ => |n|) hid
  simp only [abs_mul, abs_of_nonneg (by decide : 0 ≤ (4:ℤ)),
    abs_of_nonneg (show 0 ≤ (x+y)^2 + 3*(x-y)^2 by positivity)] at hab
  have hn : 4*m = d^3 + 3*d*t^2 := by
    zify
    simp only [m, d, t, Int.natCast_natAbs]
    rw [show |x+y|^3 = (x+y)^2*|x+y| by rw [pow_succ, sq_abs], sq_abs]
    linarith only [hab]
  have hh : 4*m - d^3 = 3*d*t^2 := by omega
  have delta : 3*d*(4*m-d^3) = (3*d*t)^2 := by rw [hh]; ring
  have hc := (List.all_eq_true.mp hcheck) d hd
  change (decide (d^3 > 4*m) || (3*d*(4*m-d^3)).sqrt^2 != 3*d*(4*m-d^3)) = true at hc
  have hle : ¬d^3 > 4*m := by omega
  simp [hle, delta, Nat.sqrt_eq'] at hc

end ThreeCubes114
