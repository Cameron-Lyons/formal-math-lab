module

public import ArctanBridge
public import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.BigOperators.Associated

public section

namespace Arxiv.«2607.05739»

/-- The squared norm of the Gaussian product, written as a product in ℕ. -/
@[expose] def normProduct (n : ℕ) := ∏ k ∈ Finset.Icc 1 n, (1 + k ^ 2)

private theorem normProduct_eq (n : ℕ) :
    (normProduct n : ℤ) = A n ^ 2 + B n ^ 2 := by
  suffices h : (normProduct n : ℤ) = (coords n).1 ^ 2 + (coords n).2 ^ 2 by
    simpa [coords_eq] using h
  induction n with
  | zero => simp [normProduct, coords]
  | succ n ih =>
    rw [show normProduct (n+1) = normProduct n * (1 + (n+1)^2) from
      Finset.prod_Icc_succ_top (Nat.succ_le_succ (Nat.zero_le n)) _]
    push_cast
    rw [ih, coords]
    push_cast
    ring

/-- Any prime occurring just once in the norm product must divide 1 + m²
for an integer value m. -/
theorem prime_dvd_one_add_sq_of_integerValue {n p : ℕ} {m : ℤ}
    (hp : p.Prime) (hd : p ∣ normProduct n) (hs : ¬ p ^ 2 ∣ normProduct n)
    (h : B n = A n * m) : (p : ℤ) ∣ 1 + m ^ 2 := by
  have hn : (normProduct n : ℤ) = A n ^ 2 * (1 + m ^ 2) := by
    rw [normProduct_eq, h]; ring
  have hd' : (p : ℤ) ∣ (normProduct n : ℤ) := by exact_mod_cast hd
  rw [hn] at hd'
  have hp' := Nat.prime_iff_prime_int.mp hp
  refine (hp'.dvd_mul.mp hd').resolve_left ?_
  intro hpa
  have hsq : (p : ℤ) ^ 2 ∣ (normProduct n : ℤ) := by
    rw [hn]
    exact dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd (hp'.dvd_of_dvd_pow hpa) 2) _
  apply hs
  exact_mod_cast hsq

/-- The two roots of -1 modulo p are k and -k. Until the second root is
reached, the product with the kth term removed is coprime to p. -/
private theorem prime_not_dvd_erase {p k n : ℕ} (hp : p.Prime) (hk : p ∣ 1 + k ^ 2)
    (hkn : k ≤ n) (hn : n + k < p) :
    ¬ p ∣ ∏ j ∈ (Finset.Icc 1 n).erase k, (1 + j ^ 2) := by
  let _ : Fact p.Prime := ⟨hp⟩
  have hkroot := (ZMod.natCast_eq_zero_iff _ _).mpr hk
  push_cast at hkroot
  intro hd
  obtain ⟨j, hj, hdiv⟩ := (hp.prime.dvd_finsetProd_iff _).mp hd
  obtain ⟨hjk, hjmem⟩ := Finset.mem_erase.mp hj
  obtain ⟨hjpos, hjn⟩ := Finset.mem_Icc.mp hjmem
  have hz := (ZMod.natCast_eq_zero_iff _ _).mpr hdiv
  push_cast at hz
  have he : (j : ZMod p) ^ 2 = (k : ZMod p) ^ 2 := by linear_combination hz - hkroot
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp he with he | he
  · apply hjk
    simpa [Nat.mod_eq_of_lt (show j < p by omega), Nat.mod_eq_of_lt (show k < p by omega)] using
      (ZMod.natCast_eq_natCast_iff' j k p).mp he
  · have hsum : ((j + k : ℕ) : ZMod p) = 0 := by simp [he]
    have hd := (ZMod.natCast_eq_zero_iff _ _).mp hsum
    have := Nat.le_of_dvd (by omega) hd
    omega

/-- A prime larger than twice the index can occur only once in the norm. -/
theorem not_sq_dvd_normProduct_of_large_prime {p n : ℕ} (hp : p.Prime) (hlarge : 2*n < p)
    (hd : p ∣ normProduct n) : ¬ p ^ 2 ∣ normProduct n := by
  obtain ⟨k, hmem, hk⟩ := (hp.prime.dvd_finsetProd_iff _).mp hd
  obtain ⟨hkpos, hkn⟩ := Finset.mem_Icc.mp hmem
  have hrest := prime_not_dvd_erase hp hk hkn (by omega)
  have hlt : 1 + k ^ 2 < p ^ 2 := calc
    1 + k ^ 2 < (k + 1) ^ 2 := by nlinarith
    _ ≤ p ^ 2 := Nat.pow_le_pow_left (by omega) 2
  obtain ⟨c, hc⟩ := hk
  intro hs
  unfold normProduct at hs
  rw [← Finset.mul_prod_erase _ _ hmem, hc, pow_two, Nat.mul_assoc,
    Nat.mul_dvd_mul_iff_left hp.pos] at hs
  have hdvc := (hp.dvd_mul.mp hs).resolve_right hrest
  have hdouble : p ^ 2 ∣ 1 + k ^ 2 := by rw [hc, pow_two]; exact Nat.mul_dvd_mul_left p hdvc
  exact (Nat.not_le_of_lt hlt) (Nat.le_of_dvd (by positivity) hdouble)

theorem twice_index_le_sq_of_large_prime {n p : ℕ} {m : ℤ}
    (hp : p.Prime) (hlarge : 2 * n < p) (hd : p ∣ normProduct n)
    (h : B n = A n * m) : 2 * (n : ℤ) ≤ m ^ 2 := by
  have hpd := prime_dvd_one_add_sq_of_integerValue hp hd
    (not_sq_dvd_normProduct_of_large_prime hp hlarge hd) h
  have := Int.le_of_dvd (show 0 < 1 + m ^ 2 by positivity) hpd
  omega

/-- If k² + 1 is prime, that prime occurs once from index k until the next
root of -1 modulo p, at index p - k. -/
theorem prime_once_on_interval {p k n : ℕ} (hp : p.Prime) (hk : k ^ 2 + 1 = p)
    (hkn : k ≤ n) (hn : n < p - k) : p ∣ normProduct n ∧ ¬ p ^ 2 ∣ normProduct n := by
  have hkpos : 0 < k := by
    by_contra! h
    obtain rfl : k = 0 := by omega
    have := hp.two_le
    norm_num at hk
    omega
  have hmem : k ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr ⟨hkpos, hkn⟩
  have hk' : 1 + k ^ 2 = p := by omega
  have hrest := prime_not_dvd_erase hp (hk' ▸ dvd_refl p) hkn (by omega)
  unfold normProduct
  rw [← Finset.mul_prod_erase _ _ hmem, hk', pow_two, Nat.mul_dvd_mul_iff_left hp.pos]
  exact ⟨dvd_mul_right _ _, hrest⟩

end Arxiv.«2607.05739»
