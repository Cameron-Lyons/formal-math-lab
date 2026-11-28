module

public import BinomialBounds

@[expose] public section

namespace Erdos677
open Finset

/-- Every prime power in a common LCM divides a positive difference between
entries in the two intervals. These differences form a single interval. -/
theorem common_dvd_difference_interval {n m k : ℕ} (hk : 0 < k) (hd : n+k ≤ m)
    (heq : lcmInterval m k = lcmInterval n k) :
    lcmInterval m k ∣ lcmInterval (m-n-k) (2*k-1) := by
  apply (Nat.dvd_iff_prime_pow_dvd_dvd ..).mpr
  intro p e hp hq
  obtain ⟨x, hx, hx', hpx⟩ := (primePower_dvd_interval hp hk).mp hq
  obtain ⟨y, hy, hy', hpy⟩ := (primePower_dvd_interval hp hk).mp (heq ▸ hq)
  exact (primePower_dvd_interval hp (by omega)).mpr
    ⟨x-y, by omega, by omega, Nat.dvd_sub hpx hpy⟩

/-- A proposed collision with start difference at most D and endpoint at least b
must satisfy this numerical inequality, which involves neither start. -/
theorem binomial_obstruction {n m k b D : ℕ} (hk : 0 < k) (hd : n+k ≤ m)
    (heq : lcmInterval m k = lcmInterval n k) (hb : b ≤ m+k) (hD : m ≤ n+D) :
    k * b.choose k ≤ lcmInterval 0 (2*k-1) * (D+k-1).choose (2*k-1) := by
  let s := m - n - k
  let r := 2*k - 1
  have hdiv := (choose_mul_dvd_interval m k hk).trans
    ((common_dvd_difference_interval hk hd heq).trans (interval_dvd_lcm_mul_choose s r))
  have hpos : 0 < lcmInterval 0 r := Nat.pos_of_ne_zero <|
    Finset.lcm_ne_zero_iff.mpr fun x h => (mem_Ioc.mp h).1.ne'
  calc k * b.choose k ≤ k * (m+k).choose k := Nat.mul_le_mul_left _ (Nat.choose_le_choose _ hb)
    _ ≤ lcmInterval 0 r * (s+r).choose r :=
      Nat.le_of_dvd (Nat.mul_pos hpos (Nat.choose_pos (by omega))) hdiv
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.choose_le_choose _ (by dsimp [s,r]; omega))

-- Move along Pascal's triangle using exact divisions. The checker carries the
-- two binomial coefficients and the LCM forward so they are computed only once.
def alongRow (n r a : ℕ) := a * (n-r) / (r+1)
def alongDiagonal (n r a : ℕ) := (n+1) * a / (r+1)

private theorem alongRow_choose (n r : ℕ) : alongRow n r (n.choose r) = n.choose (r+1) := by
  simp [alongRow, ← Nat.choose_succ_right_eq]

private theorem alongDiagonal_choose (n r : ℕ) :
    alongDiagonal n r (n.choose r) = (n+1).choose (r+1) := by
  simp [alongDiagonal, Nat.add_one_mul_choose_eq]

def checkBounds (b D : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ → Bool
  | 0, _, _, _, _ => true
  | fuel+1, k, a, c, u =>
    decide (u * c < k * a) &&
      checkBounds b D fuel (k+1) (alongRow b k a)
        (alongRow (D+k) (2*k) (alongDiagonal (D+k-1) (2*k-1) c))
        ((u.lcm (2*k)).lcm (2*k+1))

private theorem checkBounds_sound (b D fuel k : ℕ) (hk : 0 < k)
    (checked : checkBounds b D fuel k (b.choose k) ((D+k-1).choose (2*k-1))
      (lcmInterval 0 (2*k-1)) = true) {j : ℕ} (hj : k ≤ j) (hstop : j < k+fuel) :
    lcmInterval 0 (2*j-1) * (D+j-1).choose (2*j-1) < j * b.choose j := by
  induction fuel generalizing k with
  | zero => omega
  | succ fuel ih =>
    obtain ⟨here, tail⟩ := Bool.and_eq_true_iff.mp checked
    rcases eq_or_lt_of_le hj with rfl | hlt
    · exact of_decide_eq_true here
    apply ih (k+1) (by omega) _ (by omega) (by omega)
    have h₁ : D+k-1+1 = D+k := by omega
    have h₂ : 2*k-1+1 = 2*k := by omega
    have h₃ : 2*(k+1)-1 = 2*k+1 := by omega
    have h₄ : D+(k+1)-1 = D+k := by omega
    have hU : (lcmInterval 0 (2*k-1)).lcm (2*k) = lcmInterval 0 (2*k) := by
      simpa only [Nat.zero_add, h₂] using (lcmInterval_extend 0 (2*k-1)).symm
    simpa only [alongRow_choose, alongDiagonal_choose, h₁, h₂, h₃, h₄, hU,
      lcmInterval_extend 0 (2*k), Nat.zero_add] using tail

/-- A successful numerical check turns a bound on the shift into a bound on
the endpoint. The starts themselves may be arbitrarily large. -/
theorem endpoint_le_of_bounds_check {n m k limit D : ℕ} (hk : 0 < k) (hd : n+k ≤ m)
    (hD : m ≤ n+D) (heq : lcmInterval m k = lcmInterval n k)
    (hcheck : checkBounds (limit+1) D D 1 (limit+1) D 1 = true) : m+k ≤ limit := by
  by_contra! h
  have calc_ne := checkBounds_sound (limit+1) D D 1 (by decide)
    (by simpa [lcmInterval] using hcheck) (show 1 ≤ k by omega)
    (show k < 1+D by omega)
  exact (not_le_of_gt calc_ne) (binomial_obstruction hk hd heq (by omega) hD)

/-- Every collision with shift at most 7,000 would appear in the
finite search through endpoint 10,000,000. -/
theorem endpoint_le_of_shift_le_7000 {n m k : ℕ} (hk : 0 < k) (hd : n+k ≤ m)
    (hD : m ≤ n+7000) (heq : lcmInterval m k = lcmInterval n k) : m+k ≤ 10000000 := by
  apply endpoint_le_of_bounds_check hk hd hD heq
  set_option maxRecDepth 100000 in
  set_option maxHeartbeats 0 in
  decide +kernel

end Erdos677
