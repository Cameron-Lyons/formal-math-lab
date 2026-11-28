module

public import ArctanPolynomial

public section

namespace Arxiv.«2607.05739»

/-- The tenth-power bound already exceeds one million at the first open index. -/
theorem million_lt_abs_of_five_le {n : ℕ} {m : ℤ}
    (hn : 5 ≤ n) (h : B n = A n * m) : 1000000 < |m| := by
  have hlt : 1000000 < m.natAbs := (show 1000000 < 5^10 by decide).trans_le
    ((Nat.pow_le_pow_left hn 10).trans (index_pow_ten_lt_natAbs hn h).le)
  simpa only [Int.natCast_natAbs] using (show (1000000 : ℤ) < m.natAbs by exact_mod_cast hlt)

/-- The four integral initial values exhaust the bounded value window. -/
theorem integer_value_of_abs_le_million {n : ℕ} {m : ℤ} (hm : |m| ≤ 1000000)
    (h : B n = A n * m) : m = -3 ∨ m = 0 ∨ m = 1 ∨ m = 4 := by
  have hn : n < 5 := by
    by_contra! h₅
    exact (million_lt_abs_of_five_le h₅ h).not_ge hm
  have hc : (coords n).2 = (coords n).1 * m := by simpa [coords_eq] using h
  interval_cases n <;> norm_num [coords] at hc <;> omega

theorem million_lt_abs_of_simple_prime {n p : ℕ} {m : ℤ} (hp : p.Prime) (hp17 : 17 < p)
    (hd : p ∣ normProduct n) (hs : ¬ p ^ 2 ∣ normProduct n)
    (h : B n = A n * m) : 1000000 < |m| := by
  by_contra! hsmall
  have hpd := prime_dvd_one_add_sq_of_integerValue hp hd hs h
  have hbound := Int.le_of_dvd (show 0 < 1 + m ^ 2 by positivity) hpd
  rcases integer_value_of_abs_le_million hsmall h with h | h | h | h <;> subst m <;>
    norm_num at hbound <;> omega

end Arxiv.«2607.05739»
