module

public import PrimePowers
public import Mathlib.Data.Finset.Max
public import Mathlib.Tactic.Ring

@[expose] public section

namespace Erdos677
open Finset

/-- Between two distinct multiples of a positive number `q`, endpoints included,
there is a multiple of `2 * q`. -/
private theorem double_multiple_between {q x y : ℕ}
    (hxy : x < y) (hx : q ∣ x) (hy : q ∣ y) :
    ∃ z, x ≤ z ∧ z ≤ y ∧ 2 * q ∣ z := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  have hab : a < b := lt_of_mul_lt_mul_left' hxy
  by_cases h : 2 ∣ a
  · obtain ⟨t, rfl⟩ := h
    exact ⟨_, le_rfl, hxy.le, t, by ring⟩
  · have he : 2 ∣ a + 1 := by omega
    obtain ⟨t, ht⟩ := he
    refine ⟨q * (a + 1), Nat.mul_le_mul_left _ (by omega),
      Nat.mul_le_mul_left _ (by omega), t, ?_⟩
    rw [ht]
    ring

/-- Every nonempty interval `(a,b]` has a unique entry attaining the largest
exponent of 2 in the interval. -/
theorem unique_highest_two_power {a b : ℕ} (hab : a < b) :
    ∃ w, a < w ∧ w ≤ b ∧ ∀ x, a < x → x ≤ b → x ≠ w →
      x.factorization 2 < w.factorization 2 := by
  let S := Ioc a b
  have hS : S.Nonempty := ⟨b, mem_Ioc.mpr ⟨hab, le_rfl⟩⟩
  obtain ⟨w, hw, hmax⟩ := exists_max_image S (fun x : ℕ => x.factorization 2) hS
  obtain ⟨haw, hwb⟩ := mem_Ioc.mp hw
  refine ⟨w, haw, hwb, ?_⟩
  intro x hax hxb hxw
  by_contra! hle
  let e := w.factorization 2
  have hdw : 2 ^ e ∣ w := (Nat.prime_two.pow_dvd_iff_le_factorization (by omega)).2 le_rfl
  have hdx : 2 ^ e ∣ x := (Nat.prime_two.pow_dvd_iff_le_factorization (by omega)).2 hle
  have hinter : ∃ z, a < z ∧ z ≤ b ∧ 2 * 2 ^ e ∣ z := by
    rcases lt_or_gt_of_ne hxw with h | h
    · obtain ⟨z, hxz, hzw, hd⟩ := double_multiple_between h hdx hdw
      exact ⟨z, hax.trans_le hxz, hzw.trans hwb, hd⟩
    · obtain ⟨z, hwz, hzx, hd⟩ := double_multiple_between h hdw hdx
      exact ⟨z, haw.trans_le hwz, hzx.trans hxb, hd⟩
  obtain ⟨z, haz, hzb, hd⟩ := hinter
  have hdz : 2 ^ (e + 1) ∣ z := by simpa [pow_succ, Nat.mul_comm] using hd
  have hlt := (Nat.prime_two.pow_dvd_iff_le_factorization (by omega)).1 hdz
  have hbound : z.factorization 2 ≤ e := hmax z (mem_Ioc.mpr ⟨haz, hzb⟩)
  omega

/-- Equal LCMs force the unique highest power of 2 in the entire span to occur
in the gap. The two blocks may have different positive lengths. -/
theorem highest_two_power_in_gap {n m k l : ℕ}
    (hk : 0 < k) (hl : 0 < l) (hdis : n + k ≤ m)
    (heq : lcmInterval m l = lcmInterval n k) :
    ∃ w, n + k < w ∧ w ≤ m ∧ ∀ x, n < x → x ≤ m + l → x ≠ w →
      x.factorization 2 < w.factorization 2 := by
  obtain ⟨w, hnw, hwb, hmax⟩ :=
    unique_highest_two_power (a := n) (b := m + l) (by omega)
  let e := w.factorization 2
  have hdw : 2 ^ e ∣ w := (Nat.prime_two.pow_dvd_iff_le_factorization (by omega)).2 le_rfl
  have uniq : ∀ x, n < x → x ≤ m + l → 2 ^ e ∣ x → x = w := by
    intro x hnx hxb hdx
    by_contra hx
    exact (not_le_of_gt (hmax x hnx hxb hx))
      ((Nat.prime_two.pow_dvd_iff_le_factorization (by omega)).1 hdx)
  have left_iff := primePower_dvd_interval (n := n) (e := e) Nat.prime_two hk
  have right_iff := primePower_dvd_interval (n := m) (e := e) Nat.prime_two hl
  rw [heq] at right_iff
  refine ⟨w, ?_, ?_, hmax⟩
  · by_contra! hleft
    obtain ⟨x, hmx, hxb, hdx⟩ := right_iff.mp (left_iff.mpr ⟨w, hnw, hleft, hdw⟩)
    have := uniq x (by omega) hxb hdx
    omega
  · by_contra! hright
    obtain ⟨x, hnx, hxk, hdx⟩ := left_iff.mp (right_iff.mpr ⟨w, hright, hwb, hdw⟩)
    have := uniq x hnx (by omega) hdx
    omega

/-- A collision forces the gap to contain a multiple of every power of 2 up to
the length of the combined span. -/
theorem gap_contains_two_power {n m k l e : ℕ}
    (hk : 0 < k) (hl : 0 < l) (hdis : n + k ≤ m)
    (heq : lcmInterval m l = lcmInterval n k) (hlen : n + 2 ^ e ≤ m + l) :
    ∃ w, n + k < w ∧ w ≤ m ∧ 2 ^ e ∣ w := by
  obtain ⟨w, hwk, hwm, hmax⟩ := highest_two_power_in_gap hk hl hdis heq
  have hq : 0 < 2 ^ e := pow_pos (by decide) e
  obtain ⟨x, hnx, hxu, hdx⟩ :=
    (contains_multiple_iff (n := n) (k := 2 ^ e) hq).mpr (by
      rw [Nat.add_div_right _ hq]
      omega)
  refine ⟨w, hwk, hwm, ?_⟩
  rcases eq_or_ne x w with rfl | hx
  · exact hdx
  · have hxexp := (Nat.prime_two.pow_dvd_iff_le_factorization (by omega)).1 hdx
    exact (Nat.prime_two.pow_dvd_iff_le_factorization (by omega)).2
      (hxexp.trans (hmax x hnx (hxu.trans hlen) hx).le)

/-- Two nonempty adjacent blocks of consecutive positive integers have different LCMs. -/
theorem adjacent_lcm_ne (n : ℕ) {k l : ℕ} (hk : 0 < k) (hl : 0 < l) :
    lcmInterval (n + k) l ≠ lcmInterval n k := by
  intro heq
  obtain ⟨w, hw, hw', _⟩ := highest_two_power_in_gap hk hl le_rfl heq
  omega

end Erdos677
