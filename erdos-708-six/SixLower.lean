import Erdos708Statement

namespace SixLower

def originals : Finset ℕ := {13*19, 13*23, 17*19, 17*23, 19*19, 19*23}
abbrev center : ℕ := 2*13*17*19^2*23
abbrev start := center - 218
abbrev window := Finset.Ico start (start + 437)
private abbrev target := ∏ a ∈ originals, a

/-- If each chosen site supplies a gcd at most C, k sites supply at most C^k. -/
private theorem gcd_bound (d C : ℕ) (hd : 0 < d) (B : Finset ℕ)
    (h : ∀ b ∈ B, d.gcd b ≤ C) : d.gcd (∏ b ∈ B, b) ≤ C ^ B.card := by
  induction B using Finset.induction_on with
  | empty => simp
  | insert b B hb ih =>
    rw [Finset.prod_insert hb, Finset.card_insert_of_notMem hb, pow_succ']
    apply (Nat.le_of_dvd (Nat.mul_pos (Nat.gcd_pos_of_pos_left _ hd)
      (Nat.gcd_pos_of_pos_left _ hd)) (Nat.gcd_mul_right_dvd_mul_gcd d b _)).trans
    exact Nat.mul_le_mul (h b (by simp)) (ih (fun a ha => h a (by simp [ha])))

-- A divisor that must still be paid off-center in each case.
private abbrev withoutCenter := 13*17*19^5*23^3
private abbrev afterCenter := 13*17*19^3*23^2

private theorem away : ∀ b ∈ window, b ≠ center →
    Nat.gcd withoutCenter b ≤ 23 ∧ Nat.gcd afterCenter b ≤ 23 := by
  set_option maxRecDepth 4096 in decide +kernel

theorem at_least_eight (B : Finset ℕ) (hB : B ⊆ window) (hpay : target ∣ ∏ b ∈ B, b) :
    8 ≤ B.card := by
  have demand (S : Finset ℕ) (d k : ℕ) (hlarge : 23^k < d)
      (h : ∀ b∈S, d.gcd b ≤ 23) (hd : d ∣ ∏ b∈S,b) : k < S.card := by
    by_contra! hs
    have H := (gcd_bound d 23 ((Nat.zero_le _).trans_lt hlarge) S h).trans
      (Nat.pow_le_pow_right (by decide) hs)
    rw [Nat.gcd_eq_left hd] at H
    omega
  by_cases hc : center ∈ B
  · have hprod : target ∣ (∏ b ∈ B.erase center,b) * center := by rwa [Finset.prod_erase_mul _ _ hc]
    have hr : afterCenter ∣ ∏ b ∈ B.erase center,b := by
      rw [show afterCenter = target / target.gcd center by decide]
      exact (Nat.div_dvd_iff_dvd_mul (Nat.gcd_dvd_left _ _) (by decide)).mpr
        (by simpa only [Nat.mul_comm] using Nat.dvd_mul_gcd_iff_dvd_mul.mpr hprod)
    have H := demand (B.erase center) afterCenter 6 (by decide)
      (fun b hb => (away b (hB (Finset.mem_of_mem_erase hb)) (Finset.ne_of_mem_erase hb)).2) hr
    have := Finset.card_erase_add_one hc
    omega
  · have H := demand B withoutCenter 7 (by decide)
      (fun b hb => (away b (hB hb) (fun he => hc (he ▸ hb))).1) (dvd_trans (by decide : withoutCenter ∣ target) hpay)
    omega

theorem eight_suffice_here :
    let B : Finset ℕ := {center,center+13,center+17,center+19,center+38,center+57,center+23,center+46}
    B ⊆ window ∧ B.card = 8 ∧ target ∣ ∏ b∈B,b := by decide

end SixLower

namespace Erdos708
theorem eight_le_of_hasCoveringSize_six {k : ℕ} (h : HasCoveringSize 6 k) : 8 ≤ k := by
  obtain ⟨B, hB, hc, hd⟩ := h SixLower.originals (by decide) (by decide) SixLower.start (by decide)
  rw [show SixLower.originals.sup id = 437 by decide] at hB
  exact (SixLower.at_least_eight B hB hd).trans hc
end Erdos708
