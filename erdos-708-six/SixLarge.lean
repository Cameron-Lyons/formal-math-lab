import SixGroups
import PriorBounds
import Exceptions

namespace IntervalSix
open Erdos708Slots

/-- If two large primes occur, they either have a group of size one or two,
or partition the six originals into two triples. Both alternatives fit eight sites. -/
private theorem twoPrimes {L M p q : ℕ} (A : Finset ℕ) (hc : A.card = 6)
    (ha : ∀ a ∈ A, 2 ≤ a ∧ a ≤ M) (hM : 70 ≤ M)
    (hp : p.Prime) (hpM : M < 8*p) (hnp : (A.filter (p ∣ ·)).Nonempty)
    (hq : q.Prime) (hqM : M < 8*q) (hnq : (A.filter (q ∣ ·)).Nonempty) (hne : p ≠ q) :
    Cover L M 8 (∏ a ∈ A, a) := by
  classical
  let P := A.filter (p ∣ ·)
  let Q := A.filter (q ∣ ·)
  by_cases hP : P.card ≤ 2
  · exact rarePrimeCover A hc ha hp (by omega) hpM hnp hP
  by_cases hQ : Q.card ≤ 2
  · exact rarePrimeCover A hc ha hq (by omega) hqM hnq hQ
  have hsub : Q ⊆ A \ P := by
    intro a hh
    obtain ⟨hm,hqa⟩ := Finset.mem_filter.mp hh
    refine Finset.mem_sdiff.mpr ⟨hm, fun hh' => ?_⟩
    have hdiv := ((Nat.coprime_primes hp hq).mpr hne).mul_dvd_of_dvd_of_dvd
      (Finset.mem_filter.mp hh').2 hqa
    obtain ⟨h2,hb⟩ := ha a hm
    have := Nat.le_of_dvd (by omega : 0 < a) hdiv
    have := Nat.mul_le_mul_left p (by omega : 8 ≤ q)
    omega
  have hcount := Finset.card_sdiff_of_subset (show P ⊆ A from Finset.filter_subset ..)
  have hd := Finset.card_le_card hsub
  have heq : Q = A \ P := Finset.eq_of_subset_of_card_le hsub (by omega)
  have other := groupSmall (L:=L) Q hq (groupBounds ha hqM) (by omega)
  rw [show Q.card = 3 by omega, heq] at other
  exact groupJoin A ha hp (by omega) hpM (by omega : P.card≤3)
    (by omega : P.card+3≤8) (by omega : 2*P.card+3≤9) other

/-- The exceptional modulus divides 375. The other cofactors are distinct in
{1,…,7}, so their product divides 7! and the missing gcd divides 15. -/
private theorem outlier {L M p e : ℕ} (A : Finset ℕ) (hc : A.card = 6)
    (ha : ∀ a ∈ A, 2 ≤ a ∧ a ≤ M) (hM : 70 ≤ M) (hp : p.Prime) (hpM : M < 8*p)
    (he : e ∈ A) (h375 : e ∣ 375) (hne : ¬p ∣ e) (hr : ∀ a ∈ A.erase e, p ∣ a) :
    Cover L M 8 (∏ a ∈ A,a) := by
  let S := A.erase e
  have hS (a : ℕ) (h : a ∈ S) := ha a (Finset.mem_of_mem_erase h)
  obtain ⟨_,hprod,hcof⟩ := fiberData S hp (fun a h =>
    ⟨by have := (hS a h).1; omega,(hS a h).2,hr a h,smallQuotient (hS a h).2 hpM⟩)
  have hdiv : (∏ c ∈ cofactors S p, c) ∣ 5040 :=
    Finset.prod_dvd_prod_of_subset _ (Finset.Icc 1 7) id fun c h => by
      obtain ⟨h1,h2⟩ := Finset.mem_Icc.mp (hcof h)
      exact Finset.mem_Icc.mpr ⟨h1,h2.trans (min_le_left ..)⟩
  have gone : Cover L M 1 e := by
    obtain ⟨b,hb,_,hd⟩ := fresh_multiple L M 0 e ∅ (by simp)
      (by have := (ha e he).1; omega) (by simpa using (ha e he).2)
    exact ⟨{b}, Finset.singleton_subset_iff.mpr hb, by simp, by simpa using hd⟩
  rw [← A.prod_erase_mul (fun a => a) he]
  apply overlapRepair (fiveCover S (by simp [S,Finset.card_erase_of_mem he,hc]) hS)
    gone [3,5] (by decide) (by decide) (by simp; omega)
  change Nat.gcd (∏ a∈S,a) e ∣ 15
  rw [hprod, ((hp.coprime_iff_not_dvd.mpr hne).pow_left _).gcd_mul_left_cancel]
  exact (Nat.gcd_dvd_gcd_of_dvd_left e hdiv).trans (Nat.gcd_dvd_gcd_of_dvd_right 5040 h375)

theorem six_large {L M : ℕ} (A : Finset ℕ) (hc : A.card=6)
    (ha : ∀ a ∈ A, 2≤a ∧ a≤M) (hM : 70 ≤ M) : Cover L M 8 (∏ a∈A,a) := by
  classical
  by_contra hbad
  let e := if M < 125 then 75 else 125
  have primeFor (a : ℕ) (h : a ∈ A.erase e) :
      ∃ p : ℕ, p.Prime ∧ p ∣ a ∧ M < 8*p := by
    obtain ⟨hne,hm⟩ := Finset.mem_erase.mp h
    rcases classify hM (ha a hm).1 (ha a hm).2 with hs | hp | hex
    · exact False.elim (hbad (splitCover A hc ha hm hs))
    · exact hp
    · unfold MediumException at hex
      dsimp only [e] at hne
      split at hne <;> omega
  have hn : (A.erase e).Nonempty := by
    by_cases h : e ∈ A <;> apply Finset.card_pos.mp <;> simp [h,Finset.card_erase_of_mem,hc]
  obtain ⟨a,ha'⟩ := hn
  obtain ⟨p,hp,hpa,hpM⟩ := primeFor a ha'
  have rest (b : ℕ) (hb : b ∈ A.erase e) : p ∣ b := by
    obtain ⟨q,hq,hqb,hqM⟩ := primeFor b hb
    by_cases same : p=q
    · exact same ▸ hqb
    · exact False.elim (hbad (twoPrimes A hc ha hM hp hpM
        ⟨a,Finset.mem_filter.mpr ⟨Finset.mem_of_mem_erase ha',hpa⟩⟩ hq hqM
        ⟨b,Finset.mem_filter.mpr ⟨Finset.mem_of_mem_erase hb,hqb⟩⟩ same))
  by_cases hall : ∀ b∈A, p∣b
  · exact hbad (groupAll A hp (fun b hb =>
      ⟨by have := (ha b hb).1; omega,(ha b hb).2,hall b hb,smallQuotient (ha b hb).2 hpM⟩))
  · push Not at hall
    obtain ⟨b,hb,hpb⟩ := hall
    have hbe : b=e := by
      by_contra hn
      exact hpb (rest b (Finset.mem_erase.mpr ⟨hn,hb⟩))
    subst b
    exact hbad (outlier A hc ha hM hp hpM hb (by dsimp [e]; split <;> decide) hpb rest)

end IntervalSix
