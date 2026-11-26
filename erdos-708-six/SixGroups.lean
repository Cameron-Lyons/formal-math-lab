module

public import SixStructure
public import PriorBounds
public import Mathlib.Algebra.BigOperators.Associated

@[expose] public section

namespace IntervalSix
open Erdos708Slots

def cofactors (S : Finset ℕ) (p : ℕ) := S.image fun a => a/p

theorem fiberData {M p : ℕ} (S : Finset ℕ) (hp : p.Prime)
    (hs : ∀ a ∈ S, 0<a ∧ a≤M ∧ p∣a ∧ a/p≤7) :
    let C := cofactors S p
    C.card = S.card ∧ (∏ a ∈ S, a) = p^S.card * (∏ c ∈ C, c) ∧
      C ⊆ Finset.Icc 1 (min 7 (M/p)) := by
  have heq (a : ℕ) (ha : a ∈ S) : p*(a/p) = a := Nat.mul_div_cancel' (hs a ha).2.2.1
  have hinj : Set.InjOn (fun a : ℕ => a/p) ↑S := by
    intro a ha b hb hab
    change a/p = b/p at hab
    rw [← heq a ha, ← heq b hb, hab]
  refine ⟨Finset.card_image_of_injOn hinj, ?_, ?_⟩
  · unfold cofactors
    rw [Finset.prod_image hinj]
    calc (∏ a ∈ S, a) = ∏ a ∈ S, p*(a/p) := Finset.prod_congr rfl (fun a ha => (heq a ha).symm)
         _ = _ := by simp [Finset.prod_mul_distrib]
  · intro c hc
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨hpos, ham, hdiv, h7⟩ := hs a ha
    exact Finset.mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd hpos hdiv) hp.pos,
      le_min h7 (Nat.div_le_div_right ham)⟩

/-- Any prime fiber of size at most three, with cofactors in `[1,7]`, has a cover
using at most one site per original. -/
theorem groupSmall {L M p : ℕ} (S : Finset ℕ) (hp : p.Prime)
    (hs : ∀ a ∈ S, 0<a ∧ a≤M ∧ p∣a ∧ a/p≤7) (hk : S.card≤3) :
    Cover L M S.card (∏ a ∈ S, a) := by
  obtain ⟨hcard,hprod,hsub⟩ := fiberData S hp hs
  let n := min 7 (M/p)
  have hfit : p*n≤M := (Nat.mul_le_mul_left p (min_le_right ..)).trans (Nat.mul_div_le M p)
  have hcnt := Finset.card_le_card hsub
  have hcount : S.card ≤ n := by simpa [hcard, n] using hcnt
  rw [hprod]
  apply liftCover hp.pos hfit hcount
  intro K
  simpa [hcard] using cofactor_cover K n _ (min_le_left ..) hsub (hcard ▸ hk)

/-- All originals in one prime fiber with cofactors in `[1,7]` have a cover
of at most seven sites. -/
theorem groupAll {L M p : ℕ} (S : Finset ℕ) (hp : p.Prime)
    (hs : ∀ a ∈ S, 0<a ∧ a≤M ∧ p∣a ∧ a/p≤7) :
    Cover L M 8 (∏ a ∈ S, a) := by
  obtain ⟨hcard,hprod,hsub⟩ := fiberData S hp hs
  let n := min 7 (M/p)
  have hfit : p*n≤M := (Nat.mul_le_mul_left p (min_le_right ..)).trans (Nat.mul_div_le M p)
  have hcnt := Finset.card_le_card hsub
  have hcount : S.card ≤ n := by simpa [hcard, n] using hcnt
  have hlift := liftCover (L := L) hp.pos hfit (le_rfl : n≤n)
    (fun K => whole_window K n _ hsub)
  have hn : n ≤ 7 := min_le_left ..
  rw [hprod]
  exact hlift.mono (by omega) (Nat.mul_dvd_mul (pow_dvd_pow p hcount) (dvd_refl _))

theorem smallQuotient {a M p : ℕ} (ha : a ≤ M) (hp : M < 8*p) : a/p ≤ 7 := by
  have := (Nat.div_lt_iff_lt_mul (by omega : 0 < p)).mpr (ha.trans_lt hp)
  omega

theorem groupBounds {M p : ℕ} {A : Finset ℕ} (ha : ∀ a ∈ A, 2≤a ∧ a≤M)
    (hcut : M < 8*p) (a : ℕ) (h : a ∈ A.filter (p ∣ ·)) :
    0<a ∧ a≤M ∧ p∣a ∧ a/p≤7 := by
  obtain ⟨hm,hd⟩ := Finset.mem_filter.mp h
  obtain ⟨h2,hM⟩ := ha a hm
  exact ⟨by omega,hM,hd,smallQuotient hM hcut⟩

/-- Join the multiples of a large prime to the complementary cover. A shared
site costs at most the product of the cofactors, one fresh site per cofactor. -/
theorem groupJoin {L M p k : ℕ} (A : Finset ℕ) (ha : ∀ a ∈ A, 2≤a ∧ a≤M)
    (hp : p.Prime) (p8 : 8 ≤ p) (hcut : M < 8*p) :
    let S := A.filter (p ∣ ·)
    S.card ≤ 3 → S.card+k ≤ 8 → 2*S.card+k ≤ 9 →
    Cover L M k (∏ a ∈ A \ S, a) → Cover L M 8 (∏ a ∈ A, a) := by
  intro S hS hcount hroom other
  let C := cofactors S p
  have hs := groupBounds ha hcut
  obtain ⟨hcard,hprod,hcof⟩ := fiberData S hp hs
  have hcop : p.Coprime (∏ a ∈ A \ S,a) := by
    apply hp.coprime_iff_not_dvd.mpr
    intro hd
    obtain ⟨a,ha',hd⟩ := ((Nat.prime_iff.mp hp).dvd_finsetProd_iff id).mp hd
    obtain ⟨hm,hout⟩ := Finset.mem_sdiff.mp ha'
    exact hout (Finset.mem_filter.mpr ⟨hm,hd⟩)
  rw [← Finset.prod_sdiff (show S ⊆ A from Finset.filter_subset ..), Nat.mul_comm]
  apply overlapRepair (groupSmall S hp hs hS) other C.toList hcount
  · simpa [C,hcard,two_mul,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hroom
  · intro c hc
    have hC : c ∈ C := by simpa using hc
    obtain ⟨a,hm,rfl⟩ := Finset.mem_image.mp hC
    exact ⟨(Finset.mem_Icc.mp (hcof hC)).1, ((Nat.mul_le_mul_right _ p8).trans
      (Nat.mul_div_le a p)).trans (hs a hm).2.1⟩
  · rw [hprod, (hcop.pow_left _).gcd_mul_left_cancel, Finset.prod_toList]
    exact Nat.gcd_dvd_left _ _

/-- If only one or two originals use a large prime, cover the other five or four
with the known bounds and join the prime group to that cover. -/
theorem rarePrimeCover {L M p : ℕ} (A : Finset ℕ) (hc : A.card=6)
    (ha : ∀ a ∈ A, 2≤a ∧ a≤M) (hp : p.Prime) (p8 : 8≤p) (hcut : M<8*p)
    (hne : (A.filter (p ∣ ·)).Nonempty) (hcnt : (A.filter (p ∣ ·)).card≤2) :
    Cover L M 8 (∏ a∈A,a) := by
  let S := A.filter (p ∣ ·)
  have hsub : S ⊆ A := Finset.filter_subset _ _
  have hpos : 0 < S.card := Finset.card_pos.mpr hne
  change S.card ≤ 2 at hcnt
  have hother (a : ℕ) (h : a ∈ A \ S) := ha a (Finset.mem_sdiff.mp h).1
  have hcd := Finset.card_sdiff_of_subset hsub
  rcases (by omega : S.card=1 ∨ S.card=2) with h1 | h2
  · exact groupJoin A ha hp p8 hcut (by omega : S.card≤3)
      (by omega : S.card+6≤8) (by omega : 2*S.card+6≤9)
      (fiveCover (A \ S) (by omega) hother)
  · exact groupJoin A ha hp p8 hcut (by omega : S.card≤3)
      (by omega : S.card+5≤8) (by omega : 2*S.card+5≤9)
      (fourCover (A \ S) (by omega) hother)

end IntervalSix
