module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.Card
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace Erdos617

open Finset

/-- Summing the strengthened pair inequalities over the neighbors of a fixed
clique bounds its overlap-weighted mean pair excess. -/
theorem double_cover_star_mean {ι : Type*} [Fintype ι] [DecidableEq ι] {r t : ℕ}
    (ht : 2 ≤ t) (hn : Fintype.card ι=2*t+1) (b δ : ι → ℕ) (w g : ι → ι → ℕ)
    (hdpos : ∀ i, 1 ≤ δ i) (hbr : ∀ i, b i+δ i=r) (hdsum : (∑ i,δ i)+2=r)
    (hw : ∀ i j, w i j=w j i) (hg : ∀ i j, g i j=g j i)
    (hrow : ∀ i, (∑ j ∈ univ.erase i, w i j)=b i)
    (heq : ∀ i j, i≠j → g i j+w i j+δ j=b i)
    (hp : ∀ i j, i≠j → w i j*g i j +
      (∑ z ∈ (univ.erase i).erase j, w i z*w j z) ≤ δ i*δ j+g i j) :
    ∀ i, (∑ j ∈ univ.erase i, w i j*g i j) ≤ (t-1)*b i := by
  classical
  intro i
  let R := univ.erase i
  have hR : R.card = 2*t := by simp [R,hn]
  have residual (z : ι) (hz : z ∈ R) : (∑ j ∈ R.erase z, w j z)=δ i+g i z := by
    have hzi := (mem_erase.mp hz).1
    have hi : i ∈ (univ : Finset ι).erase z := mem_erase.mpr ⟨hzi.symm,mem_univ _⟩
    have hs := sum_erase_add (univ.erase z) (w z) hi
    rw [hrow, erase_right_comm] at hs
    have eq := heq z i hzi
    rw [hg z i] at eq
    have flip : (∑ j ∈ R.erase z, w j z) = ∑ j ∈ R.erase z, w z j :=
      sum_congr rfl (fun j _ => hw j z)
    rw [flip]
    change (∑ j ∈ R.erase z, w z j)+w z i=b z at hs
    omega
  have dot : (∑ j ∈ R, ∑ z ∈ R.erase j, w i z*w j z) =
      (b i*δ i) + ∑ z ∈ R, w i z*g i z := by
    calc
      _ = ∑ z ∈ R, ∑ j ∈ R.erase z, w i z*w j z := by
        simp only [← filter_ne', sum_filter]
        rw [sum_comm]
        exact sum_congr rfl fun z _ => sum_congr rfl fun j _ => by by_cases h : j=z <;> simp [h,Ne.symm]
      _ = ∑ z ∈ R, w i z*(δ i+g i z) := by
        refine sum_congr rfl fun z hz => ?_
        rw [← mul_sum, residual z hz]
      _ = _ := by simp only [Nat.mul_add, sum_add_distrib, ← sum_mul, R, hrow]
  have hh := sum_le_sum (s := R) (fun j hj => hp i j (mem_erase.mp hj).1.symm)
  simp only [sum_add_distrib, ← mul_sum] at hh
  change (∑ j ∈ R, w i j*g i j) + (∑ j ∈ R, ∑ z ∈ R.erase j, w i z*w j z) ≤ _ at hh
  rw [dot] at hh
  have small := sum_erase_add univ δ (mem_univ i)
  have ds : (∑ j ∈ R, δ j)+2=b i := by
    change (∑ j ∈ R, δ j)+δ i=∑ j,δ j at small
    have hi := hbr i
    omega
  have row := sum_congr (s₁ := R) rfl (fun j hj => heq i j (mem_erase.mp hj).1.symm)
  simp only [sum_add_distrib, sum_const, nsmul_eq_mul, Nat.cast_id, hR] at row
  change (∑ j ∈ R, w i j*g i j) ≤ (t-1)*b i
  have wr : (∑ j ∈ R,w i j)=b i := hrow i
  rw [wr] at row
  nlinarith only [hh, row, ds, congrArg (δ i*·) ds, hdpos i,
    congrArg (·*b i) (show t-1+1=t by omega)]

end Erdos617
