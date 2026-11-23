module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Nat.Sqrt
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

public section

open Finset

namespace Arxiv.«2607.05739»

/-- The starting points of pairs at distance d. -/
@[expose] def labelPairs (S : Finset ℕ) (d : ℕ) := S.filter fun a => a+d ∈ S

private theorem card_sq_of_pair_bound {S : Finset ℕ} {L B : ℕ} (hSL : S ⊆ range L)
    (hB : ∀ d, 0 < d → (labelPairs S d).card ≤ B) :
    S.card ^ 2 ≤ S.card + 2*L*B := by
  let byGap := (Ico 1 L).sigma (labelPairs S)
  let endpoints (z : Σ _ : ℕ, ℕ) := (z.2, z.2 + z.1)
  -- Every pair a < b is obtained from the gap b-a and its starting point a.
  have cover : ((S ×ˢ S).filter fun x => x.1 < x.2) ⊆ byGap.image endpoints := by
    rintro ⟨a,b⟩ h
    obtain ⟨hm, hab⟩ := mem_filter.mp h
    obtain ⟨ha,hb⟩ := mem_product.mp hm
    change a < b at hab
    have hbL := mem_range.mp (hSL hb)
    have hd : b-a ∈ Ico 1 L := mem_Ico.mpr ⟨by omega, by omega⟩
    have hstart : a ∈ labelPairs S (b-a) := by
      simpa [labelPairs, ha, Nat.add_sub_of_le hab.le] using hb
    refine mem_image.mpr ⟨⟨b-a,a⟩, mem_sigma.mpr ⟨hd,hstart⟩, ?_⟩
    simp [endpoints, Nat.add_sub_of_le hab.le]
  have hcount : S.card.choose 2 ≤ L*B := calc
    _ = _ := card_product_filter_lt.symm
    _ ≤ byGap.card := (card_le_card cover).trans card_image_le
    _ = ∑ d ∈ Ico 1 L, (labelPairs S d).card := card_sigma _ _
    _ ≤ ∑ _d ∈ Ico 1 L, B := sum_le_sum fun d hd => hB d (mem_Ico.mp hd).1
    _ ≤ _ := by simp; exact Nat.mul_le_mul_right B (Nat.sub_le _ _)
  -- Pascal’s identity gives m² = m + 2 * choose m 2.
  have h := Nat.add_one_mul_choose_eq S.card 1
  simp only [Nat.choose_succ_succ' _ 1, Nat.choose_one_right] at h
  nlinarith only [h, hcount]

/-- In an interval of length L, assume that for each pair of positive
differences (d,e), at most one starting point gives all four labels
a, a+d, a+e, a+d+e. Then the fourth power of the label count is O(L³). -/
theorem card_fourth_le_of_unique_parallelograms {S : Finset ℕ} {L : ℕ}
    (hSL : S ⊆ range L)
    (huniq : ∀ d e : ℕ, 0 < d → 0 < e → (labelPairs (labelPairs S d) e).card ≤ 1) :
    S.card ^ 4 ≤ 26 * (L+1)^3 := by
  have hsize : S.card ≤ L := by simpa using card_le_card hSL
  let r := Nat.sqrt (3*L)
  have hrep (d : ℕ) (hd : 0 < d) : (labelPairs S d).card ≤ r := by
    have hsub : labelPairs S d ⊆ S := filter_subset _ _
    have h := card_sq_of_pair_bound (hsub.trans hSL) (fun e he => huniq d e hd he)
    have := (card_le_card hsub).trans hsize
    apply Nat.le_sqrt'.mpr
    omega
  have h1 := card_sq_of_pair_bound hSL hrep
  have hr : r * r ≤ 3*L := Nat.sqrt_le _
  have hfactor : (1+2*r)^2 ≤ 26*(L+1) := by nlinarith [sq_nonneg ((r : ℤ)-1)]
  calc
    S.card ^ 4 = (S.card ^ 2)^2 := by ring
    _ ≤ (L*(1+2*r))^2 := Nat.pow_le_pow_left (by nlinarith) _
    _ = L^2 * (1+2*r)^2 := mul_pow _ _ _
    _ ≤ (L+1)^2 * (26*(L+1)) := Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) _) hfactor
    _ = _ := by ring

end Arxiv.«2607.05739»
