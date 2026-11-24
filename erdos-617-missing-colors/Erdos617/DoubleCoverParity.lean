import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

namespace Erdos617

open Finset SimpleGraph

/-- Each row has an overlapping partner with union excess below t by the
weighted sum bound. Two such partners would use more than its row sum.
The resulting one-regular graph cannot have odd order. -/
theorem no_odd_partner_table {ι : Type*} [Fintype ι] [DecidableEq ι] {r t : ℕ}
    (ht : 2≤t) (hn : Fintype.card ι=2*t+1) (b δ : ι→ℕ) (w g : ι→ι→ℕ)
    (hpos : ∀i,0<b i) (hdpos : ∀i,1≤δ i) (hbr : ∀i,b i+δ i=r)
    (hdsum : (∑i,δ i)+2=r) (hw : ∀i j,w i j=w j i) (hg : ∀i j,g i j=g j i)
    (hrow : ∀i, (∑j∈univ.erase i,w i j)=b i)
    (heq : ∀i j,i≠j → g i j+w i j+δ j=b i)
    (hmean : ∀i, (∑j∈univ.erase i, w i j*g i j) ≤ (t-1)*b i) : False := by
  classical
  let G : SimpleGraph ι := {
    Adj := fun i j => i≠j ∧ 0<w i j ∧ g i j<t
    symm := ⟨by
      intro i j he
      exact ⟨he.1.symm,hw i j ▸ he.2.1,hg i j ▸ he.2.2⟩⟩
    loopless := ⟨by simp⟩ }
  have exists_partner (i : ι) : ∃j, G.Adj i j := by
    by_contra! hno
    have per (j : ι) (hj : j∈univ.erase i) : w i j*t ≤ w i j*g i j := by
      by_cases hp : 0<w i j
      · apply Nat.mul_le_mul_left
        exact le_of_not_gt (fun hlo => hno j ⟨(mem_erase.mp hj).1.symm,hp,hlo⟩)
      · simp [Nat.eq_zero_of_not_pos hp]
    have all := sum_le_sum per
    rw [← sum_mul, hrow] at all
    have hstrict := Nat.mul_lt_mul_of_pos_right (show t-1<t by omega) (hpos i)
    nlinarith only [all,hmean i,hstrict]
  have unique {i j k : ι} (a : G.Adj i j) (b' : G.Adj i k) : j=k := by
    by_contra hjk
    have hij : i≠j := a.1
    have hik : i≠k := b'.1
    let R := univ.erase i
    let T := (R.erase j).erase k
    have hj : j ∈ R := mem_erase.mpr ⟨hij.symm,mem_univ _⟩
    have hk : k ∈ R.erase j := mem_erase.mpr ⟨Ne.symm hjk,mem_erase.mpr ⟨hik.symm,mem_univ _⟩⟩
    have w1 := sum_erase_add R (w i) hj
    have w2 := sum_erase_add (R.erase j) (w i) hk
    have wr : (∑ a ∈ R,w i a)=b i := hrow i
    have d0 := sum_erase_add univ δ (mem_univ i)
    have d1 := sum_erase_add R δ hj
    have d2 := sum_erase_add (R.erase j) δ hk
    change (∑ x ∈ R,δ x)+δ i=∑ x, δ x at d0
    change (∑ x ∈ T,δ x)+δ k=∑ x∈R.erase j,δ x at d2
    have size : T.card=2*t-2 := by
      simp only [T,card_erase_of_mem hk, card_erase_of_mem hj,R,card_erase_of_mem (mem_univ i),
        card_univ,hn]
      omega
    have need : T.card ≤ ∑ x∈T,δ x := by simpa using sum_le_sum (s := T) (fun x _ => hdpos x)
    have gj := a.2.2
    have gk := b'.2.2
    have ej := heq i j hij
    have ek := heq i k hik
    have bi := hbr i
    omega
  have deg (i : ι) : G.degree i=1 := by
    obtain ⟨j, hj⟩ := exists_partner i
    have hs : G.neighborFinset i={j} := by
      ext k
      simp only [mem_neighborFinset,mem_singleton]
      exact ⟨fun hk => unique hk hj, fun h => h ▸ hj⟩
    rw [← card_neighborFinset_eq_degree,hs,card_singleton]
  have shake := G.sum_degrees_eq_twice_card_edges
  simp only [deg,sum_const,card_univ,hn,nsmul_eq_mul,Nat.cast_id,Nat.mul_one] at shake
  omega

end Erdos617
