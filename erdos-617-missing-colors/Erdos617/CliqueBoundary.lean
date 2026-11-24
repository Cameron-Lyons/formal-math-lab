import Erdos617.IndependentSets
import Mathlib.Data.Fintype.EquivFin

namespace Erdos617

open Finset

/-- If a full clique and an independent set of the same size are disjoint,
their matching forces a quadratic lower bound on the total degree excess. -/
theorem full_clique_independent_excess_bound
    {r : ℕ} {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hr : 3 ≤ r) (hV : Fintype.card V = r * r + 1)
    (C : Finset V) (hC : G.IsNClique r C)
    (hout : ∀ x ∉ C, ∀ y ∈ C, ∀ z ∈ C, G.Adj x y → G.Adj x z → y = z)
    (J : Finset V) (hJ : G.IsNIndepSet r J) (hdisj : Disjoint J C)
    (hi : G.IndepSetFree (r+1)) :
    (r-1)*(r-2) ≤ ∑ v, (G.degree v - r) := by
  classical
  have dominates {K : Finset V} (hK : G.IsNIndepSet r K) {v : V} (hv : v ∉ K) :
      ∃ z ∈ K, G.Adj v z := by
    by_contra! hn
    exact hi (insert v K) ⟨independent_insert_of_nonadjacent G hK.isIndepSet v hn,
      by rw [card_insert_of_notMem hv, hK.card_eq]⟩
  have choice (c : C) : ∃ j : J, G.Adj c.val j.val := by
    obtain ⟨j, hj, he⟩ := dominates hJ (Finset.disjoint_left.mp hdisj.symm c.prop)
    exact ⟨⟨j, hj⟩, he⟩
  choose partner hed using choice
  have hinj : Function.Injective partner := by
    intro a b he
    exact Subtype.ext (hout _ (Finset.disjoint_left.mp hdisj (partner a).prop)
      _ a.prop _ b.prop (hed a).symm (he ▸ (hed b).symm))
  have hsurj := ((Fintype.bijective_iff_injective_and_card partner).mpr
    ⟨hinj, by simpa using hC.card_eq.trans hJ.card_eq.symm⟩).surjective

  have sole (c : C) {k : V} (hk : k ∈ J) (he : G.Adj c.val k) : (partner c).val = k := by
    obtain ⟨d, hd⟩ := hsurj ⟨k, hk⟩
    have he' : G.Adj d.val k := by simpa only [hd] using hed d
    have hcd := hout k (Finset.disjoint_left.mp hdisj hk) _ c.prop _ d.prop he.symm he'.symm
    exact congrArg Subtype.val ((congrArg partner (Subtype.ext hcd)).trans hd)
  let X := (J ∪ C)ᶜ
  let N (x : V) := (J ∪ C).filter (G.Adj x)
  let L (v : V) := X.filter fun x => G.Adj x v
  let excess (v : V) := G.degree v - r
  have outside {x : V} (hx : x ∈ X) : x ∉ J ∧ x ∉ C :=
    not_or.mp (fun h => (mem_compl.mp hx) (mem_union.mpr h))
  -- A unique neighbor in the union would be the only neighbor in J.
  -- Replace it by x, freeing its matched clique vertex.
  have lower (x : V) (hx : x ∈ X) : 2 ≤ (N x).card := by
    by_contra! h
    obtain ⟨j, hj, hxj⟩ := dominates hJ (outside hx).1
    have hjN : j ∈ N x := mem_filter.mpr ⟨mem_union_left _ hj, hxj⟩
    have only {k : V} (hk : k ∈ J ∪ C) (he : G.Adj x k) : k = j := by
      by_contra hn
      have hkN : k ∈ N x := mem_filter.mpr ⟨hk, he⟩
      have := one_lt_card.mpr ⟨k, hkN, j, hjN, hn⟩
      omega
    obtain ⟨c, hc⟩ := hsurj ⟨j, hj⟩
    let K := insert x (J.erase j)
    have hK : G.IsNIndepSet r K := by
      have hxJ : x ∉ J.erase j := fun h => (outside hx).1 (mem_of_mem_erase h)
      refine ⟨independent_insert_of_nonadjacent G
        (hJ.isIndepSet.mono (erase_subset _ _)) x ?_, ?_⟩
      · intro k hk he
        exact (mem_erase.mp hk).1 (only (mem_union_left _ (mem_of_mem_erase hk)) he)
      · change (insert x (J.erase j)).card = r
        rw [card_insert_of_notMem hxJ, card_erase_of_mem hj, hJ.card_eq]
        omega
    have hcK : c.val ∉ K := by
      intro h
      rcases mem_insert.mp h with h | h
      · exact (outside hx).2 (h ▸ c.prop)
      · exact Finset.disjoint_left.mp hdisj (mem_of_mem_erase h) c.prop
    obtain ⟨w, hw, he⟩ := dominates hK hcK
    rcases mem_insert.mp hw with rfl | hw
    · have hcj := only (mem_union_right _ c.prop) he.symm
      exact Finset.disjoint_left.mp hdisj hj (hcj ▸ c.prop)
    · have hcw := sole c (mem_of_mem_erase hw) he
      rw [hc] at hcw
      exact (mem_erase.mp hw).1 hcw.symm
  have upperC (c : V) (hc : c ∈ C) : (L c).card ≤ excess c := by
    let p := partner ⟨c, hc⟩
    let F := insert p.val (C.erase c)
    have hpC := Finset.disjoint_left.mp hdisj p.prop
    have Fsize : F.card = r := by
      have hpe : p.val ∉ C.erase c := fun hz => hpC (mem_of_mem_erase hz)
      rw [show F = insert p.val (C.erase c) from rfl, card_insert_of_notMem hpe,
        card_erase_of_mem hc, hC.card_eq]
      omega
    have hdis : Disjoint F (L c) := by
      refine Finset.disjoint_left.mpr (fun v hv hL => ?_)
      obtain ⟨hx, _⟩ := mem_filter.mp hL
      rcases mem_insert.mp hv with rfl | hv
      · exact (outside hx).1 p.prop
      · exact (outside hx).2 (mem_of_mem_erase hv)
    have hsub : F ∪ L c ⊆ G.neighborFinset c := by
      intro v hv
      apply (G.mem_neighborFinset c v).mpr
      rcases mem_union.mp hv with hv | hv
      · rcases mem_insert.mp hv with rfl | hv
        · exact hed ⟨c, hc⟩
        · exact hC.isClique hc (mem_of_mem_erase hv) (Ne.symm (mem_erase.mp hv).1)
      · exact (mem_filter.mp hv).2.symm
    have hle := card_le_card hsub
    rw [card_union_of_disjoint hdis, Fsize, G.card_neighborFinset_eq_degree] at hle
    change _ ≤ G.degree c - r
    omega
  have upperJ (j : V) (hj : j ∈ J) : (L j).card ≤ (r-1) + excess j := by
    obtain ⟨c, hc⟩ := hsurj ⟨j, hj⟩
    have hcL : c.val ∉ L j := fun h => (outside (mem_filter.mp h).1).2 c.prop
    have hsub : insert c.val (L j) ⊆ G.neighborFinset j := by
      intro k hk
      refine (G.mem_neighborFinset _ _).mpr ?_
      rcases mem_insert.mp hk with rfl | hk
      · simpa only [hc] using (hed c).symm
      · exact (mem_filter.mp hk).2.symm
    have hle := card_le_card hsub
    rw [card_insert_of_notMem hcL, G.card_neighborFinset_eq_degree] at hle
    change _ ≤ (r-1) + (G.degree j-r)
    omega
  have count := sum_le_sum (s := X) lower
  simp only [sum_const, nsmul_eq_mul] at count
  rw [show (∑ x ∈ X, (N x).card) = ∑ z ∈ J ∪ C, (L z).card from
    sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow G.Adj, sum_union hdisj] at count
  have capJ := sum_le_sum (s := J) upperJ
  simp only [sum_add_distrib, sum_const, nsmul_eq_mul, hJ.card_eq] at capJ
  have capC := sum_le_sum (s := C) upperC
  have cap : (∑ j ∈ J, excess j) + (∑ c ∈ C, excess c) ≤ ∑ v, excess v := by
    rw [← sum_union hdisj]
    exact sum_le_univ_sum_of_nonneg fun _ => Nat.zero_le _
  have total := card_add_card_compl (J ∪ C)
  rw [card_union_of_disjoint hdisj, hC.card_eq, hJ.card_eq, hV] at total
  change r+r+X.card = r*r+1 at total
  change (r-1)*(r-2) ≤ ∑ v, excess v
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hr
  have hr1 : r-1 = 2+k := by omega
  have hr2 : r-2 = 1+k := by omega
  rw [hr1, hr2]
  rw [hr1, hk] at capJ
  rw [hk] at total
  nlinarith only [count, total, capJ, capC, cap]

/-- In a graph of order `r²+1` with maximum degree at most `r`, a full
clique with distinct exterior neighbors cannot coexist with a disjoint
independent `r`-set if the independence number is at most `r`. -/
theorem independent_outside_full_clique_impossible
    {r : ℕ} {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hr : 3 ≤ r) (hV : Fintype.card V = r * r + 1)
    (hdeg : ∀ v, G.degree v ≤ r) (C : Finset V) (hC : G.IsNClique r C)
    (hout : ∀ x ∉ C, ∀ y ∈ C, ∀ z ∈ C, G.Adj x y → G.Adj x z → y = z)
    (J : Finset V) (hJ : G.IsNIndepSet r J) (hdisj : Disjoint J C)
    (hi : G.IndepSetFree (r+1)) : False := by
  have h := full_clique_independent_excess_bound G hr hV C hC hout J hJ hdisj hi
  simp only [fun v => Nat.sub_eq_zero_of_le (hdeg v), Finset.sum_const_zero] at h
  exact (Nat.mul_pos (by omega : 0 < r-1) (by omega : 0 < r-2)).not_ge h

end Erdos617
