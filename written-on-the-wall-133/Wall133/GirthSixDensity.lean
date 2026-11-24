import Wall133.GirthSixGeodesic
import Wall133.GirthSixHigh
import Wall133.Bipartite

namespace Wall133
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableEq V] in
/-- If the vertices of degree above d have disjoint neighborhoods, the
average degree is strictly less than d+1. -/
private lemma degree_sum_lt_of_unique_high {d : ℕ} (hd : 0 < d)
    (unique : ∀ {a b x : V}, d < G.degree a → d < G.degree b → G.Adj x a → G.Adj x b → a=b) :
    (∑ v, G.degree v) < Fintype.card V*(d+1) := by
  classical
  let high := Finset.univ.filter (fun z : V => d < G.degree z)
  let low := Finset.univ.filter (fun z : V => ¬d < G.degree z)
  have lowSum : ∑ z ∈ low, G.degree z ≤ low.card*d := by
    simpa using Finset.sum_le_sum (s := low) (f := fun z : V => G.degree z) (g := fun _ => d)
      (fun z hz => Nat.le_of_not_gt (Finset.mem_filter.mp hz).2)
  have highSum : ∑ z∈high,G.degree z ≤ Fintype.card V := by
    calc
      _ = ∑ z∈high, (Finset.bipartiteAbove G.Adj Finset.univ z).card := by
        apply Finset.sum_congr rfl
        intro z _
        rw [← G.card_neighborFinset_eq_degree]
        congr 1
        ext u
        simp [Finset.bipartiteAbove]
      _ = ∑ x : V, (Finset.bipartiteBelow G.Adj high x).card :=
        Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow ..
      _ ≤ ∑ _x : V, 1 := by
        apply Finset.sum_le_sum
        intro x _
        apply Finset.card_le_one.mpr
        intro a ha b hb
        obtain ⟨ha',hxa⟩ := Finset.mem_filter.mp ha
        obtain ⟨hb',hxb⟩ := Finset.mem_filter.mp hb
        exact unique (Finset.mem_filter.mp ha').2 (Finset.mem_filter.mp hb').2 hxa.symm hxb.symm
      _ = _ := by simp
  have cs := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun z : V => d<G.degree z)
  change high.card+low.card=Finset.univ.card at cs
  rw [Finset.card_univ] at cs
  have split := Finset.sum_filter_add_sum_filter_not Finset.univ (fun z : V => d<G.degree z)
    (fun z : V => G.degree z)
  change (∑ z∈high,G.degree z)+(∑ z∈low,G.degree z)=∑ z : V,G.degree z at split
  rw [Nat.mul_succ]
  by_cases h : high.Nonempty
  · have := Nat.mul_lt_mul_of_pos_right
      (show low.card < Fintype.card V by have := h.card_pos; omega) hd
    omega
  · have hh := Finset.not_nonempty_iff_eq_empty.mp h
    simp [hh] at split cs
    have := Fintype.card_pos (α := V)
    rw [cs] at lowSum
    omega

/-- A density threshold of k ≥ 4 gives k+5 path vertices when k is even
and k+4 when k is odd, irrespective of the radius. -/
theorem girth_six_density_path_bound (hg : 6 ≤ G.egirth) {k : ℕ} (hk : 4 ≤ k)
    (hav : k*Fintype.card V ≤ ∑ v,G.degree v) : 2*(k/2)+5 ≤ G.path := by
  classical
  by_contra! hshort
  let m := k/2
  have hcost : 2 * (∑ _ : V, m) ≤ ∑ x, G.degree x := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    calc
      _ = (2*m)*Fintype.card V := by ac_rfl
      _ ≤ k*Fintype.card V := Nat.mul_le_mul_right _ (by dsimp [m]; omega)
      _ ≤ _ := hav
  obtain ⟨S,hS,hmin,hsum⟩ := exists_weighted_degree_core G (fun _ => m) (by dsimp [m]; omega) hcost
  let H := G.induce (S : Set V)
  have : Nonempty S := hS.to_subtype
  have hg' : 6 ≤ H.egirth := hg.trans (IsContained.egirth_le ⟨Copy.induce G (S : Set V)⟩)
  have mono : H.path ≤ G.path := G.path_induce_le (S : Set V)
  have bound : (∑ u : S,H.degree u) < Fintype.card S*((m+1)+1) := by
    apply degree_sum_lt_of_unique_high (by omega : 0 < m+1)
    intro a b x ha hb hxa hxb
    exact girth_six_high_no_common hg' (by dsimp [m]; omega : 3 ≤ m+1) hmin
      (by dsimp [m]; omega) ha hb hxa hxb
  change 2*(∑ _x ∈ S, m) ≤ ∑ v : S, H.degree v at hsum
  simp only [Finset.sum_const, nsmul_eq_mul] at hsum
  change 2*(S.card*m) ≤ ∑ v : S, H.degree v at hsum
  rw [Fintype.card_coe] at bound
  have le := Nat.mul_le_mul_left S.card (show (m+1)+1 ≤ 2*m by dsimp [m]; omega)
  have eq : S.card*(2*m)=2*(S.card*m) := by ac_rfl
  omega

omit [Nonempty V] in
/-- An induced subgraph of sufficiently high minimum degree proves the exact
girth-six inequality even when the whole graph is irregular and nonbipartite. -/
theorem radius_add_threshold_le_path_of_girth_six_core (hc : G.Connected) (hg : 6 ≤ G.egirth)
    (S : Finset V) (hs : S.Nonempty) {k d : ℕ} (hd : 5 ≤ d) (hk : k+4 ≤ 2*d)
    (hmin : ∀ v : S, d ≤ (G.induce (S : Set V)).degree v) :
    G.radius.toNat+k ≤ G.path := by
  have h := girth_six_radius_core_bound hg hc S hs hd hmin
  omega

/-- A geodesic and minimum-degree path growth give the radius plus the
minimum degree at every radius, without a bipartiteness assumption. -/
theorem radius_add_degree_le_path_of_girth_six (hc : G.Connected) (hg : 6 ≤ G.egirth)
    {d : ℕ} (hmin : ∀ v, d ≤ G.degree v) : G.radius.toNat+d ≤ G.path := by
  by_cases large : 5 ≤ d
  · apply radius_add_threshold_le_path_of_girth_six_core hc hg Finset.univ
      Finset.univ_nonempty large (by omega : d+4 ≤ 2*d)
    intro v
    have hne : G.neighborSet v.val ⊆ (↑(Finset.univ : Finset V) : Set V) := by simp
    convert (hmin v.val).trans_eq (degree_induce_of_neighborSet_subset hne).symm using 1
    congr 1
    apply Subsingleton.elim
  by_cases small : d ≤ 1
  · have := radius_add_one_le_path G hc
    omega
  have h := girth_six_min_degree_bound hg (by omega : 2 ≤ d) hmin (Classical.arbitrary V)
  have := chung_bound_nat G hc
  omega

/-- Every connected regular graph of girth at least six satisfies the
inequality even for the unrounded neighborhood average. -/
theorem radius_add_l_le_path_of_regular_girth_six (hc : G.Connected) (hg : 6 ≤ G.egirth)
    {d : ℕ} (hreg : G.IsRegularOfDegree d) : (G.radius.toNat : ℝ) + l G ≤ G.path := by
  have hp := radius_add_degree_le_path_of_girth_six hc hg (fun v => (hreg.degree_eq v).ge)
  have hl := averageIndepNeighbors_le_of_degree_le (fun v => (hreg.degree_eq v).le)
  have hp' : (G.radius.toNat : ℝ)+(d : ℝ) ≤ (G.path : ℝ) := by exact_mod_cast hp
  linarith

end Wall133
