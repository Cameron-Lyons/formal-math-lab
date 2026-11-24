import Wall133.Basic
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Independence

namespace Wall133

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] {G : SimpleGraph α}

omit [DecidableEq α] in
/-- An average above one gives a vertex with two nonadjacent neighbors. -/
private lemma exists_independent_neighbors (hav : 1 < l G) :
    ∃ v x y : α, G.Adj v x ∧ G.Adj v y ∧ x ≠ y ∧ ¬G.Adj x y := by
  classical
  have hx : ∃ v, 1 < G.indepNeighborsCard v := by
    by_contra! h
    have hsum : (∑ v : α, G.indepNeighbors v) ≤ Fintype.card α := by
      calc
        _ ≤ ∑ _v : α, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro v _
          unfold indepNeighbors
          exact_mod_cast h v
        _ = _ := by simp
    have hbound : l G ≤ 1 := by
      unfold l averageIndepNeighbors
      by_cases hcard : Fintype.card α = 0
      · simp [hcard]
      · exact (div_le_iff₀ (by exact_mod_cast Nat.pos_of_ne_zero hcard)).2 (by simpa using hsum)
    exact hav.not_ge hbound
  obtain ⟨v, hv⟩ := hx
  let H := G.induce (G.neighborSet v)
  obtain ⟨s, hs⟩ := exists_isNIndepSet_indepNum (G := H)
  have hcard : 1 < s.card := hs.card_eq.symm ▸ hv
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hcard
  exact ⟨v, x.1, y.1, x.2, y.2, fun h => hxy (Subtype.ext h), hs.isIndepSet hx hy hxy⟩

omit [Fintype α] in
/-- In a four-cycle-free graph, a neighbor of `v` cannot meet every other neighbor
if `v` has two nonadjacent neighbors. -/
private lemma exists_neighbor_off_first (hC4 : NoFourCycle G) {v s x y : α}
    (hvs : G.Adj v s) (hvx : G.Adj v x) (hvy : G.Adj v y)
    (hxy : x ≠ y) (hind : ¬G.Adj x y) :
    ∃ w, G.Adj v w ∧ w ≠ s ∧ ¬G.Adj s w := by
  by_contra! h
  by_cases hxs : x = s
  · subst x
    exact hind (h y hvy hxy.symm)
  by_cases hys : y = s
  · subst y
    exact hind (h x hvx hxs).symm
  exact hxy (hC4 hvs.ne hvx (h x hvx hxs) hvy (h y hvy hys))

/-- A geodesic can be extended one vertex past its first endpoint if that endpoint
has two nonadjacent neighbors and the graph has no four-cycle. -/
private lemma geodesic_add_two_le_path (hconn : G.Connected) (hC4 : NoFourCycle G)
    {v z x y : α} (p : G.Walk v z) (hp : p.length = G.dist v z) (hpos : 0 < p.length)
    (hvx : G.Adj v x) (hvy : G.Adj v y) (hxy : x ≠ y) (hind : ¬G.Adj x y) :
    p.length + 2 ≤ path G := by
  have hfirst : G.Adj v (p.getVert 1) := by simpa using p.adj_getVert_succ (i := 0) hpos
  obtain ⟨w, hvw, hne, hoff⟩ := exists_neighbor_off_first hC4 hfirst hvx hvy hxy hind
  have hdist (i : ℕ) (hi : i ≤ p.length) : G.dist v (p.getVert i) = i := by
    simpa using dist_getVert_eq_sub_of_le_of_length_eq_dist p hp (Nat.zero_le i) hi
  have hnmem : w ∉ p.support := by
    intro hm
    obtain ⟨i, hiw, hi⟩ := Walk.mem_support_iff_exists_getVert.mp hm
    have hi' := hdist i hi
    rw [hiw, dist_eq_one_iff_adj.mpr hvw] at hi'
    exact hne (hi' ▸ hiw.symm)
  have hchord (i : ℕ) (hi : i ≤ p.length) (ha : G.Adj w (p.getVert i)) : i = 0 := by
    have hle : i ≤ 2 := by
      calc
        i = G.dist v (p.getVert i) := (hdist i hi).symm
        _ ≤ G.dist v w + G.dist w (p.getVert i) := hconn.dist_triangle
        _ = 2 := by rw [dist_eq_one_iff_adj.mpr hvw, dist_eq_one_iff_adj.mpr ha]
    interval_cases i
    · rfl
    · exact (hoff ha.symm).elim
    · have hsecond : v ≠ p.getVert 2 := by
        intro heq
        have hd := hdist 2 hi
        rw [← heq, dist_self] at hd
        omega
      have h12 := p.adj_getVert_succ (i := 1) (by omega : 1 < p.length)
      exact (hne (hC4 hsecond hvw ha.symm hfirst h12.symm)).elim
  let q := Walk.cons hvw.symm p
  have hq : G.isInducedPath q.support := by
    apply isInducedPath_support_of_isPath_of_adj_getVert q ((p.isPath_of_length_eq_dist hp).cons hnmem)
    intro i j hi hj ha
    cases i <;> cases j
    · exact (ha.ne rfl).elim
    · rename_i j
      have h0 := hchord j (by simpa [q] using hj) ha
      omega
    · rename_i i
      have h0 := hchord i (by simpa [q] using hi) ha.symm
      omega
    · rename_i i j
      have hij := (adj_getVert_iff_consecutive_of_length_eq_dist p hp
        (by simpa [q] using hi : i ≤ p.length) (by simpa [q] using hj : j ≤ p.length)).mp ha
      omega
  have hlen := G.length_le_path_of_isInducedPath q.support hq
  rw [Walk.length_support] at hlen
  change p.length + 1 + 1 ≤ path G at hlen
  omega

/-- The open four-cycle-free branch gains a second vertex over the radius
as soon as the average neighborhood independence number exceeds one. -/
theorem radius_add_two_le_path_of_one_lt_l [Nontrivial α]
    (hconn : G.Connected) (hC4 : NoFourCycle G) (hav : 1 < l G) :
    G.radius.toNat + 2 ≤ path G := by
  obtain ⟨v, x, y, hvx, hvy, hxy, hind⟩ := exists_independent_neighbors hav
  obtain ⟨z, hz⟩ := G.exists_edist_eq_eccent_of_finite v
  have het : G.edist v z ≠ ⊤ := edist_ne_top_iff_reachable.mpr (hconn v z)
  have hr : G.radius.toNat ≤ G.dist v z := ENat.toNat_le_toNat (hz ▸ G.radius_le_eccent) het
  have hx : G.dist v x ≤ G.dist v z := ENat.toNat_le_toNat (hz ▸ G.edist_le_eccent) het
  rw [dist_eq_one_iff_adj.mpr hvx] at hx
  obtain ⟨p, _, hp⟩ := hconn.exists_path_of_dist v z
  have hpath := geodesic_add_two_le_path hconn hC4 p hp (by omega) hvx hvy hxy hind
  omega

/-- With a universal vertex in a four-cycle-free graph, each other vertex has a
clique for its neighborhood, forcing the neighborhood-independence average below two. -/
theorem l_lt_two_of_universal_vertex [Nonempty α] (hC4 : NoFourCycle G) (c : α)
    (hc : ∀ w, w ≠ c → G.Adj c w) : l G < 2 := by
  classical
  have hn : 0 < (Fintype.card α : ℝ) := by exact_mod_cast Fintype.card_pos
  have hlocal (w : α) (hw : w ≠ c) : G.indepNeighbors w ≤ 1 := by
    unfold indepNeighbors indepNeighborsCard
    norm_cast
    obtain ⟨s, hs⟩ := exists_isNIndepSet_indepNum (G := G.induce (G.neighborSet w))
    rw [← hs.card_eq, Finset.card_le_one]
    intro x hx y hy
    by_contra hxy
    have hind : ¬ G.Adj x.1 y.1 := hs.isIndepSet hx hy hxy
    by_cases hxc : x.1 = c
    · have hyc : y.1 ≠ c := fun he => hxy (Subtype.ext (hxc.trans he.symm))
      exact hind (hxc ▸ hc _ hyc)
    by_cases hyc : y.1 = c
    · exact hind (hyc ▸ (hc _ hxc).symm)
    exact hxy (Subtype.ext (hC4 hw x.2 (hc _ hxc) y.2 (hc _ hyc)))
  have hcenter : G.indepNeighbors c ≤ Fintype.card α := by
    unfold indepNeighbors indepNeighborsCard
    norm_cast
    obtain ⟨s, hs⟩ := exists_isNIndepSet_indepNum (G := G.induce (G.neighborSet c))
    rw [← hs.card_eq]
    exact s.card_le_univ.trans (Fintype.card_le_of_injective Subtype.val Subtype.val_injective)
  unfold l averageIndepNeighbors
  apply (div_lt_iff₀ hn).2
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ c)]
  have hrest : (∑ w ∈ Finset.univ.erase c, G.indepNeighbors w) ≤ (Fintype.card α : ℝ) - 1 := by
    calc
      _ ≤ ∑ _w ∈ Finset.univ.erase c, (1 : ℝ) :=
        Finset.sum_le_sum fun w hw => hlocal w (Finset.mem_erase.mp hw).1
      _ = _ := by simp [Nat.cast_sub Fintype.card_pos]
  linarith

/-- Every four-cycle-free graph of radius one lies in the first two bands. -/
theorem l_lt_two_of_radius_one [Nontrivial α] (hconn : G.Connected) (hC4 : NoFourCycle G)
    (hR : G.radius.toNat = 1) : l G < 2 := by
  obtain ⟨c, hc⟩ := G.exists_eccent_eq_radius
  apply l_lt_two_of_universal_vertex hC4 c
  intro w hw
  have hd := dist_le_radius_toNat_of_eccent_eq_radius hconn hc w
  have hne : G.dist c w ≠ 0 := by
    intro hzero
    exact hw (hconn.dist_eq_zero_iff.mp hzero).symm
  exact dist_eq_one_iff_adj.mp (by omega)

end Wall133
