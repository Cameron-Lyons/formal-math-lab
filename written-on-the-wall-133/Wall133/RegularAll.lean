module

public import Wall133.ShortGirthExact
public import Wall133.Bipartite

@[expose] public section

namespace Wall133
open SimpleGraph
variable {V : Type*} [Fintype V] [Nonempty V] {G : SimpleGraph V}

theorem le_average_iff_sum_indep {k : ℕ} : (k : ℝ) ≤ l G ↔
    k*Fintype.card V ≤ ∑ v,G.indepNeighborsCard v := by
  have hp : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  change _ ≤ (∑ v : V,(G.indepNeighborsCard v : ℝ)) / Fintype.card V ↔ _
  rw [le_div_iff₀ hp]
  exact_mod_cast (Iff.rfl : k*Fintype.card V ≤ ∑ v,G.indepNeighborsCard v ↔ _)

theorem exists_large_indep_neighbors {k : ℕ} (hk : (k : ℝ) ≤ l G) :
    ∃ v, k ≤ G.indepNeighborsCard v := by
  by_contra! h
  have lt := Finset.sum_lt_sum_of_nonempty (s := Finset.univ) Finset.univ_nonempty
    (fun (v : V) _ => h v)
  have hle := le_average_iff_sum_indep.mp hk
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at lt
  change (∑ v, G.indepNeighborsCard v) < Fintype.card V*k at lt
  rw [Nat.mul_comm k] at hle
  omega

variable [DecidableEq V] [DecidableRel G.Adj]

/-- Each vertex may meet either of two thresholds. The final endpoint is
chosen by the average and the two growth phases use whichever bound is
available at each successive vertex. -/
theorem radius_add_local_threshold_le_path (hc : G.Connected) (h4 : NoFourCycle G)
    {k : ℕ} (hk : (k : ℝ) ≤ l G) (hr : 2 ≤ G.radius.toNat)
    (hmin : ∀ x,k ≤ G.indepNeighborsCard x ∨ k+1 ≤ G.degree x) : G.radius.toNat+k ≤ G.path := by
  obtain ⟨v,hv⟩ := exists_large_indep_neighbors hk
  obtain ⟨a,q,hq,hlen⟩ := exists_geodesic_ge_radius G hc v
  have hrev : q.reverse.length=G.dist a v := by simpa [G.dist_comm] using hq
  have := geodesic_add_neighborhood_threshold_le_path h4 hc hmin q.reverse hv hrev (by simpa using hr.trans hlen)
  simp only [Walk.length_reverse] at this
  omega

omit [DecidableEq V] in
/-- If a regular graph attains degree d as its average neighborhood
independence, then it attains d at each individual vertex. -/
theorem local_threshold_of_regular {d k : ℕ} (hreg : G.IsRegularOfDegree d) (hk : (k : ℝ) ≤ l G) :
    ∀ v,k ≤ G.indepNeighborsCard v ∨ k+1 ≤ G.degree v := by
  classical
  intro v
  rw [hreg.degree_eq v]
  by_cases h : k < d
  · exact Or.inr h
  left
  by_contra! small
  have hle (u : V) : G.indepNeighborsCard u ≤ k :=
    (indepNeighborsCard_le_degree u).trans ((hreg.degree_eq u) ▸ Nat.le_of_not_gt h)
  have strict := Finset.sum_lt_sum (s := Finset.univ) (fun u _ => hle u) ⟨v,Finset.mem_univ _,small⟩
  have budget := le_average_iff_sum_indep.mp hk
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at strict
  change (∑ u, G.indepNeighborsCard u) < Fintype.card V*k at strict
  rw [Nat.mul_comm k] at budget
  omega
end Wall133
