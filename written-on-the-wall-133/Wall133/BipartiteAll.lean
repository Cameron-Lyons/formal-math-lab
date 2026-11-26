module

public import Wall133.ExactRotation
public import Wall133.CoreIncidence

@[expose] public section

/-!
# The floored conjecture for connected bipartite graphs

In a hypothetical counterexample every vertex of the degree core is
central. A rotation at a neighboring vertex then limits how many neighbors
can have degree strictly above the core minimum. Counting these incidences
in both directions contradicts the average degree retained by the core.
-/

namespace Wall133
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

/-- Vertices in opposite parts have different distances to a fixed vertex in a
connected bipartite graph. -/
theorem dist_ne_of_color_ne (hc : G.Connected) (c : G.Coloring (Fin 2))
    {a b v : V} (hab : c a ≠ c b) : G.dist a v ≠ G.dist b v := by
  obtain ⟨p,_,hp⟩ := hc.exists_path_of_dist v a
  obtain ⟨q,_,hq⟩ := hc.exists_path_of_dist v b
  have h₁ := (Chain.ofGeodesic p hp).color_val c p.length le_rfl
  have h₂ := (Chain.ofGeodesic q hq).color_val c q.length le_rfl
  simp only [Chain.ofGeodesic,Walk.getVert_zero, Walk.getVert_length] at h₁ h₂
  intro he
  have e : p.length=q.length := hp.trans ((G.dist_comm (u := v) (v := a)).trans
    (he.trans ((G.dist_comm (u := b) (v := v)).trans hq.symm)))
  rw [e] at h₁
  exact hab (Fin.ext (h₁.trans h₂.symm))

private theorem neighbor_dist_ne (hc : G.Connected) (c : G.Coloring (Fin 2))
    {a b v : V} (hab : G.Adj a b) : G.dist a v ≠ G.dist b v :=
  dist_ne_of_color_ne hc c (c.valid hab)

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj] [Nonempty V]

/-- The even density threshold follows by counting incidences at the
vertices whose degree exceeds the minimum guaranteed by the core. -/
theorem radius_add_even_density_le_path_exact (hc : G.Connected) (c : G.Coloring (Fin 2))
    (h4 : NoFourCycle G) {m : ℕ} (hm : 3 ≤ m)
    (hav : (2*m)*Fintype.card V ≤ ∑ v, G.degree v) (hr : 5 ≤ G.radius.toNat) :
    G.radius.toNat + 2*m ≤ G.path := by
  classical
  by_contra! hshort
  have hh : 2*(∑ _v : V, m) ≤ ∑ v,G.degree v := by
    simpa [Nat.mul_left_comm,Nat.mul_assoc,Nat.mul_comm] using hav
  obtain ⟨S,hS,hmin,hsum⟩ := exists_weighted_degree_core G (fun _ => m) (by omega) hh
  let H := G.induce (S : Set V)
  let d := m+1
  have : Nonempty S := hS.to_subtype
  have dense : S.card*(2*m) ≤ ∑ u : S,H.degree u := by
    simpa [Nat.mul_left_comm,Nat.mul_assoc,Nat.mul_comm] using hsum
  have central (a : S) (v : V) : G.dist a.val v ≤ G.radius.toNat := by
    by_cases h : 5 ≤ G.dist a.val v
    · obtain ⟨q,_,hq⟩ := hc.exists_path_of_dist a.val v
      obtain ⟨n,T,hl,_⟩ := exists_rotated_core_path hc c h4 S (by omega : 4≤m+1) hmin a q hq (by omega)
      have := T.length_le
      omega
    · omega
  have test (a x : S) (hax : H.Adj a x) (A : Finset S)
      (hA : ∀ z∈A, H.Adj x z ∧ (z=a ∨ d<H.degree z)) : A.card ≤ d-1 := by
    obtain ⟨v,q,hq,hrq⟩ := exists_geodesic_ge_radius G hc a.val
    have hcen := central a v
    have other : ∃ y ∈ H.neighborFinset a, y ≠ x := by
      by_contra! hall
      have h1 : (H.neighborFinset a).card ≤ 1 :=
        Finset.card_le_one.mpr (fun u hu w hw => (hall u hu).trans (hall w hw).symm)
      rw [H.card_neighborFinset_eq_degree] at h1
      have hh := hmin a
      change _ < H.degree a at hh
      omega
    obtain ⟨y,hy,hyx⟩ := other
    have hay : G.Adj a.val y.val := (H.mem_neighborFinset _ _).mp hy
    have hcy := central y v
    have hne := neighbor_dist_ne hc c (v := v) hay
    have htri := hc.dist_triangle (u := a.val) (v := y.val) (w := v)
    rw [dist_eq_one_iff_adj.mpr hay] at htri
    obtain ⟨w,_,hw⟩ := hc.exists_path_of_dist y.val v
    let p := w.cons hay
    have hp : p.length=G.dist a.val v := by change w.length+1=_; omega
    have hx : x.val ≠ p.getVert 1 := by
      have e : p.getVert 1=y.val := by simp [p]
      exact fun h => hyx (Subtype.ext (h.trans e).symm)
    exact geodesic_high_neighbors_bound hc c h4 S (by omega : 4 ≤ m+1) hmin a x p hp
      (by omega) hax hx (by omega) A hA
  exact core_incidence_contradiction S hS hm hmin dense test

/-- The full radius plus floored average bound for connected bipartite
graphs without a four-cycle, including irregular graphs of arbitrary radius. -/
theorem radius_add_floor_le_path_of_bipartite (hc : G.Connected) (hb : G.IsBipartite)
    (h4 : NoFourCycle G) : G.radius.toNat + ⌊l G⌋₊ ≤ G.path := by
  by_cases hr : G.radius.toNat ≤ 6
  · exact radius_add_floor_le_path_of_bipartite_radius_le_six hc hb h4 hr
  by_cases hk : ⌊l G⌋₊ < G.radius.toNat
  · have := chung_bound_nat G hc
    omega
  rcases Nat.mod_two_eq_zero_or_one ⌊l G⌋₊ with he | ho
  · have eq : 2*(⌊l G⌋₊/2) = ⌊l G⌋₊ := by omega
    have hdeg := sum_degree_ge_of_le_l (G := G) (k := ⌊l G⌋₊)
      (Nat.floor_le (div_nonneg (Finset.sum_nonneg (fun v _ =>
        Nat.cast_nonneg (G.indepNeighborsCard v))) (Nat.cast_nonneg _)))
    obtain ⟨c⟩ := hb
    have := radius_add_even_density_le_path_exact hc c h4 (m := ⌊l G⌋₊/2)
      (by omega) (by rwa [eq]) (by omega)
    omega
  · exact radius_add_floor_le_path_of_bipartite_odd hc hb h4 ho

end Wall133
