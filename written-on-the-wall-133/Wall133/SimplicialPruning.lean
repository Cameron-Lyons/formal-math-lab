import Wall133.IndependenceCore

/-! # Removing vertices of low neighborhood independence -/
namespace Wall133
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Removing a vertex costs at most twice its neighborhood independence
from the sum of all neighborhood independence numbers. -/
theorem sum_indep_le_delete_add_twice (h4 : NoFourCycle G) (x : V) :
    let S := Finset.univ.erase x
    (∑ z, G.indepNeighborsCard z) ≤ (∑ z : S, (G.induce (S : Set V)).indepNeighborsCard z) +
      2*G.indepNeighborsCard x := by
  classical
  let S := Finset.univ.erase x
  let H := G.induce (S : Set V)
  let w := triangleWeight G
  have zero (a : V) : w a a=0 := by simp [w,triangleWeight]
  have four : NoFourCycle H := fun _ _ _ _ hne a b c d =>
    Subtype.ext (h4 (fun he => hne (Subtype.ext he)) a b c d)
  have tot : mass w Finset.univ=2*∑ z,G.indepNeighborsCard z := by
    simp only [mass,w,weighted_degree_eq_twice_indep h4,Finset.mul_sum]
  have cost : (∑ z∈S,w x z)=2*G.indepNeighborsCard x := by
    have he := Finset.sum_erase_add (Finset.univ : Finset V) (w x) (Finset.mem_univ x)
    simpa only [zero,Nat.add_zero,w,weighted_degree_eq_twice_indep h4] using he
  have split := mass_insert (fun i j => weight_symm (G:=G) i j) zero (s:=S) (Finset.notMem_erase x Finset.univ)
  have ins : insert x S=Finset.univ := Finset.insert_erase (Finset.mem_univ _)
  change mass w (insert x S)=mass w S+2*∑ z∈S,w x z at split
  rw [ins,tot,cost] at split
  have localBound (u : S) : (∑ z∈S,w u.val z) ≤ 2*H.indepNeighborsCard u := by
    rw [←weighted_degree_eq_twice_indep (G:=H) four u,←Finset.sum_attach S (w u.val)]
    exact Finset.sum_le_sum (fun z _ => weight_induce_le S u z)
  have bound := Finset.sum_le_sum (s:=Finset.univ) (fun (z:S) _ => localBound z)
  have restr : mass w S = ∑ u:S,∑ z∈S,w u.val z := (Finset.sum_attach S _).symm
  rw [←restr,←Finset.mul_sum] at bound
  change (∑ z,G.indepNeighborsCard z) ≤ (∑ z:S,H.indepNeighborsCard z)+2*G.indepNeighborsCard x
  omega

/-- Deleting a vertex preserves an integer threshold whenever its
deletion cost is no larger than the threshold. -/
theorem le_l_delete_of_twice_indep_le [Nontrivial V] (h4 : NoFourCycle G) {k : ℕ}
    (hav : (k : ℝ)≤l G) (x : V) (low : 2*G.indepNeighborsCard x≤k) :
    (k : ℝ)≤l (G.induce (↑(Finset.univ.erase x) : Set V)) := by
  classical
  let S := Finset.univ.erase x
  let H := G.induce (S : Set V)
  obtain ⟨b,hb⟩ := exists_ne x
  let : Nonempty S := ⟨⟨b,Finset.mem_erase.mpr ⟨hb,Finset.mem_univ _⟩⟩⟩
  have cost := sum_indep_le_delete_add_twice h4 x
  change _ ≤ (∑ z:S,H.indepNeighborsCard z) + _ at cost
  have avg := le_average_iff_sum_indep.mp hav
  have size : Fintype.card V= S.card + 1 := by
    simp only [S,Finset.card_erase_of_mem (Finset.mem_univ x),Finset.card_univ]
    have := Fintype.card_pos (α:=V)
    omega
  rw [size,Nat.mul_succ] at avg
  have counted : k*Fintype.card S ≤ ∑ z:S,H.indepNeighborsCard z := by
    rw [Fintype.card_coe]
    omega
  apply le_average_iff_sum_indep.mpr
  convert counted using 1 <;> congr 2

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- A shortest path between other vertices cannot pass through a vertex
whose neighbors form a clique. -/
private theorem shortest_avoids_simplicial {a b x : V}
    (simplicial : G.IsClique (G.neighborSet x)) (ha : a≠x) (hb : b≠x)
    (p : G.Walk a b) (hp : p.length=G.dist a b) : x∉p.support := by
  intro contains
  obtain ⟨i,he,hi⟩ := Walk.mem_support_iff_exists_getVert.mp contains
  have pos : i ≠ 0 := fun e => ha (by simpa [e] using he)
  have lt : i < p.length := by
    by_contra! n
    exact hb (by simpa [le_antisymm hi n] using he)
  have left : G.Adj (p.getVert (i-1)) x := by
    have edge := p.adj_getVert_succ (by omega : i-1<p.length)
    simpa [show i-1+1=i by omega,he] using edge
  have right : G.Adj x (p.getVert (i+1)) := he ▸ p.adj_getVert_succ lt
  have ne : p.getVert (i-1) ≠ p.getVert (i+1) := by
    intro e
    have := (p.isPath_of_length_eq_dist hp).getVert_injOn (by omega : i-1≤p.length) (by omega : i+1≤p.length) e
    omega
  have chord := simplicial (show p.getVert (i-1) ∈ G.neighborSet x from left.symm) right ne
  have := (adj_getVert_iff_consecutive_of_length_eq_dist p hp (by omega : i-1≤p.length)
    (by omega : i+1≤p.length)).1 chord
  omega

omit [DecidableRel G.Adj] in
/-- Removing a simplicial vertex preserves all distances between the
remaining vertices. -/
theorem deletion_isometric_of_simplicial [Nontrivial V] (hc : G.Connected) {x : V}
    (simplicial : G.IsClique (G.neighborSet x)) :
    let S := Finset.univ.erase x
    let H := G.induce (S : Set V)
    H.Connected ∧ ∀ a b : S,H.dist a b=G.dist a.val b.val := by
  classical
  let S := Finset.univ.erase x
  let H := G.induce (S : Set V)
  obtain ⟨y,hy⟩ := exists_ne x
  let : Nonempty S := ⟨⟨y,Finset.mem_erase.mpr ⟨hy,Finset.mem_univ _⟩⟩⟩
  have geod (a b : S) : ∃ q : H.Walk a b, q.length=G.dist a.val b.val := by
    obtain ⟨p,_,hp⟩ := hc.exists_path_of_dist a.val b.val
    have avoid := shortest_avoids_simplicial simplicial (Finset.mem_erase.mp a.property).1
      (Finset.mem_erase.mp b.property).1 p hp
    have inside (z) (hz : z∈p.support) : z ∈ (S : Set V) := Finset.mem_erase.mpr
      ⟨fun h => avoid (h ▸ hz),Finset.mem_univ _⟩
    let q := p.induce (S : Set V) inside
    refine ⟨q,?_⟩
    have eq := congrArg Walk.length (p.map_induce inside)
    simpa only [Walk.length_map] using eq.trans hp
  have conn : H.Connected := ⟨fun a b => ⟨(geod a b).choose⟩⟩
  refine ⟨conn,?_⟩
  intro a b
  obtain ⟨q,hq⟩ := geod a b
  exact ((H.dist_le q).trans_eq hq).antisymm (dist_val_le_dist_induce (G:=G) _ conn a b)

omit [DecidableRel G.Adj] in
/-- If deleting a simplicial vertex lowers the radius, that vertex is
the unique farthest vertex from a center of the deletion graph. -/
theorem simplicial_deletion_lowers_radius_iff [Nontrivial V] (hc : G.Connected) {x : V}
    (simplicial : G.IsClique (G.neighborSet x)) :
    let S := Finset.univ.erase x
    (G.induce (S : Set V)).radius.toNat < G.radius.toNat ↔
      ∃ u : S, ∀ v ∈ S,G.dist u.val v < G.radius.toNat := by
  classical
  let S := Finset.univ.erase x
  let H := G.induce (S : Set V)
  obtain ⟨conn,iso⟩ := deletion_isometric_of_simplicial hc simplicial
  let : Nonempty S := conn.nonempty
  change H.radius.toNat < G.radius.toNat ↔ _
  constructor
  · intro drop
    obtain ⟨u,hu⟩ := H.exists_eccent_eq_radius
    refine ⟨u,fun v hv => ?_⟩
    have := dist_le_radius_toNat_of_eccent_eq_radius conn hu (⟨v,hv⟩ : S)
    rw [iso] at this
    change G.dist u.val v ≤ H.radius.toNat at this
    exact this.trans_lt drop
  · rintro ⟨u,hu⟩
    obtain ⟨v,q,hq,hr⟩ := exists_geodesic_ge_radius H conn u
    have hd := hu v.val v.property
    have eq := iso u v
    change H.dist u v=G.dist u.val v.val at eq
    omega


omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem indep_le_one_of_simplicial {x : V} (simplicial : G.IsClique (G.neighborSet x)) :
    G.indepNeighborsCard x ≤ 1 := by
  classical
  let K := G.induce (G.neighborSet x)
  obtain ⟨I,hi⟩ := exists_isNIndepSet_indepNum (G:=K)
  change K.indepNum ≤ 1
  rw [←hi.card_eq]
  apply Finset.card_le_one.mpr
  intro a ha b hb
  by_contra ne
  exact hi.isIndepSet ha hb ne (simplicial a.property b.property (fun e => ne (Subtype.ext e)))

/-- Every simplicial vertex of a minimum-order counterexample must be
the unique vertex at distance at least the old radius from some retained
vertex. Otherwise the deletion graph gives a smaller counterexample
at the same integer threshold. -/
theorem simplicial_counterexample_reduction [Nontrivial V] (hc : G.Connected) (h4 : NoFourCycle G)
    {x : V} (simplicial : G.IsClique (G.neighborSet x)) {k : ℕ} (hk : 2≤k) (hav : (k : ℝ)≤l G)
    (short : G.path < G.radius.toNat+k) :
    let S := Finset.univ.erase x
    let H := G.induce (S : Set V)
    (∃ u : S, (∀ v∈S,G.dist u.val v < G.radius.toNat) ∧ G.radius.toNat ≤ G.dist u.val x) ∨
    (H.Connected ∧ (k:ℝ)≤l H ∧ G.radius.toNat≤H.radius.toNat ∧ H.path<H.radius.toNat+k) := by
  classical
  let S := Finset.univ.erase x
  let H := G.induce (S : Set V)
  change _ ∨ (H.Connected ∧ _ ∧ _ ∧ H.path < H.radius.toNat+k)
  have conn := (deletion_isometric_of_simplicial hc simplicial).1
  by_cases drop : H.radius.toNat<G.radius.toNat
  · obtain ⟨u,hu⟩ := (simplicial_deletion_lowers_radius_iff hc simplicial).1 drop
    obtain ⟨v,q,hq,hr⟩ := exists_geodesic_ge_radius G hc u.val
    have eq : v=x := by
      by_contra neq
      have := hu v (Finset.mem_erase.mpr ⟨neq,Finset.mem_univ _⟩)
      omega
    have hd := hr.trans_eq hq
    rw [eq] at hd
    exact Or.inl ⟨u,hu,hd⟩
  · have low := indep_le_one_of_simplicial simplicial
    have newAverage := le_l_delete_of_twice_indep_le h4 hav x (by omega)
    have mono : H.path≤G.path := G.path_induce_le (S:Set V)
    exact Or.inr ⟨conn,newAverage,Nat.le_of_not_gt drop,mono.trans_lt (short.trans_le (Nat.add_le_add_right (Nat.le_of_not_gt drop) k))⟩

end Wall133
