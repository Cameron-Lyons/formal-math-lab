module

public import Wall133.GirthSixOddSharp
public import Wall133.GirthSixTwoEnds

@[expose] public section

namespace Wall133
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Far from the degree core, a second neighbor of the eccentric endpoint
can be made a leaf in an induced subgraph containing the whole geodesic.
The geodesic in that subgraph gains one edge. -/
theorem girth_six_far_nonleaf (hg : 6 ≤ G.egirth) (hc : G.Connected)
    (S : Finset V) {d : ℕ} (hd : 4 ≤ d) (hmin : ∀ z : S,d ≤ (G.induce (S : Set V)).degree z)
    (independent : ∀ x y : S,(G.induce (S : Set V)).degree x=d →
      (G.induce (S : Set V)).degree y=d → ¬(G.induce (S : Set V)).Adj x y)
    (a : S) (v : V) (large : 5 ≤ G.dist a.val v) (hdeg : 2 ≤ G.degree v)
    (far : ∀ b : S,3 ≤ G.dist v b.val) : G.dist a.val v+2*d-1 ≤ G.path := by
  classical
  obtain ⟨q,_,hq⟩ := hc.exists_path_of_dist a.val v
  let g := q.reverse
  have ggeo : g.length=G.dist v a.val := by simp [g,hq,G.dist_comm]
  have gp : Chordless g := ⟨g.isPath_of_length_eq_dist ggeo,
    fun _ _ hi hj => (adj_getVert_iff_consecutive_of_length_eq_dist g ggeo hi hj).1⟩
  obtain ⟨z,hz,hne⟩ : ∃ z∈G.neighborFinset v,z ≠ g.getVert 1 := by
    by_contra! none
    have h : (G.neighborFinset v).card ≤ 1 := Finset.card_le_one.mpr
      (fun x hx y hy => (none x hx).trans (none y hy).symm)
    rw [G.card_neighborFinset_eq_degree] at h; omega
  have hvz := (G.mem_neighborFinset _ _).mp hz
  have off := gp.pending_off_path hvz hne
  have only (x : V) (hx : x∈q.support) (hzx : G.Adj z x) : x=v := by
    have h : x∈g.support := by simpa [g] using hx
    obtain ⟨i,he,hi⟩ := Walk.mem_support_iff_exists_getVert.mp h
    by_contra ne
    have pos : i ≠ 0 := by rintro rfl; exact ne (by simpa using he.symm)
    have := first_blocker (g:=6) hg gp hvz off hi pos (he ▸ hzx)
    have eq := dist_getVert_eq_sub_of_le_of_length_eq_dist g ggeo (Nat.zero_le _) hi
    rw [Walk.getVert_zero,Nat.sub_zero,he] at eq
    have tri := hc.dist_triangle (u:=v) (v:=z) (w:=x)
    rw [eq,dist_eq_one_iff_adj.mpr hvz,dist_eq_one_iff_adj.mpr hzx] at tri
    omega
  let W := insert z (S ∪ q.support.toFinset)
  let J := G.induce (W : Set V)
  have memS (u : S) : u.val∈W := Finset.mem_insert_of_mem (Finset.mem_union_left _ u.property)
  let A : W := ⟨a.val,memS a⟩
  let Z : W := ⟨z,Finset.mem_insert_self ..⟩
  let C := J.connectedComponentMk A
  let K := C.toSimpleGraph
  have pW : ∀ b∈(q.concat hvz).support,b∈(W : Set V) := by
    intro b hb
    rw [Walk.support_concat] at hb
    rcases List.mem_append.mp hb with h|h
    · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (List.mem_toFinset.mpr h))
    · simp [List.mem_singleton.mp h,W]
  let route : J.Walk A Z := (q.concat hvz).induce _ pW
  have ca : A∈C.supp := ConnectedComponent.connectedComponentMk_mem
  have cz : Z∈C.supp := ConnectedComponent.sound route.reachable.symm
  let a' : C := ⟨A,ca⟩
  let z' : C := ⟨Z,cz⟩
  let M := Finset.univ.filter (fun u : C => u.val.val∈S)
  have ma : a'∈M := Finset.mem_filter.mpr ⟨Finset.mem_univ _,a.property⟩
  let H := G.induce (S : Set V)
  let LM := K.induce (M : Set C)
  let old (x : M) : S := ⟨x.val.val.val,(Finset.mem_filter.mp x.property).2⟩
  have degree (x : M) : LM.degree x=H.degree (old x) := by
    let f (b : LM.neighborSet x) : H.neighborSet (old x) := ⟨old b.val,b.property⟩
    let back (b : H.neighborSet (old x)) : LM.neighborSet x := by
      let t : W := ⟨b.val.val,memS b.val⟩
      have e : J.Adj x.val.val t := b.property
      let t' : C := ⟨t,C.mem_supp_of_adj_mem_supp x.val.property e⟩
      have ht : t'∈M := Finset.mem_filter.mpr ⟨Finset.mem_univ _,b.val.property⟩
      exact ⟨⟨t',ht⟩,b.property⟩
    let equiv : LM.neighborSet x ≃ H.neighborSet (old x) :=
      ⟨f,back,fun _ => rfl,fun _ => rfl⟩
    rw [←LM.card_neighborSet_eq_degree,←H.card_neighborSet_eq_degree]
    exact Fintype.card_congr equiv
  have gJ : 6 ≤ J.egirth := hg.trans (IsContained.egirth_le ⟨Copy.induce G (W : Set V)⟩)
  have gK : 6 ≤ K.egirth := gJ.trans (IsContained.egirth_le ⟨Copy.induce J C.supp⟩)
  have hK := C.connected_toSimpleGraph
  obtain ⟨p,_,dp⟩ := hK.exists_path_of_dist a' z'
  let back := (Embedding.induce (G:=G) (W : Set V)).toHom.comp C.toSimpleGraph_hom
  have lastEdge (b : C) (h : K.Adj z' b) : b.val.val=v := by
    have hb := Finset.mem_insert.mp b.val.property
    change G.Adj z b.val.val at h
    rcases hb with hEq|hm
    · exact (h.ne hEq.symm).elim
    rcases Finset.mem_union.mp hm with hs|hq'
    · have hfar : 3 ≤ G.dist v b.val.val := far ⟨b.val.val,hs⟩
      have tr := hc.dist_triangle (u:=v) (v:=z) (w:=b.val.val)
      rw [dist_eq_one_iff_adj.mpr hvz,dist_eq_one_iff_adj.mpr h] at tr
      clear * - hfar tr; omega
    · exact only _ (List.mem_toFinset.mp hq') h
  have uneq : a' ≠ z' := by
    intro eq
    have e : a.val=z := congrArg (fun b : C => b.val.val) eq
    have small := dist_eq_one_iff_adj.mpr hvz.symm
    rw [←e] at small
    omega
  have pn : ¬p.Nil := fun h => uneq h.eq
  have pen := lastEdge p.penultimate (p.adj_penultimate pn).symm
  have dist := G.dist_le (p.dropLast.map back)
  change G.dist a.val p.penultimate.val.val ≤ _ at dist
  rw [pen,Walk.length_map,Walk.length_dropLast] at dist
  have bound := girth_six_independent_low_pointed gK hK M hd
    (fun u => (hmin (old u)).trans_eq (degree u).symm)
    (fun u b du db h => independent (old u) (old b) ((degree u).symm.trans du) ((degree b).symm.trans db) h)
    ⟨a',ma⟩ p dp (by clear * - large dist; omega)
  have monoK : K.path ≤ J.path := @path_induce_le W (inferInstanceAs (Fintype W))
    (inferInstanceAs (DecidableEq W)) J C.supp (inferInstanceAs (Fintype C))
    (inferInstanceAs (DecidableEq C))
  have monoJ : J.path ≤ G.path := @path_induce_le V _ _ G (W : Set V)
    (inferInstanceAs (Fintype W)) (inferInstanceAs (DecidableEq W))
  clear * - large dist bound monoK monoJ
  omega


/-- If two vertices at distance at most two from each other are respectively
a nonleaf eccentric endpoint and a core vertex, two-ended growth recovers
the distance loss at radius at least sixteen. -/
theorem girth_six_path_of_distant_nonleaf (hg : 6 ≤ G.egirth) (hc : G.Connected)
    (S : Finset V) {d : ℕ} (hd : 6 ≤ d) (hmin : ∀ z : S,d ≤ (G.induce (S : Set V)).degree z)
    (independent : ∀ x y : S,(G.induce (S : Set V)).degree x=d →
      (G.induce (S : Set V)).degree y=d → ¬(G.induce (S : Set V)).Adj x y)
    (a : S) (v : V) (large : 16 ≤ G.dist a.val v) (deg : 2 ≤ G.degree v) :
    G.dist a.val v+2*d-1 ≤ G.path := by
  by_cases far : ∀ b : S,3 ≤ G.dist v b.val
  · exact girth_six_far_nonleaf hg hc S (by omega) hmin independent a v (by omega) deg far
  push Not at far
  obtain ⟨b,hb⟩ := far
  have tri := hc.dist_triangle (u:=a.val) (v:=b.val) (w:=v)
  rw [G.dist_comm (u:=b.val) (v:=v)] at tri
  have := girth_six_distance_between_core_vertices hg hc S (by omega : 5 ≤ d) hmin a b
    (by omega) (j:=5) (by omega) (by omega)
  omega

/-- The exact odd threshold at radius at least sixteen for a graph with
at most one vertex of degree at most one. -/
theorem girth_six_odd_of_at_most_one_leaf (hg : 6 ≤ G.egirth) (hc : G.Connected)
    {m : ℕ} (hav : (2*m+1)*Fintype.card V ≤ ∑ v,G.degree v)
    (hr : 16 ≤ G.radius.toNat) (leaves : ∀ a b, G.degree a ≤ 1 → G.degree b ≤ 1 → a=b) :
    G.radius.toNat+(2*m+1) ≤ G.path := by
  classical
  have : Nonempty V := hc.nonempty
  by_contra! bad
  have chung := chung_bound_nat G hc
  have hd : 6 ≤ m+1 := by omega
  have hsum : (2*(m+1)-1)*Fintype.card V ≤ ∑ v,G.degree v := by
    rwa [show 2*(m+1)-1=2*m+1 by omega]
  obtain ⟨S,hS,_,min,ind,center,layers⟩ := girth_six_central_core_of_odd_shortfall hg hc
    (by omega : 4 ≤ m+1) hsum (by omega) (by omega)
  let H := G.induce (S : Set V)
  have low : ∃ a : S,H.degree a=m+1 := by
    by_contra! all
    have bigger (a : S) : m+2 ≤ H.degree a := by
      have deg : m+1 ≤ H.degree a := min a
      have := all a; omega
    have := girth_six_radius_core_sharp hc hg S hS (by omega : 2 ≤ m+2) bigger
    omega
  obtain ⟨a,ha⟩ := low
  obtain ⟨y,hy⟩ := (H.degree_pos_iff_exists_adj a).mp (by omega)
  have endLeaf (x : S) : ∃ v,G.dist x.val v=G.radius.toNat ∧ G.degree v ≤ 1 := by
    obtain ⟨v,q,hq,hv⟩ := exists_geodesic_ge_radius G hc x.val
    have cap := center x v
    refine ⟨v,by omega,?_⟩
    by_contra! high
    have := girth_six_path_of_distant_nonleaf hg hc S hd min ind x v (by omega) (by omega)
    omega
  obtain ⟨v,hv,hvl⟩ := endLeaf a
  obtain ⟨w,hw,hwl⟩ := endLeaf y
  obtain rfl := leaves _ _ hvl hwl
  have := (layers a y ha hy v).1 hv
  omega

end Wall133
