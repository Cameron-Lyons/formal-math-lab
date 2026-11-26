module

public import Wall133.FiveCycle
public import Mathlib.Tactic.FinCases

@[expose] public section

namespace Wall133
open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

private def pairAt (a : Fin 6) : Finset (Fin 6) := {a, a+3}

set_option maxRecDepth 2000 in
set_option maxHeartbeats 2000000 in
private theorem six_masks : ∀ S : Finset (Fin 6), S.Nonempty → Legal S →
    (∃ a, S = pairAt a) ∨ ∃ (i : Fin 6) (b : Bool), CleanArc S (forwardArc (k := 5) i b) := by
  decide

/-- A six-vertex adjacency pattern determines its vertices injectively. -/
private theorem six_path [Fintype V] [DecidableEq V] {a b c d e f : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hde : G.Adj d e) (hef : G.Adj e f)
    (hac : ¬ G.Adj a c) (had : ¬ G.Adj a d) (hae : ¬ G.Adj a e) (haf : ¬ G.Adj a f)
    (hbd : ¬ G.Adj b d) (hbe : ¬ G.Adj b e) (hbf : ¬ G.Adj b f)
    (hce : ¬ G.Adj c e) (hcf : ¬ G.Adj c f) (hdf : ¬ G.Adj d f) : 6 ≤ G.path := by
  let vs : Fin 6 → V := ![a,b,c,d,e,f]
  have adj (i j : Fin 6) : G.Adj (vs i) (vs j) ↔ i.val+1 = j.val ∨ j.val+1 = i.val := by
    fin_cases i <;> fin_cases j <;>
      simp [vs, hab, hbc, hcd, hde, hef, hac, had, hae, haf, hbd, hbe, hbf, hce, hcf, hdf,
        G.adj_comm b a, G.adj_comm c a, G.adj_comm d a, G.adj_comm e a, G.adj_comm f a,
        G.adj_comm c b, G.adj_comm d b, G.adj_comm e b, G.adj_comm f b,
        G.adj_comm d c, G.adj_comm e c, G.adj_comm f c,
        G.adj_comm e d, G.adj_comm f d, G.adj_comm f e]
  apply path_bound_of_indices vs _ adj
  intro i j he
  have distinguish : ∀ i j : Fin 6,
      (∀ t : Fin 6, (i.val+1=t.val ∨ t.val+1=i.val) ↔ (j.val+1=t.val ∨ t.val+1=j.val)) → i=j := by decide
  apply distinguish i j
  intro t
  rw [← adj, ← adj, he]

private def footprint (C : Ring G 6) [DecidableRel G.Adj] (w : V) : Finset (Fin 6) :=
  Finset.univ.filter fun i => G.Adj w (C.label i)

private lemma mem_footprint (C : Ring G 6) [DecidableRel G.Adj] (w : V) (i : Fin 6) :
    i ∈ footprint C w ↔ G.Adj w (C.label i) := by simp [footprint]

private lemma attachment_pair [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (C : Ring G 6) (hC : C.Induced) (h4 : NoFourCycle G) (hp : G.path < 6) {w : V}
    (hout : w ∉ Set.range C.label) (ht : (footprint C w).Nonempty) :
    ∃ a, footprint C w = pairAt a := by
  rcases six_masks _ ht (legal_of_outside C hC h4 hout) with h | ⟨i,b,hi⟩
  · exact h
  · exact (hp.not_ge (CleanArc.extend C hC hi hout (mem_footprint C w))).elim

/-- Geometry of antipodal pairs in a six-cycle. The final arc goes from one
pair to the other, touching each only at the appropriate end. -/
private lemma adjacent_pairs : ∀ a b : Fin 6, pairAt a ≠ pairAt b →
    ∃ i ∈ pairAt a, ∃ j ∈ pairAt b, CyclicEdge i j := by decide

private lemma pair_arc : ∀ a b : Fin 6, pairAt a ≠ pairAt b →
    ∃ i j k : Fin 6, i ∈ pairAt a ∧ j ∉ pairAt a ∧ k ∉ pairAt a ∧
      i ∉ pairAt b ∧ j ∉ pairAt b ∧ k ∈ pairAt b ∧
      CyclicEdge i j ∧ CyclicEdge j k ∧ ¬ CyclicEdge i k := by decide

private lemma lone_arc : ∀ a : Fin 6, ∃ i j k : Fin 6,
    i ∈ pairAt a ∧ j ∉ pairAt a ∧ k ∉ pairAt a ∧
    CyclicEdge i j ∧ CyclicEdge j k ∧ ¬ CyclicEdge i k := by decide

private lemma pairs_meet : ∀ a : Fin 6, ∃ i ∈ pairAt a, ∃ j ∈ pairAt a, i ≠ j := by decide

/-- A vertex adjacent to one attacher and missing the cycle is adjacent to
every attacher, since otherwise it ends an induced six-vertex path. -/
private lemma common_attacher [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (C : Ring G 6) (hC : C.Induced) (h4 : NoFourCycle G) (hp : G.path < 6)
    {x y z : V} {a b : Fin 6} (hx : x ∉ Set.range C.label) (hy : y ∉ Set.range C.label)
    (ha : footprint C x = pairAt a) (hb : footprint C y = pairAt b)
    (hz : ∀ i, ¬ G.Adj z (C.label i)) (hyz : G.Adj y z) : G.Adj x z := by
  by_contra hxz
  have hxy : x ≠ y := fun h => hxz (h ▸ hyz)
  have ax (i) : G.Adj x (C.label i) ↔ i ∈ pairAt a := (mem_footprint C x i).symm.trans (ha ▸ Iff.rfl)
  have ay (i) : G.Adj y (C.label i) ↔ i ∈ pairAt b := (mem_footprint C y i).symm.trans (hb ▸ Iff.rfl)
  have hne : pairAt a ≠ pairAt b := by
    intro he
    obtain ⟨i,hi,j,hj,hij⟩ := pairs_meet a
    exact hij (C.label_inj (h4 hxy ((ax i).2 hi) ((ay i).2 (he ▸ hi)) ((ax j).2 hj) ((ay j).2 (he ▸ hj))))
  have hsep : ¬ G.Adj x y := by
    intro he
    obtain ⟨i,hi,j,hj,hij⟩ := adjacent_pairs a b hne
    have hd : x ≠ C.label j := fun h => hx ⟨j,h.symm⟩
    have e := h4 hd ((ax i).2 hi) ((C.edge_iff hC i j).2 hij).symm he ((ay j).2 hj).symm
    exact hy ⟨i,e⟩
  obtain ⟨i,j,k,hi,hj,hk,hi',hj',hk',hij,hjk,hik⟩ := pair_arc a b hne
  apply hp.not_ge
  exact six_path ((ax i).2 hi) ((C.edge_iff hC i j).2 hij) ((C.edge_iff hC j k).2 hjk)
    ((ay k).2 hk').symm hyz (hj ∘ (ax j).1) (hk ∘ (ax k).1) hsep hxz
    (hik ∘ (C.edge_iff hC i k).1) (fun h => hi' ((ay i).1 h.symm)) (fun h => hz i h.symm)
    (fun h => hj' ((ay j).1 h.symm)) (fun h => hz j h.symm) (fun h => hz k h.symm)

private lemma cycle_shortcuts : ∀ a i : Fin 6, a = i ∨ CyclicEdge a i ∨
    (∃ j, CyclicEdge a j ∧ CyclicEdge j i) ∨ i ∈ pairAt a := by decide

private lemma pair_covers : ∀ a b : Fin 6, ∃ j ∈ pairAt b, a = j ∨ CyclicEdge a j := by decide

/-- An induced six-cycle in a connected graph with no four-cycle and no induced
six-vertex path is either the whole graph, or provides a center of eccentricity two. -/
theorem hexagon_radius_or_average [Fintype V] [DecidableEq V] [DecidableRel G.Adj] [Nonempty V]
    (hc : G.Connected) (h4 : NoFourCycle G) (hp : G.path < 6)
    (C : Ring G 6) (hC : C.Induced) : G.radius.toNat ≤ 2 ∨ l G ≤ 2 := by
  classical
  by_cases hsur : Function.Surjective C.label
  · exact Or.inr (C.average_le_two_of_surjective hC hsur (by decide))
  left
  obtain ⟨w, hw⟩ : ∃ w, w ∉ Set.range C.label := by
    simpa [Function.Surjective, Set.mem_range] using hsur
  obtain ⟨q⟩ := hc (C.label 0) w
  obtain ⟨_, ⟨i,rfl⟩, x, hx, hix⟩ := exits (S := Set.range C.label) q ⟨0,rfl⟩ hw
  obtain ⟨a, ha⟩ := attachment_pair C hC h4 hp hx ⟨i, (mem_footprint C x i).2 hix.symm⟩
  have ax (j) : G.Adj x (C.label j) ↔ j ∈ pairAt a :=
    (mem_footprint C x j).symm.trans (ha ▸ Iff.rfl)
  have hax : G.Adj (C.label a) x := ((ax a).2 (by simp [pairAt])).symm
  let U : Set V := {z | z ∈ Set.range C.label ∨ (footprint C z).Nonempty ∨ G.Adj x z}
  have all_mem (v : V) : v ∈ U := by
    by_contra hnot
    obtain ⟨qv⟩ := hc (C.label a) v
    obtain ⟨y, hy, z, hz, hyz⟩ := exits qv (show C.label a ∈ U from Or.inl ⟨a,rfl⟩) hnot
    have hz' : ¬ (z ∈ Set.range C.label ∨ (footprint C z).Nonempty ∨ G.Adj x z) := hz
    push Not at hz'
    have hzc (i : Fin 6) : ¬ G.Adj z (C.label i) :=
      fun e => hz (Or.inr (Or.inl ⟨i, (mem_footprint C z i).2 e⟩))
    change y ∈ Set.range C.label ∨ (footprint C y).Nonempty ∨ G.Adj x y at hy
    by_cases hRing : y ∈ Set.range C.label
    · obtain ⟨i,rfl⟩ := hRing
      exact hzc i hyz.symm
    by_cases hTouch : (footprint C y).Nonempty
    · obtain ⟨b,hb⟩ := attachment_pair C hC h4 hp hRing hTouch
      exact hz'.2.2 (common_attacher C hC h4 hp hx hRing ha hb hzc hyz)
    have hxy : G.Adj x y := (hy.resolve_left hRing).resolve_left hTouch
    have hyc (i : Fin 6) : ¬ G.Adj y (C.label i) := fun e => hTouch ⟨i, (mem_footprint C y i).2 e⟩
    obtain ⟨i,j,k,hi,hj,hk,hij,hjk,hik⟩ := lone_arc a
    apply hp.not_ge
    exact six_path hyz.symm hxy.symm ((ax i).2 hi) ((C.edge_iff hC i j).2 hij)
      ((C.edge_iff hC j k).2 hjk) (fun h => hz'.2.2 h.symm) (hzc i) (hzc j) (hzc k)
      (hyc i) (hyc j) (hyc k) (hj ∘ (ax j).1) (hk ∘ (ax k).1) (hik ∘ (C.edge_iff hC i k).1)
  have two_steps {r s t : V} (hrs : G.Adj r s) (hst : G.Adj s t) : G.dist r t ≤ 2 :=
    (hc.dist_triangle (u := r) (v := s) (w := t)).trans_eq (by
      rw [dist_eq_one_iff_adj.mpr hrs, dist_eq_one_iff_adj.mpr hst])
  have hbound (z : V) : G.dist (C.label a) z ≤ 2 := by
    have hz := all_mem z
    by_cases hr : z ∈ Set.range C.label
    · obtain ⟨i,rfl⟩ := hr
      rcases cycle_shortcuts a i with rfl | h | ⟨j,hj,hj'⟩ | h
      · simp
      · rw [dist_eq_one_iff_adj.mpr ((C.edge_iff hC a i).2 h)]; decide
      · exact two_steps ((C.edge_iff hC a j).2 hj) ((C.edge_iff hC j i).2 hj')
      · exact two_steps hax ((ax i).2 h)
    change _ ∨ _ ∨ _ at hz
    rcases hz.resolve_left hr with h | h
    · obtain ⟨b,hb⟩ := attachment_pair C hC h4 hp hr h
      obtain ⟨i,hi,rfl | hi'⟩ := pair_covers a b
      · rw [dist_eq_one_iff_adj.mpr ((mem_footprint C z a).1 (hb.symm ▸ hi)).symm]; decide
      · exact two_steps ((C.edge_iff hC a i).2 hi') ((mem_footprint C z i).1 (hb.symm ▸ hi)).symm
    · exact two_steps hax h
  obtain ⟨z,q,hq,hr⟩ := exists_geodesic_ge_radius G hc (C.label a)
  exact hr.trans (hq ▸ hbound z)

end Wall133
