module

public import Wall133.NeighborhoodTriangles
public import Wall133.Girth

@[expose] public section

namespace Wall133
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableEq V] in
/-- After excluding the first path neighbor and all its neighbors, the number
of choices left is at least the neighborhood independence number minus one.
The excluded vertices form a clique of order at most two. -/
theorem eligible_neighbors_data (h4 : NoFourCycle G) {u x : V} (hux : G.Adj u x)
    (W : Finset V) (hW : ∀ w, w∈W ↔ G.Adj u w ∧ w≠x ∧ ¬G.Adj x w) :
    (∃ I ⊆ W, G.IsIndepSet (↑I : Set V) ∧ G.indepNeighborsCard u ≤ I.card+1) ∧
      G.degree u ≤ W.card+2 := by
  classical
  let H := G.induce (G.neighborSet u)
  obtain ⟨I,hI⟩ := exists_isNIndepSet_indepNum (G := H)
  let f := Function.Embedding.subtype (· ∈ G.neighborSet u)
  let A := I.map f
  have inA {w} (hw : w∈A) : G.Adj u w := by
    obtain ⟨v,_,rfl⟩ := Finset.mem_map.mp hw
    exact v.property
  have indep {v w} (hv : v∈A) (hw : w∈A) (hne : v≠w) : ¬G.Adj v w := by
    obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp hv
    obtain ⟨b,hb,rfl⟩ := Finset.mem_map.mp hw
    exact hI.isIndepSet ha hb (fun e => hne (congrArg f e))
  have triUnique {v w : V} (hv : G.Adj u v) (hw : G.Adj u w)
      (hxv : G.Adj x v) (hxw : G.Adj x w) := h4 hux.ne hv hxv hw hxw
  have bad {w : V} (hu : G.Adj u w) (hw : w ∉ W) : w=x ∨ G.Adj x w := by
    by_cases e : w=x
    · exact Or.inl e
    · exact Or.inr (by_contra (fun h => hw ((hW _).2 ⟨hu,e,h⟩)))
  have cardA : G.indepNeighborsCard u=A.card := by
    change H.indepNum = (I.map f).card
    rw [Finset.card_map,hI.card_eq]
  have badI : (A \ W).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro v hv w hw
    obtain ⟨hv,hv'⟩ := Finset.mem_sdiff.mp hv
    obtain ⟨hw,hw'⟩ := Finset.mem_sdiff.mp hw
    by_contra hne
    rcases bad (inA hv) hv' with rfl|hxv <;> rcases bad (inA hw) hw' with rfl|hxw
    · exact hne rfl
    · exact indep hv hw hne hxw
    · exact indep hv hw hne hxv.symm
    · exact hne (triUnique (inA hv) (inA hw) hxv hxw)
  constructor
  · refine ⟨A ∩ W,Finset.inter_subset_right,?_,?_⟩
    · intro a ha b hb hne
      exact indep (Finset.mem_inter.mp ha).1 (Finset.mem_inter.mp hb).1 hne
    · have := Finset.card_sdiff_add_card_inter A W
      omega
  · let B := (G.neighborFinset u).erase x
    have badB : (B \ W).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro v hv w hw
      obtain ⟨hv,hv'⟩ := Finset.mem_sdiff.mp hv
      obtain ⟨hw,hw'⟩ := Finset.mem_sdiff.mp hw
      obtain ⟨nv,av⟩ := Finset.mem_erase.mp hv
      obtain ⟨nw,aw⟩ := Finset.mem_erase.mp hw
      have hu := (G.mem_neighborFinset _ _).mp av
      have hvw := (G.mem_neighborFinset _ _).mp aw
      exact triUnique hu hvw ((bad hu hv').resolve_left nv) ((bad hvw hw').resolve_left nw)
    have hb : G.degree u-1 ≤ B.card := Finset.pred_card_le_card_erase
    have := Finset.card_le_card (Finset.inter_subset_right (s₁ := B) (s₂ := W))
    have := Finset.card_sdiff_add_card_inter B W
    omega

omit [DecidableEq V] in
theorem eligible_neighbors_card (h4 : NoFourCycle G) {u x : V} (hux : G.Adj u x)
    (W : Finset V) (hW : ∀ w, w∈W ↔ G.Adj u w ∧ w≠x ∧ ¬G.Adj x w) :
    G.indepNeighborsCard u ≤ W.card+1 ∧ G.degree u ≤ W.card+2 := by
  obtain ⟨⟨I,hI,_,hi⟩,hd⟩ := eligible_neighbors_data h4 hux W hW
  exact ⟨hi.trans (Nat.add_le_add_right (Finset.card_le_card hI) 1),hd⟩

theorem exists_stalled_contacts_at (hc : G.Connected) (h4 : NoFourCycle G) {u v : V}
    {p : G.Walk u v} (hp : Chordless p) (hn : 2 ≤ p.length)
    (sat : ∀ w, G.Adj u w → w ∉ p.support → ∃ i ≤ p.length, i ≠ 0 ∧ G.Adj w (p.getVert i)) :
    ∃ W : Finset V, (∀ w, w∈W ↔ G.Adj u w ∧ w≠p.getVert 1 ∧ ¬G.Adj (p.getVert 1) w) ∧
      (G.indepNeighborsCard u ≤ W.card+1 ∧ G.degree u ≤ W.card+2) ∧
      ∃ idx : W → ℕ, Function.Injective idx ∧
        ∀ w, 3 ≤ idx w ∧ idx w ≤ p.length ∧ G.Adj w.val (p.getVert (idx w)) ∧ G.dist u (p.getVert (idx w)) ≤ 2 := by
  classical
  let x := p.getVert 1
  let W := (G.neighborFinset u).filter (fun w => w ≠ x ∧ ¬G.Adj x w)
  have hW (w) : w∈W ↔ G.Adj u w ∧ w≠x ∧ ¬G.Adj x w := by simp [W]
  have hx : G.Adj u x := by simpa [x] using p.adj_getVert_succ (i := 0) (by omega)
  have pos (w : W) := (hW _).1 w.property
  choose idx hi hp0 hadj using (fun w : W => sat w.val (pos w).1 (hp.pending_off_path (pos w).1 (pos w).2.1))
  have unequal (i : ℕ) (hi : i≤p.length) (hne : i ≠ 0) : u ≠ p.getVert i := by
    intro eq
    exact hne (hp.simple.getVert_injOn (x₁ := 0) (x₂ := i) (Nat.zero_le _) hi
      (by simpa only [Walk.getVert_zero] using eq)).symm
  refine ⟨W,hW,eligible_neighbors_card h4 hx W hW,idx,?_,?_⟩
  · intro a b he
    exact Subtype.ext (h4 (unequal _ (hi a) (hp0 a)) (pos a).1 (hadj a).symm
      (pos b).1 (he ▸ (hadj b).symm))
  · intro w
    refine ⟨?_,hi w,hadj w,?_⟩
    · have h1 : idx w ≠ 1 := fun eq => (pos w).2.2 (by simpa [x,eq] using (hadj w).symm)
      have h2 : idx w ≠ 2 := by
        intro eq
        apply (pos w).2.1
        exact h4 (unequal 2 hn (by decide)) (pos w).1 (eq ▸ (hadj w).symm) hx
          (p.adj_getVert_succ (i := 1) (by omega)).symm
      have := hp0 w
      omega
    · have hd := hc.dist_triangle (u := u) (v := w.val) (w := p.getVert (idx w))
      simpa only [dist_eq_one_iff_adj.mpr (pos w).1,dist_eq_one_iff_adj.mpr (hadj w)] using hd

/-- Independent neighbors at a stalled endpoint yield distinct contacts
from index three onwards, even in the presence of triangles. -/
theorem exists_stalled_indep_contacts (hc : G.Connected) (h4 : NoFourCycle G) {u v : V}
    {p : G.Walk u v} (hp : Chordless p) (hn : 2 ≤ p.length)
    (sat : ∀ w, G.Adj u w → w ∉ p.support → ∃ i ≤ p.length, i ≠ 0 ∧ G.Adj w (p.getVert i)) :
    ∃ W : Finset V, G.indepNeighborsCard u ≤ W.card+1 ∧ ∃ idx : W → ℕ, Function.Injective idx ∧
      ∀ w, 3 ≤ idx w ∧ idx w ≤ p.length ∧ G.dist u (p.getVert (idx w)) ≤ 2 := by
  obtain ⟨W,_,h,idx,hi,hb⟩ := exists_stalled_contacts_at hc h4 hp hn sat
  exact ⟨W,h.1,idx,hi,fun w => ⟨(hb w).1,(hb w).2.1,(hb w).2.2.2⟩⟩

end Wall133
