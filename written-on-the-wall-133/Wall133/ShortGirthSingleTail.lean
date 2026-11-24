import Wall133.ShortGirthStars

namespace Wall133
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {n : ℕ}

/-- Three usable positive contact sites suffice for a two-branch extension. -/
theorem path_of_three_metric_sites (P : Chain G n) (hn : 4≤n) (h4 : NoFourCycle G) (hc : G.Connected)
    (geo : ∀ i,4 ≤ i → i<n → 4≤G.dist (P.vertex 0) (P.vertex i)) {x y : V}
    (hx : Good P x) (hy : Good P y) (hxy : x≠y) (nxy : ¬G.Adj x y)
    (hdx : 3≤G.indepNeighborsCard x ∨ 4≤G.degree x) (hdy : 3≤G.indepNeighborsCard y ∨ 4≤G.degree y) :
    n+3≤G.path := by
  classical
  by_contra short
  have doubleContact {v w : V} (hv : Good P v) (hw : Good P w) (hvw : v≠w) (nvw : ¬G.Adj v w)
      (hd : 3≤G.indepNeighborsCard v ∨ 4≤G.degree v) :
      ∃ b, G.Adj v b ∧ G.Adj (P.vertex 2) b ∧ G.Adj (P.vertex n) b := by
    let R := grow P v hv
    obtain ⟨A⟩ := exists_contact_options R (by omega) h4 hd
    have card := A.size
    have one : ∃ b∈A.points,¬G.Adj b (P.vertex 3) := by
      by_contra! all
      have small : A.points.card≤1 := Finset.card_le_one.mpr (by
        intro s hs t ht
        exact h4 (hv.2.1 3 (by omega)) (A.adj _ hs) (all _ hs).symm (A.adj _ ht) (all _ ht).symm)
      omega
    obtain ⟨b,hb,miss⟩ := one
    have fb (i) (hi : i≤n) := A.fresh _ hb (i+1) (show i+1≤n+1 by omega)
    have ends (i) (hi : i≤n) (ha : G.Adj b (P.vertex i)) : i=2 ∨ i=n := by
      have lo := A.lower _ hb (i+1) (by omega) (by omega) ha
      by_cases ht : i=n
      · exact Or.inr ht
      have tri := hc.dist_triangle (u := P.vertex 0) (v := v) (w := P.vertex i)
      have tri' := hc.dist_triangle (u := v) (v := b) (w := P.vertex i)
      rw [dist_eq_one_iff_adj.mpr hv.1] at tri
      rw [dist_eq_one_iff_adj.mpr (show G.Adj v b from A.adj _ hb),dist_eq_one_iff_adj.mpr ha] at tri'
      have ne : i≠3 := fun e => miss (e ▸ ha)
      left
      by_contra h
      have := geo i (by omega) (by omega)
      omega
    have any : ∃ i≤n,G.Adj b (P.vertex i) := by
      by_contra! no
      have good : Good R b := by
        refine ⟨A.adj _ hb,A.fresh _ hb,?_⟩
        rintro (_|i) hi ip
        · contradiction
        · exact no i (by omega)
      exact short (grow R b good).length_le
    obtain ⟨i,hi,ha⟩ := any
    have right : G.Adj b (P.vertex n) := by
      by_contra nr
      have only (j) (hj : j≤n) (hb' : G.Adj b (P.vertex j)) := (ends j hj hb').resolve_right (fun e => nr (e ▸ hb'))
      exact short (independent_end_reroute P (by omega) h4 hv hw hvw nvw (A.adj _ hb)
        fb (fun j hj => ⟨only j hj,fun e => e ▸ (only i hi ha) ▸ ha⟩))
    have left : G.Adj b (P.vertex 2) := by
      by_contra nl
      have only (j) (hj : j≤n) (hb' : G.Adj b (P.vertex j)) := (ends j hj hb').resolve_left (fun e => nl (e ▸ hb'))
      exact short (independent_last_reroute P (by omega) h4 hv hw hvw nvw (A.adj _ hb)
        fb (fun j hj => ⟨only j hj,fun e => e ▸ right⟩))
    exact ⟨b,A.adj _ hb,left.symm,right.symm⟩
  obtain ⟨b,xb,b2,bn⟩ := doubleContact hx hy hxy nxy hdx
  obtain ⟨c,yc,c2,cn⟩ := doubleContact hy hx hxy.symm (fun h => nxy h.symm) hdy
  have ne : P.vertex 2≠P.vertex n := fun e => by have := P.inj (by omega) le_rfl e; omega
  have bc := h4 ne b2 bn c2 cn
  have be := h4 hxy xb (bc ▸ yc) hx.1.symm hy.1.symm
  rw [be] at b2
  have := (P.edges (by omega : 2≤n) (Nat.zero_le _)).1 b2
  omega

/-- A shortest path with one additional vertex at its far end gains two
further vertices from two independent extensions at its near end. -/
theorem path_of_three_contact_sites (P : Chain G n) (hn : 4≤n) (h4 : NoFourCycle G) (hc : G.Connected)
    (geo : ∀ i<n,G.dist (P.vertex 0) (P.vertex i)=i) {x y : V}
    (hx : Good P x) (hy : Good P y) (hxy : x≠y) (nxy : ¬G.Adj x y)
    (hdx : 3≤G.indepNeighborsCard x ∨ 4≤G.degree x) (hdy : 3≤G.indepNeighborsCard y ∨ 4≤G.degree y) :
    n+3≤G.path := by
  exact path_of_three_metric_sites P hn h4 hc (fun i hi il => by rw [geo i il]; exact hi) hx hy hxy nxy hdx hdy

end Wall133
