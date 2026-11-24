import Wall133.FourCycleFreeRotation
import Wall133.IndependentContacts

namespace Wall133
open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- Replace the first vertex of a stalled chain by a private neighbor of its
second vertex, then append the private neighbor of the opposite endpoint. -/
private theorem extend_at_private_ends {n : ℕ} (P : Chain G n) (h4 : NoFourCycle G)
    (hn : 3 ≤ n) {t w : V} (ht0 : G.Adj (P.vertex 0) t) (ht1 : G.Adj (P.vertex 1) t)
    (ht : ∀ i ≤ n, i ≠ 0 → G.Adj (P.vertex i) t → i=1)
    (hw0 : G.Adj (P.vertex 0) w) (hwn : G.Adj (P.vertex n) w)
    (hw : ∀ i ≤ n, i ≠ 0 → G.Adj (P.vertex i) w → i=n) :
    Nonempty (Chain G (n+1)) := by
  have fresh {z : V} {j : ℕ} (hz : G.Adj (P.vertex 0) z)
      (only : ∀ i ≤ n, i ≠ 0 → G.Adj (P.vertex i) z → i=j) (hj : 2 ≠ j) :
      ∀ i ≤ n, z ≠ P.vertex i := by
    intro i hi eq
    have idx := (P.edges (Nat.zero_le n) hi).mp (eq ▸ hz)
    have ei : i=1 := by omega
    subst i
    exact hj (only 2 (by omega) (by decide) (eq ▸ (P.edges (i:=2) (j:=1)
      (by omega) (by omega)).mpr (by decide)))
  have tf := fresh ht0 ht (by decide)
  have wf := fresh hw0 hw (by omega)
  have tw : t≠w := by
    intro eq
    have := ht n le_rfl (by omega) (eq ▸ hwn)
    omega
  have sep : ¬G.Adj t w := by
    intro adj
    have eq := h4 ht0.ne.symm adj hw0 ht1.symm
      ((P.edges (i:=0) (j:=1) (by omega) (by omega)).mpr (by decide))
    exact wf 1 (by omega) eq
  let segment : Chain G (n-1) :=
    ⟨fun i => P.vertex (i+1), fun {i j} hi hj eq => by
        have := P.inj (show i+1≤n by omega) (show j+1≤n by omega) eq
        omega,
      fun {i j} hi hj => by rw [P.edges (show i+1≤n by omega) (show j+1≤n by omega)]; omega⟩
  have good : Good segment t := by
    refine ⟨ht1,fun i hi => tf (i+1) (by omega),?_⟩
    intro i hi pos adj
    have := ht (i+1) (by omega) (by omega) adj.symm
    omega
  let Q := (grow segment t good).reverse
  have before (i) (hi : i<n) : Q.vertex i=P.vertex (n-i) := by
    change (grow segment t good).vertex (n-1+1-i)=_
    rw [show n-1+1-i=(n-i-1)+1 by omega]
    change P.vertex (n-i-1+1)=_
    rw [show n-i-1+1=n-i by omega]
  have last : Q.vertex n=t := by
    change (grow segment t good).vertex (n-1+1-n)=t
    rw [show n-1+1-n=0 by omega]
    rfl
  have more : Good Q w := by
    refine ⟨by simpa only [before 0 (by omega),Nat.sub_zero] using hwn,?_,?_⟩
    · intro i hi
      by_cases hi' : i<n
      · rw [before i hi']; exact wf _ (by omega)
      · rw [show i=n by omega,last]; exact tw.symm
    · intro i hi pos adj
      by_cases hi' : i<n
      · rw [before i hi'] at adj
        have := hw (n-i) (by omega) (by omega) adj.symm
        omega
      · rw [show i=n by omega,last] at adj
        exact sep adj.symm
  have extended := grow Q w more
  exact ⟨(show n-1+1+1=n+1 by omega) ▸ extended⟩

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- A connected four-cycle-free graph of minimum degree at least three has
an induced path with at least two more vertices than its minimum degree. -/
theorem three_le_min_degree_add_two (hc : G.Connected) (h4 : NoFourCycle G)
    {d : ℕ} (hd : 3 ≤ d) (hmin : ∀ x,d ≤ G.degree x) : d+2 ≤ G.path := by
  classical
  let a := hc.nonempty.some
  obtain ⟨b,hab⟩ := (G.degree_pos_iff_exists_adj a).mp (by have := hmin a; omega)
  let W := (G.neighborFinset b).filter (fun w => w≠a ∧ ¬G.Adj a w)
  have wm (w) : w∈W ↔ G.Adj b w ∧ w≠a ∧ ¬G.Adj a w := by simp [W]
  have count := (eligible_neighbors_card h4 hab.symm W wm).2
  obtain ⟨z,hz⟩ := Finset.card_pos.mp (by have := hmin b; omega : 0<W.card)
  obtain ⟨_,hza,haz⟩ := (wm z).mp hz
  obtain ⟨q,_,hq⟩ := hc.exists_path_of_dist a z
  have positive := hc.pos_dist_of_ne hza.symm
  have hq2 : 2≤q.length := by
    have : G.dist a z≠1 := fun h => haz (dist_eq_one_iff_adj.mp h)
    omega
  obtain ⟨s,P,_,_,_,stalled⟩ := longest_seed (Chain.ofGeodesic q hq) Finset.univ (by simp)
  let n := s+q.length
  change Chain G n at P
  have h2 : 2≤n := by dsimp [n]; omega
  have len := P.length_le
  by_contra! short
  have deg := hmin (P.vertex 0)
  obtain ⟨eq,sites⟩ := full_degree_private_sites P hc h4 h2
    (fun w _ => stalled w (by simp)) (by omega)
  obtain ⟨t,ht0,ht1,ht⟩ := sites 1 (by decide) (by omega)
  obtain ⟨w,hw0,hwn,hw⟩ := sites n (by omega) le_rfl
  obtain ⟨R⟩ := extend_at_private_ends P h4 (by omega) ht0 ht1 ht hw0 hwn hw
  have := R.length_le
  omega


omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem noFour_of_induce (S : Set V) (h4 : NoFourCycle G) : NoFourCycle (G.induce S) := by
  intro x y a b ne xA yA xB yB
  exact Subtype.ext (h4 (x:=x.val) (y:=y.val) (fun e => ne (Subtype.ext e)) xA yA xB yB)

private theorem path_of_nonempty_min_degree [Nonempty V] (h4 : NoFourCycle G)
    {d : ℕ} (hd : 3≤d) (hmin : ∀ x,d≤G.degree x) : d+2≤G.path := by
  classical
  let C := G.connectedComponentMk (Classical.arbitrary V)
  let K := C.toSimpleGraph
  have minK (x : C) : d ≤ K.degree x := by
    let neighbors : G.neighborSet x.val ≃ K.neighborSet x :=
      ⟨fun y => ⟨⟨y.val,C.mem_supp_of_adj_mem_supp x.property y.property⟩,y.property⟩,
       fun y => ⟨y.val.val,y.property⟩,fun _ => rfl,fun _ => rfl⟩
    have degree : G.degree x.val = K.degree x := by
      rw [←G.card_neighborSet_eq_degree,←K.card_neighborSet_eq_degree]
      exact Fintype.card_congr neighbors
    exact (hmin x.val).trans_eq degree
  have bound := three_le_min_degree_add_two (G:=K) C.connected_toSimpleGraph
    (noFour_of_induce C.supp h4) hd minK
  have mono : K.path ≤ G.path := @path_induce_le V _ _ G C.supp
    (inferInstanceAs (Fintype C)) (inferInstanceAs (DecidableEq C))
  exact bound.trans mono

/-- A single nonempty induced subgraph of minimum degree d supplies a path
with d+2 vertices in the ambient graph. -/
theorem core_degree_add_two_le_path (h4 : NoFourCycle G)
    (S : Finset V) (hs : S.Nonempty) {d : ℕ} (hd : 3≤d)
    (hmin : ∀ x:S,d≤(G.induce (S:Set V)).degree x) : d+2≤G.path := by
  classical
  have : Nonempty S := hs.to_subtype
  have bound := path_of_nonempty_min_degree (G:=G.induce (S : Set V)) (noFour_of_induce _ h4) hd hmin
  exact bound.trans (G.path_induce_le (S:Set V))

/-- A four-cycle-free graph of average degree at least k has an induced path
of at least ⌊k/2⌋+3 vertices when k is an integer at least four. -/
theorem half_degree_density_add_three [Nonempty V] (h4 : NoFourCycle G) {k : ℕ}
    (hk : 4≤k) (hav : k*Fintype.card V ≤ ∑ v,G.degree v) : k/2+3 ≤ G.path := by
  obtain ⟨S,hs,hmin⟩ := exists_degree_core G (by omega : 0<k) hav
  exact core_degree_add_two_le_path h4 S hs (by omega) hmin

end Wall133
