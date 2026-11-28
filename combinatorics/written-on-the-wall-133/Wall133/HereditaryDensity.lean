module

public import Wall133.BipartiteGeodesic

@[expose] public section

/-! # Density inside a part of the graph

The radius in the bound is the radius of the entire graph even when the
average degree threshold holds only in an induced subgraph.
-/

namespace Wall133
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] in
/-- Lift degree lower bounds from a twice-induced subgraph to a vertex set
of the ambient graph. -/
theorem lift_core (U : Finset V) (T : Finset U) (hT : T.Nonempty)
    (f : V → ℕ) (hd : ∀ z : T, f z.val.val ≤
        ((G.induce (U : Set V)).induce (T : Set U)).degree z) :
    ∃ S : Finset V, S.Nonempty ∧ S ⊆ U ∧ ∀ z : S, f z.val ≤ (G.induce (S : Set V)).degree z := by
  classical
  let S := T.map (Function.Embedding.subtype (· ∈ U))
  let K := (G.induce (U : Set V)).induce (T : Set U)
  let H := G.induce (S : Set V)
  refine ⟨S,Finset.map_nonempty.mpr hT,?_,?_⟩
  · intro z hz
    obtain ⟨t,_,rfl⟩ := Finset.mem_map.mp hz
    exact t.property
  intro z
  obtain ⟨t,ht,he⟩ := Finset.mem_map.mp z.property
  let t' : T := ⟨t,ht⟩
  have hv : t.val = z.val := he
  let g : K.neighborSet t' → H.neighborSet z := fun w =>
    ⟨⟨w.val.val.val,Finset.mem_map.mpr ⟨w.val.val,w.val.property,rfl⟩⟩,
      show G.Adj z.val w.val.val.val from hv ▸ w.property⟩
  have ginj : Function.Injective g := by
    intro x y h
    exact Subtype.ext (Subtype.ext (Subtype.ext (congrArg (fun w : H.neighborSet z => w.val.val) h)))
  have hle := Fintype.card_le_of_injective g ginj
  rw [K.card_neighborSet_eq_degree, H.card_neighborSet_eq_degree] at hle
  exact (hv ▸ hd t').trans hle

omit [Fintype V] in
/-- A two-colored induced subgraph of odd average-degree threshold supplies
a core with the stronger degree bound on one color, in the ambient graph. -/
theorem exists_odd_colored_core_of_induce (U : Finset V) (hU : U.Nonempty)
    (hb : (G.induce (U:Set V)).IsBipartite) {m : ℕ} (hm : 0<m)
    (hav : (2*m+1)*U.card ≤ ∑ x:U,(G.induce (U:Set V)).degree x) :
    ∃ S : Finset V, S.Nonempty ∧ ∃ c : (G.induce (S:Set V)).Coloring (Fin 2),
      ∃ col : Fin 2, ∀ x : S, m+1+(if c x=col then 1 else 0) ≤ (G.induce (S:Set V)).degree x := by
  classical
  have : Nonempty U := hU.to_subtype
  obtain ⟨C⟩ := hb
  obtain ⟨col,T,hT,hmin⟩ := exists_odd_degree_core C hm (by simpa using hav)
  let color (x : V) : Fin 2 := if h : x ∈ U then C ⟨x,h⟩ else 0
  have color_in (x:U) : color x.val=C x := by simp [color,x.property]
  obtain ⟨S,hS,sub,bound⟩ := lift_core (G := G) U T hT (fun v => m+1+(if color v=col then 1 else 0))
    (fun z => by
      simp only [color_in]
      convert hmin z using 1)
  let c : (G.induce (S:Set V)).Coloring (Fin 2) := ⟨fun x => color x.val,by
    intro x y h
    have e : C (⟨x.val,sub x.property⟩:U) ≠ C (⟨y.val,sub y.property⟩:U) := C.valid h
    change color x.val ≠ color y.val
    simpa only [color, dite_eq_left (sub x.property), dite_eq_left (sub y.property)] using e⟩
  exact ⟨S,hS,c,col,bound⟩

/-- Any induced subgraph of average degree at least `k` supplies the
degree term of the two-vertex bound for the ambient radius. -/
theorem radius_add_induced_average_threshold_le_path_add_two [Nonempty V]
    (hc : G.Connected) (hb : G.IsBipartite) (h4 : NoFourCycle G)
    (U : Finset V) (hU : U.Nonempty) {k : ℕ}
    (hdensity : k * U.card ≤ ∑ v : U, (G.induce (U : Set V)).degree v)
    (hr : 2 ≤ G.radius.toNat) : G.radius.toNat+k ≤ G.path+2 := by
  classical
  by_cases hk : k ≤ 3
  · have := radius_add_one_le_path G hc
    omega
  let H := G.induce (U : Set V)
  have : Nonempty U := hU.to_subtype
  have hdeg : k * Fintype.card U ≤ ∑ v, H.degree v := by simpa using hdensity
  rcases Nat.mod_two_eq_zero_or_one k with he | he
  · obtain ⟨T,hT,hmin⟩ := exists_degree_core H (by omega : 0 < k) hdeg
    obtain ⟨S,hS,_,hSmin⟩ := lift_core (G := G) U T hT (fun _ => k/2+1) hmin
    obtain ⟨a,ha⟩ := hS
    obtain ⟨v,q,hq,hrq⟩ := exists_geodesic_ge_radius G hc a
    have := distance_add_twice_degree_le_path_add_four hc hb h4 S ha
      (by omega : 2 ≤ G.dist a v) hSmin
    omega
  · obtain ⟨c⟩ := hb
    let C : H.Coloring (Fin 2) := ⟨fun x => c x.val,fun h => c.map_rel h⟩
    let m := k/2
    have eq : 2*m+1 = k := by dsimp [m]; omega
    obtain ⟨col,T,hT,hmin⟩ := exists_odd_degree_core C (by omega : 0 < m) (eq ▸ hdeg)
    obtain ⟨S,hS,_,hmin'⟩ := lift_core (G := G) U T hT
      (fun v => m+1+(if c v = col then 1 else 0)) hmin
    have hodd := radius_add_odd_threshold_le_path_add_two_of_core hc c h4 S hS col hmin' hr
    omega

/-- The exact bound holds if some induced subgraph has average degree
at least two more than the floor for the whole graph. -/
theorem radius_add_floor_le_path_of_dense_induce [Nonempty V] (hc : G.Connected)
    (hb : G.IsBipartite) (h4 : NoFourCycle G) (U : Finset V) (hU : U.Nonempty)
    (hdensity : (⌊l G⌋₊+2)*U.card ≤ ∑ v : U, (G.induce (U : Set V)).degree v)
    (hr : 2 ≤ G.radius.toNat) : G.radius.toNat+⌊l G⌋₊ ≤ G.path := by
  have := radius_add_induced_average_threshold_le_path_add_two hc hb h4 U hU hdensity hr
  omega

end Wall133
