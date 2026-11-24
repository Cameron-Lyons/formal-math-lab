import Wall133.ShortGirthFifthData

namespace Wall133.FifthCertificate
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

/-- Independent neighbors of one endpoint of a five-edge induced path, after
excluding the first path edge and its possible triangle. -/
structure Choices (P : Chain G 5) (m : ℕ) where
  v : Fin m ↪ V
  edge : ∀ i,G.Adj (P.vertex 0) (v i)
  fresh : ∀ i j,j≤5 → v i≠P.vertex j
  miss : ∀ i j,0<j → j≤2 → ¬G.Adj (v i) (P.vertex j)
  independent : ∀ i j,i≠j → ¬G.Adj (v i) (v j)

private theorem chooseEnd [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (P : Chain G 5)
    (h4 : NoFourCycle G) {m : ℕ} (high : m+1≤G.indepNeighborsCard (P.vertex 0)) :
    Nonempty (Choices P m) := by
  classical
  obtain ⟨A⟩ := exists_independent_options P (by decide) h4
  have cnt := A.size
  have bound : Fintype.card (Fin m) ≤ Fintype.card A.points := by
    rw [Fintype.card_fin,Fintype.card_coe]
    omega
  obtain ⟨ι⟩ := Function.Embedding.nonempty_of_card_le bound
  let f := ι.trans (Function.Embedding.subtype (· ∈ A.points))
  refine ⟨⟨f,fun i => A.adj _ (ι i).property,fun i => A.fresh _ (ι i).property,?_,?_⟩⟩
  · intro i j pos lo adj
    have := A.lower _ (ι i).property j (by omega) (by omega) adj
    omega
  · intro i j ne
    exact A.independent (ι i).property (ι j).property (fun h => ne (f.injective h))

private theorem contacts {P : Chain G 5} {m : ℕ} (A : Choices P m) (h4 : NoFourCycle G)
    (j : ℕ) (hj : 0<j ∧ j≤5) : ∃ k : Option (Fin m),
    ∀ i,G.Adj (A.v i) (P.vertex j) ↔ k=some i := by
  classical
  by_cases hit : ∃ i,G.Adj (A.v i) (P.vertex j)
  · obtain ⟨a,ha⟩ := hit
    refine ⟨some a,fun i => ⟨fun hi => congrArg some (A.v.injective ?_),?_⟩⟩
    · have diff : P.vertex 0 ≠ P.vertex j := fun h => by
        have := P.inj (Nat.zero_le 5) hj.2 h
        omega
      exact h4 diff (A.edge a) ha.symm (A.edge i) hi.symm
    · intro eq
      exact Option.some.inj eq ▸ ha
  · exact ⟨none,fun i => ⟨fun h => (hit ⟨i,h⟩).elim,fun h => by cases h⟩⟩

private lemma endsDisjoint {P : Chain G 5} {m : ℕ} (A : Choices P m) (h4 : NoFourCycle G)
    (i : Fin m) (h3 : G.Adj (A.v i) (P.vertex 3)) (h5 : G.Adj (A.v i) (P.vertex 5)) : False := by
  have diff : P.vertex 3≠P.vertex 5 := fun e => by
    have := P.inj (by decide : 3≤5) (by decide : 5≤5) e
    omega
  exact A.fresh i 4 (by decide) (h4 diff h3.symm h5.symm
    ((P.edges (by decide : 3≤5) (by decide : 4≤5)).2 (Or.inl rfl))
    ((P.edges (by decide : 5≤5) (by decide : 4≤5)).2 (Or.inr rfl)))

set_option synthInstance.maxSize 2000 in
private theorem nearOrder : ∀ p q r : Option (Fin 4), (∀ i,p=some i → r≠some i) →
    ∃ a b c d : Fin 4, a≠b ∧ a≠c ∧ a≠d ∧ b≠c ∧ b≠d ∧ c≠d ∧
      p≠some a ∧ q≠some a ∧ r≠some a ∧ r≠some b ∧ p≠some c ∧ r≠some c ∧ p≠some d := by
  decide

private theorem farOrder : ∀ p r : Option (Fin 2), (∀ i,p=some i → r≠some i) →
    ∃ a b : Fin 2, a≠b ∧ r≠some a ∧ p≠some b := by decide

/-- At the first endpoint the first of the four choices misses the whole
tail, and the other three can be ordered by contacts at its extreme sites. -/
theorem nearChoices [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (P : Chain G 5) (h4 : NoFourCycle G) (high : 5≤G.indepNeighborsCard (P.vertex 0)) :
    ∃ A : Choices P 4, (∀ j,3≤j → j≤5 → ¬G.Adj (A.v 0) (P.vertex j)) ∧
      ¬G.Adj (A.v 1) (P.vertex 5) ∧ ¬G.Adj (A.v 2) (P.vertex 3) ∧
      ¬G.Adj (A.v 2) (P.vertex 5) ∧ ¬G.Adj (A.v 3) (P.vertex 3) := by
  obtain ⟨A⟩ := chooseEnd P h4 high
  obtain ⟨p,hp⟩ := contacts A h4 3 (by decide)
  obtain ⟨q,hq⟩ := contacts A h4 4 (by decide)
  obtain ⟨r,hr⟩ := contacts A h4 5 (by decide)
  obtain ⟨a,b,c,d,ab,ac,ad,bc,bd,cd,p0,q0,r0,r1,p2,r2,p3⟩ :=
    nearOrder p q r (fun i hi hj => endsDisjoint A h4 i ((hp i).2 hi) ((hr i).2 hj))
  let perm : Fin 4 ↪ Fin 4 := ⟨![a,b,c,d],by
    intro i j e
    fin_cases i <;> fin_cases j <;> simp_all⟩
  let B : Choices P 4 := ⟨perm.trans A.v,fun i => A.edge _,fun i => A.fresh _,fun i => A.miss _,
    fun i j h => A.independent _ _ (perm.injective.ne h)⟩
  refine ⟨B,?_,mt (hr b).1 r1,mt (hp c).1 p2,mt (hr c).1 r2,mt (hp d).1 p3⟩
  intro j lo hi
  interval_cases j
  · exact mt (hp a).1 p0
  · exact mt (hq a).1 q0
  · exact mt (hr a).1 r0

/-- Two choices at the opposite endpoint can miss opposite ends of the tail. -/
theorem farChoices [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (P : Chain G 5) (h4 : NoFourCycle G) (high : 3≤G.indepNeighborsCard (P.vertex 0)) :
    ∃ A : Choices P 2, ¬G.Adj (A.v 0) (P.vertex 5) ∧ ¬G.Adj (A.v 1) (P.vertex 3) := by
  obtain ⟨A⟩ := chooseEnd P h4 high
  obtain ⟨p,hp⟩ := contacts A h4 3 (by decide)
  obtain ⟨r,hr⟩ := contacts A h4 5 (by decide)
  obtain ⟨a,b,ab,ra,pb⟩ := farOrder p r (fun i hi hj => endsDisjoint A h4 i ((hp i).2 hi) ((hr i).2 hj))
  let perm : Fin 2 ↪ Fin 2 := ⟨![a,b],by intro i j e; fin_cases i <;> fin_cases j <;> simp_all⟩
  exact ⟨⟨perm.trans A.v,fun i => A.edge _,fun i => A.fresh _,fun i => A.miss _,
    fun i j h => A.independent _ _ (perm.injective.ne h)⟩,mt (hr a).1 ra,mt (hp b).1 pb⟩

/-- Two independent neighbors of a branch vertex, disjoint and nonadjacent
to its parent, are available when its neighborhood independence is at least three. -/
structure Fork (G : SimpleGraph V) (root parent : V) where
  v : Fin 2 ↪ V
  edge : ∀ i,G.Adj root (v i)
  fresh : ∀ i,v i≠parent
  miss : ∀ i,¬G.Adj parent (v i)
  independent : ¬G.Adj (v 0) (v 1)

theorem getFork [Fintype V] [DecidableEq V] [DecidableRel G.Adj] {z p : V}
    (h4 : NoFourCycle G) (edge : G.Adj z p) (high : 3≤G.indepNeighborsCard z) : Nonempty (Fork G z p) := by
  classical
  let W := (G.neighborFinset z).filter (fun w => w≠p ∧ ¬G.Adj p w)
  have wm (w) : w∈W ↔ G.Adj z w ∧ w≠p ∧ ¬G.Adj p w := by simp [W]
  obtain ⟨⟨I,hI,ind,size⟩,_⟩ := eligible_neighbors_data h4 edge W wm
  obtain ⟨a,b,ha,hb,ab⟩ := Finset.one_lt_card_iff.mp (by omega : 1<I.card)
  let f : Fin 2 ↪ V := ⟨![a,b],by intro i j e; fin_cases i <;> fin_cases j <;> simp_all⟩
  have mem (i) : f i∈I := by fin_cases i <;> assumption
  exact ⟨⟨f,fun i => ((wm _).1 (hI (mem i))).1,fun i => ((wm _).1 (hI (mem i))).2.1,
    fun i => ((wm _).1 (hI (mem i))).2.2,ind ha hb ab⟩⟩

end Wall133.FifthCertificate
