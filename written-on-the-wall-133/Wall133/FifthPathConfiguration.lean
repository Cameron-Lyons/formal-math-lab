import Wall133.FifthBranches

namespace Wall133.FifthCertificate
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A five-edge induced path with five independent neighbors at its starting
vertex realizes the certificate if every vertex has three independent neighbors. -/
theorem exists_configuration (P : Chain G 5) (h4 : NoFourCycle G)
    (high : 5≤G.indepNeighborsCard (P.vertex 0)) (hmin : ∀ v,3≤G.indepNeighborsCard v) :
    ∃ f : ℕ → V, ∀ t∈inputs,Holds G f t := by
  classical
  obtain ⟨A,good,n15,n23,n25,n33⟩ := nearChoices P h4 high
  obtain ⟨B,n00,n12⟩ := farChoices P.reverse h4 (hmin _)
  obtain ⟨X⟩ := getFork h4 (A.edge 0).symm (hmin _)
  obtain ⟨Y⟩ := getFork h4 (A.edge 1).symm (hmin _)
  obtain ⟨Z⟩ := getFork h4 (A.edge 2).symm (hmin _)
  obtain ⟨T⟩ := getFork h4 (B.edge 0).symm (hmin _)
  let f : ℕ → V
    | 0 => P.vertex 0 | 1 => P.vertex 1 | 2 => P.vertex 2 | 3 => P.vertex 3
    | 4 => P.vertex 4 | 5 => P.vertex 5 | 6 => A.v 0 | 7 => A.v 1
    | 8 => A.v 2 | 9 => A.v 3 | 10 => B.v 0 | 11 => B.v 1
    | 12 => X.v 0 | 13 => X.v 1 | 14 => Y.v 0 | 15 => Y.v 1
    | 16 => Z.v 0 | 17 => Z.v 1 | 18 => T.v 0 | _ => T.v 1
  have noEdge (i j : ℕ) (hi : i≤5) (hj : j≤5) (gap : ¬(i+1=j ∨ j+1=i)) :
      ¬G.Adj (P.vertex i) (P.vertex j) := fun e => gap ((P.edges hi hj).1 e)
  have separate (i j : ℕ) (hi : i≤5) (hj : j≤5) (ne : i≠j) : P.vertex i≠P.vertex j :=
    fun h => ne (P.inj hi hj h)
  have reverseIndex (j : ℕ) (hj : j≤5) : P.reverse.vertex (5-j)=P.vertex j := by
    change P.vertex (5-(5-j))=P.vertex j
    rw [show 5-(5-j)=j by omega]
  have farFresh (j i) (hj : j≤5) : P.vertex j≠B.v i := by
    rw [←reverseIndex j hj]
    exact (B.fresh i _ (by omega)).symm
  have farMiss (j i) (lo : 3≤j) (hi : j≤4) : ¬G.Adj (P.vertex j) (B.v i) := by
    rw [←reverseIndex j (by omega)]
    exact mt Adj.symm (B.miss i _ (by omega) (by omega))
  refine ⟨f,?_⟩
  simp only [inputs,List.forall_mem_cons]
  repeat' apply And.intro
  all_goals dsimp only [Holds,FourthCertificate.Holds,f]
  all_goals first
    | assumption
    | exact (P.edges (by decide) (by decide)).2 (by decide)
    | exact noEdge _ _ (by decide) (by decide) (by decide)
    | exact separate _ _ (by decide) (by decide) (by decide)
    | exact A.edge _ | exact B.edge _ | exact X.edge _ | exact Y.edge _ | exact Z.edge _ | exact T.edge _
    | exact (A.fresh _ _ (by decide)).symm | exact farFresh _ _ (by decide)
    | exact A.v.injective.ne (by decide) | exact B.v.injective.ne (by decide)
    | exact X.v.injective.ne (by decide) | exact Y.v.injective.ne (by decide)
    | exact Z.v.injective.ne (by decide) | exact T.v.injective.ne (by decide)
    | exact (X.fresh _).symm | exact (Y.fresh _).symm | exact (Z.fresh _).symm | exact (T.fresh _).symm
    | exact X.miss _ | exact Y.miss _ | exact Z.miss _ | exact T.miss _
    | exact mt Adj.symm (A.miss _ _ (by decide) (by decide)) | exact farMiss _ _ (by decide) (by decide)
    | exact good _ (by decide) (by decide)
    | exact A.independent _ _ (by decide) | exact B.independent _ _ (by decide)
    | exact X.independent | exact Y.independent | exact Z.independent | exact T.independent
    | exact fun _ h => False.elim (List.not_mem_nil h)

end Wall133.FifthCertificate
