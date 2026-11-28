module

public import Wall133.ShortGirthCertificateData

@[expose] public section

namespace Wall133
open SimpleGraph FourthCertificate

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

private structure Branch (P : Chain G 4) (S : Set V) (x : V) where
  child : Fin 2 → V
  inside : ∀ i, child i ∈ S
  edge : ∀ i, G.Adj x (child i)
  fresh : ∀ i j, j ≤ 4 → child i ≠ P.vertex j
  miss : ∀ i j, (j ≤ 1 ∨ j=4) → ¬ G.Adj (child i) (P.vertex j)
  apart : child 0 ≠ child 1
  independent : ¬G.Adj (child 0) (child 1)

private theorem makeBranch (P : Chain G 4) (h4 : NoFourCycle G) (hc : G.Connected)
    (geo : ∀ i ≤ 4, G.dist (P.vertex 0) (P.vertex i)=i) {x : V} (hx : Good P x)
    {S : Set V} (star : IndependentCoreStar G S x 3) : Nonempty (Branch P S x) := by
  classical
  let R := grow P x hx
  obtain ⟨A,inside,ind⟩ := star.options (P:=R) h4 (by decide)
  have size := A.size
  obtain ⟨a,b,ha,hb,ab⟩ := Finset.one_lt_card_iff.mp (by omega : 1<A.points.card)
  let c : Fin 2 → V := ![a,b]
  have mem (i) : c i∈A.points := by fin_cases i <;> assumption
  refine ⟨⟨c,fun i => inside _ (mem i),fun i => A.adj _ (mem i),
    fun i j hj => A.fresh _ (mem i) (j+1) (by omega),?_,ab,ind ha hb ab⟩⟩
  intro i j hj edge
  rcases hj with lo | rfl
  · have := A.lower _ (mem i) (j+1) (by omega) (by omega) edge
    omega
  · have tr := hc.dist_triangle (u:=P.vertex 0) (v:=x) (w:=P.vertex 4)
    have tr' := hc.dist_triangle (u:=x) (v:=c i) (w:=P.vertex 4)
    rw [geo 4 (by decide),dist_eq_one_iff_adj.mpr hx.1] at tr
    rw [dist_eq_one_iff_adj.mpr (show G.Adj x (c i) from A.adj _ (mem i)),dist_eq_one_iff_adj.mpr edge] at tr'
    omega

private structure Fork (G : SimpleGraph V) (z parent : V) where
  child : Fin 2 → V
  edge : ∀ i, G.Adj (child i) z
  fresh : ∀ i, child i ≠ parent
  miss : ∀ i, ¬G.Adj (child i) parent
  apart : child 0 ≠ child 1
  independent : ¬G.Adj (child 0) (child 1)

omit [Fintype V] in
private theorem makeFork (h4 : NoFourCycle G) {z p : V} (edge : G.Adj z p)
    {S : Set V} (star : IndependentCoreStar G S z 3) : Nonempty (Fork G z p) := by
  classical
  let A := star.points.filter (fun x => x≠p ∧ ¬G.Adj x p)
  have mem {x} : x∈A ↔ x∈star.points ∧ x≠p ∧ ¬G.Adj x p := Finset.mem_filter
  have diff {x} (hx : x∈star.points \ A) : x∈star.points ∧ (x=p ∨ G.Adj x p) := by
    obtain ⟨hx,notA⟩ := Finset.mem_sdiff.mp hx
    exact ⟨hx,by by_contra! h; exact notA (mem.mpr ⟨hx,h⟩)⟩
  have atMost : (star.points \ A).card ≤ 1 := Finset.card_le_one.mpr (by
    intro u hu v hv
    by_contra ne
    obtain ⟨uS,uh|uh⟩ := diff hu <;> obtain ⟨vS,vh|vh⟩ := diff hv
    · exact ne (uh.trans vh.symm)
    · exact star.independent uS vS ne (uh ▸ vh.symm)
    · exact star.independent uS vS ne (vh ▸ uh)
    · exact ne (h4 edge.ne (star.adj u uS) uh.symm (star.adj v vS) vh.symm))
  have card := Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ star.points : A⊆star.points)
  change (star.points \ A).card+A.card=star.points.card at card
  have three := star.card
  obtain ⟨a,b,ha,hb,ab⟩ := Finset.one_lt_card_iff.mp (by omega : 1<A.card)
  let c : Fin 2 → V := ![a,b]
  have hs (i) : c i ∈ A := by fin_cases i <;> assumption
  exact ⟨⟨c,fun i => (star.adj _ (mem.mp (hs i)).1).symm,fun i => (mem.mp (hs i)).2.1,
    fun i => (mem.mp (hs i)).2.2,ab,star.independent (mem.mp ha).1 (mem.mp hb).1 ab⟩⟩

/-- A four-edge geodesic starting at a high vertex of the independence core
admits the local configuration used in the fourth-band certificate. -/
theorem exists_fourth_configuration (P : Chain G 4) (h4 : NoFourCycle G) (hc : G.Connected)
    (geo : ∀ i ≤ 4,G.dist (P.vertex 0) (P.vertex i)=i) (S : Set V)
    (atRoot : IndependentCoreStar G S (P.vertex 0) 4)
    (core : ∀ w∈S, Nonempty (IndependentCoreStar G S w 3)) :
    ∃ f : ℕ → V, f 3=P.vertex 3 ∧ f 4=P.vertex 4 ∧ ∀ t∈inputs,Holds G f t := by
  classical
  obtain ⟨A,inside,ind⟩ := atRoot.options (P:=P) h4 (by decide)
  have good (x) (hx:x∈A.points) : Good P x := by
    refine ⟨A.adj _ hx,A.fresh _ hx,?_⟩
    intro i hi hn e
    have := A.lower x hx i hi hn e
    have dist := hc.dist_triangle (u:=P.vertex 0) (v:=x) (w:=P.vertex i)
    rw [geo i hi,dist_eq_one_iff_adj.mpr (A.adj _ hx),dist_eq_one_iff_adj.mpr e] at dist
    omega
  have size := A.size
  obtain ⟨x,y,z,hx,hy,hz,xy,xz,yz⟩ := Finset.two_lt_card_iff.mp (by omega : 2<A.points.card)
  obtain ⟨X⟩ := makeBranch P h4 hc geo (good x hx) (Classical.choice (core x (inside x hx)))
  obtain ⟨Y⟩ := makeBranch P h4 hc geo (good y hy) (Classical.choice (core y (inside y hy)))
  obtain ⟨Z⟩ := makeBranch P h4 hc geo (good z hz) (Classical.choice (core z (inside z hz)))
  obtain ⟨U⟩ := makeFork h4 (X.edge 0).symm (Classical.choice (core _ (X.inside 0)))
  obtain ⟨W⟩ := makeFork h4 (X.edge 1).symm (Classical.choice (core _ (X.inside 1)))
  let f : ℕ → V
    | 0 => P.vertex 0 | 1 => P.vertex 1 | 2 => P.vertex 2 | 3 => P.vertex 3 | 4 => P.vertex 4
    | 5 => x | 6 => y | 7 => z
    | 8 => X.child 0 | 9 => X.child 1 | 10 => Y.child 0 | 11 => Y.child 1
    | 12 => Z.child 0 | 13 => Z.child 1 | 14 => U.child 0 | 15 => U.child 1
    | 16 => W.child 0 | _ => W.child 1
  refine ⟨f,rfl,rfl,?_⟩
  have gx := good x hx
  have gy := good y hy
  have gz := good z hz
  have noEdge (i j : ℕ) (hi : i≤4) (hj : j≤4) (gap : ¬(i+1=j ∨ j+1=i)) :
      ¬G.Adj (P.vertex i) (P.vertex j) := fun e => gap ((P.edges hi hj).1 e)
  simp only [inputs,List.forall_mem_cons]
  repeat' apply And.intro
  all_goals dsimp only [Holds,f]
  all_goals first
    | assumption
    | exact (P.edges (by decide) (by decide)).2 (by decide)
    | exact noEdge _ _ (by decide) (by decide) (by decide)
    | exact fun _ h => False.elim (List.not_mem_nil h)
    | exact gx.1 | exact gy.1 | exact gz.1
    | exact gx.2.1 _ (by decide) | exact gy.2.1 _ (by decide) | exact gz.2.1 _ (by decide)
    | exact gx.2.2 _ (by decide) (by decide) | exact gy.2.2 _ (by decide) (by decide)
    | exact gz.2.2 _ (by decide) (by decide)
    | exact ind hx hy xy | exact ind hx hz xz | exact ind hy hz yz
    | exact X.edge _ | exact Y.edge _ | exact Z.edge _ | exact U.edge _ | exact W.edge _
    | exact X.fresh _ _ (by decide) | exact Y.fresh _ _ (by decide) | exact Z.fresh _ _ (by decide)
    | exact U.fresh _ | exact W.fresh _
    | exact X.miss _ _ (by decide) | exact Y.miss _ _ (by decide) | exact Z.miss _ _ (by decide)
    | exact U.miss _ | exact W.miss _
    | exact X.apart | exact Y.apart | exact Z.apart | exact U.apart | exact W.apart
    | exact X.independent | exact Z.independent
    | exact U.independent | exact W.independent

end Wall133
