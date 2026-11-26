module

public import Wall133.ShortGirthStars
public import Wall133.ShortGirthSeven

@[expose] public section

namespace Wall133
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

private structure Row (P : Chain G 3) (x : V) where
  clean : V
  blocked : V
  adj_clean : G.Adj x clean
  adj_blocked : G.Adj x blocked
  off_clean : Off P clean (fun _ => False)
  fresh_blocked : ∀ i ≤ 3, blocked ≠ P.vertex i
  hit : G.Adj blocked (P.vertex 2)
  private_of_miss : ¬G.Adj blocked (P.vertex 3) → Off P blocked (·=2)

private theorem simplicial_row (P : Chain G 3) (h4 : NoFourCycle G) {S : Set V} {x : V}
    (hx : Good P x) (xs : x∈S) (core : ∀ w∈S, Nonempty (IndependentCoreStar G S w 3))
    (tip : ∀ w,G.Adj w (P.vertex 3) → w ≠ P.vertex 2 → G.Adj w (P.vertex 2))
    (short : ¬7 ≤ G.path) : Nonempty (Row P x) := by
  classical
  let R := grow P x hx
  have root : R.vertex 0 = x := rfl
  obtain ⟨star⟩ := core x xs
  obtain ⟨A,inside,ind⟩ := star.options (P := R) h4 (by decide)
  have size := A.size
  obtain ⟨z,w,hz,hw,ne⟩ := Finset.one_lt_card_iff.mp (by omega : 1<A.points.card)
  have fresh (c) (h:c∈A.points) (i) (hi:i≤3) : c≠P.vertex i := A.fresh _ h (i+1) (by omega)
  have low (c) (h:c∈A.points) (i) (hi:i≤3) (hit:G.Adj c (P.vertex i)) : 2 ≤ i := by
    have := A.lower _ h (i+1) (by omega) (by omega) hit
    omega
  have hit (c) (h:c∈A.points) (no : ¬Good R c) : G.Adj c (P.vertex 2) := by
    by_contra miss
    apply no
    refine ⟨A.adj _ h,A.fresh _ h,?_⟩
    rintro (_|i) hi hpos hadj
    · contradiction
    · have lo := low c h i (by omega) hadj
      rcases (show i=2 ∨ i=3 by omega) with rfl|rfl
      · exact miss hadj
      · exact miss (tip c hadj (fresh c h _ (by decide)))
  have make (v c) (hv : v∈A.points) (hc : c∈A.points) (good : Good R v)
      (hh : G.Adj c (P.vertex 2)) : Nonempty (Row P x) := by
    refine ⟨⟨v,c,A.adj _ hv,A.adj _ hc,⟨fresh v hv,?_⟩,fresh c hc,hh,?_⟩⟩
    · intro i hi
      exact iff_false_intro (good.2.2 (i+1) (by omega) (by omega))
    · intro no3
      refine ⟨fresh c hc,?_⟩
      intro i hi
      constructor
      · intro e
        have := low c hc i hi e
        by_contra ne
        exact no3 ((show i=3 by omega) ▸ e)
      · rintro rfl; exact hh
  by_cases gz : Good R z
  · by_cases gw : Good R w
    · obtain ⟨sz⟩ := core z (inside z hz)
      obtain ⟨sw⟩ := core w (inside w hw)
      exact (short (seven_of_two_low_rows R h4 gz gw ne (ind hz hw ne)
        (Or.inl sz.ambient) (Or.inl sw.ambient))).elim
    · exact make z w hz hw gz (hit _ hw gw)
  · by_cases gw : Good R w
    · exact make w z hw hz gw (hit _ hz gz)
    · exact (ne (h4 (hx.2.1 2 (by decide)) (A.adj _ hz) (hit _ hz gz).symm
        (A.adj _ hw) (hit _ hw gw).symm)).elim

omit [DecidableRel G.Adj] in
private theorem cross_path (P : Chain G 3) (h4 : NoFourCycle G) {x y : V}
    (hx : Good P x) (hy : Good P y) (hne : x≠y) (nxy : ¬G.Adj x y)
    (r : Row P x) (s : Row P y) (miss : ¬G.Adj r.blocked (P.vertex 3))
    (cross : ¬G.Adj r.blocked s.clean) : 7 ≤ G.path := by
  have ax := offGood hx
  have ay := offGood hy
  have ab := r.private_of_miss miss
  have az := s.off_clean
  have nby : ¬G.Adj y r.blocked := fun e =>
    r.fresh_blocked 0 (by decide) (h4 hne r.adj_blocked e hx.1.symm hy.1.symm)
  have nzx : ¬G.Adj x s.clean := fun e =>
    az.fresh 0 (by decide) (h4 hne e s.adj_clean hx.1.symm hy.1.symm)
  let f : Fin 7 → V := ![P.vertex 3,P.vertex 2,r.blocked,x,P.vertex 0,y,s.clean]
  have edges (i j : Fin 7) : G.Adj (f i) (f j) ↔ i.val+1=j.val ∨ j.val+1=i.val := by
    fin_cases i <;> fin_cases j <;> dsimp [f]
    all_goals first
      | rw [P.edges (by decide) (by decide)]; decide
      | rw [ab.contact _ (by decide)]; decide
      | rw [az.contact _ (by decide)]; decide
      | rw [ax.contact _ (by decide)]; decide
      | rw [ay.contact _ (by decide)]; decide
      | rw [G.adj_comm,ab.contact _ (by decide)]; decide
      | rw [G.adj_comm,az.contact _ (by decide)]; decide
      | rw [G.adj_comm,ax.contact _ (by decide)]; decide
      | rw [G.adj_comm,ay.contact _ (by decide)]; decide
      | simp only [SimpleGraph.irrefl,r.adj_blocked,r.adj_blocked.symm,s.adj_clean,s.adj_clean.symm,
          nby,mt Adj.symm nby,nzx,mt Adj.symm nzx,cross,mt Adj.symm cross,
          nxy,mt Adj.symm nxy,true_iff,false_iff]; decide
  apply path_bound_of_indices f _ edges
  have twins : ∀ a b : Fin 7, (∀ k : Fin 7,(a.val+1=k.val ∨ k.val+1=a.val) ↔
      (b.val+1=k.val ∨ k.val+1=b.val)) → a=b := by decide
  intro i j eq
  apply twins i j
  intro k
  rw [← edges,← edges,eq]

/-- A three-edge geodesic from a vertex with four independent core neighbors
can be extended to an induced seven-vertex path even if its far endpoint
has only one neighbor, or two adjacent neighbors. -/
theorem seven_of_simplicial_end (P : Chain G 3) (h4 : NoFourCycle G) (hc : G.Connected)
    (geo : ∀ i ≤ 3,G.dist (P.vertex 0) (P.vertex i)=i) (S : Set V)
    (atRoot : IndependentCoreStar G S (P.vertex 0) 4)
    (core : ∀ w∈S, Nonempty (IndependentCoreStar G S w 3))
    (simplicial : ∀ z,G.Adj z (P.vertex 3) → z≠P.vertex 2 → G.Adj z (P.vertex 2)) :
    7 ≤ G.path := by
  classical
  by_contra short
  obtain ⟨A,inside,ind⟩ := atRoot.options (P := P) h4 (by decide)
  have good (x) (hx:x∈A.points) : Good P x := by
    refine ⟨A.adj _ hx,A.fresh _ hx,?_⟩
    intro i hi hn e
    have := A.lower x hx i hi hn e
    have dist := hc.dist_triangle (u := P.vertex 0) (v := x) (w := P.vertex i)
    rw [geo i hi,dist_eq_one_iff_adj.mpr (A.adj _ hx), dist_eq_one_iff_adj.mpr e] at dist
    omega
  let row (x : A.points) := Classical.choice
    (simplicial_row P h4 (good _ x.property) (inside _ x.property) core simplicial short)
  have different {x y:A.points} (hne:x≠y) : (row x).blocked ≠ (row y).blocked := by
    intro eq
    have ne : x.val≠y.val := fun e => hne (Subtype.ext e)
    have := h4 ne (row x).adj_blocked (eq ▸ (row y).adj_blocked)
      (A.adj _ x.property).symm (A.adj _ y.property).symm
    exact (row x).fresh_blocked 0 (by decide) this
  let missed := (Finset.univ : Finset A.points).filter (fun x => ¬G.Adj (row x).blocked (P.vertex 3))
  have cardHit : (Finset.univ.filter (fun x:A.points => G.Adj (row x).blocked (P.vertex 3))).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro x hx y hy
    by_contra ne
    apply different ne
    exact h4 (fun e => by have := P.inj (i:=2) (j:=3) (by decide) (by decide) e; omega)
      (row x).hit.symm (Finset.mem_filter.mp hx).2.symm (row y).hit.symm (Finset.mem_filter.mp hy).2.symm
  have three := A.size
  have cards := Finset.card_filter_add_card_filter_not (s:=Finset.univ)
    (fun x:A.points => G.Adj (row x).blocked (P.vertex 3))
  change _+missed.card=Finset.univ.card at cards
  rw [Finset.card_univ,Fintype.card_coe] at cards
  obtain ⟨x,y,hx,hy,ne⟩ := Finset.one_lt_card_iff.mp (by omega : 1<missed.card)
  have third : ∃ z:A.points,z≠x ∧ z≠y := by
    by_contra! absent
    have sub : (Finset.univ : Finset A.points) ⊆ {x,y} := by
      intro z _
      by_cases e : z=x
      · simp [e]
      · simp [absent z e]
    have := (Finset.card_le_card sub).trans (Finset.card_le_two (a:=x) (b:=y))
    simp only [Finset.card_univ,Fintype.card_coe] at this
    omega
  obtain ⟨z,zx,zy⟩ := third
  have hits {w:A.points} (hw:w∈missed) (ne:w≠z) : G.Adj (row w).blocked (row z).clean := by
    by_contra e
    have valne : w.val≠z.val := fun h => ne (Subtype.ext h)
    exact short (cross_path P h4 (good _ w.property) (good _ z.property) valne
      (ind w.property z.property valne) (row w) (row z) (Finset.mem_filter.mp hw).2 e)
  have eq := h4 (x := P.vertex 2) (y := (row z).clean) ((row z).off_clean.fresh 2 (by decide)).symm
    (row x).hit.symm (hits hx (Ne.symm zx)).symm (row y).hit.symm (hits hy (Ne.symm zy)).symm
  exact different ne eq

end Wall133
