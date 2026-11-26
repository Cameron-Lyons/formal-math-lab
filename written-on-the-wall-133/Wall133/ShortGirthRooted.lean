module

public import Wall133.ShortGirthCore
public import Wall133.ShortGirthSingleTail

@[expose] public section

namespace Wall133
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {n : ℕ}

/-- If each clean branch has at least n−1 independent neighbors, one of
two branches can reroute around the first two vertices of an n-edge path. -/
theorem two_independent_near_saturated_branches (P : Chain G n) (hn : 4≤n) (h4 : NoFourCycle G)
    {x y : V} (hx : Good P x) (hy : Good P y) (hxy : x≠y) (nxy : ¬G.Adj x y)
    (dx : n-1≤G.indepNeighborsCard x) (dy : n-1≤G.indepNeighborsCard y) : n+3≤G.path := by
  classical
  by_contra short
  have doubleContact {v w : V} (hv : Good P v) (hw : Good P w) (hvw : v≠w) (nvw : ¬G.Adj v w)
      (hd : n-1≤G.indepNeighborsCard v) :
      ∃ b, G.Adj v b ∧ G.Adj (P.vertex 2) b ∧ G.Adj (P.vertex n) b := by
    let R := grow P v hv
    obtain ⟨A⟩ := exists_contact_options R (by omega) h4 (Or.inl hd)
    have card := A.size
    have one : ∃ b∈A.points,∀ i,3 ≤ i → i < n → ¬G.Adj b (P.vertex i) := by
      by_contra! bad
      choose idx lo hi a using fun w : A.points => bad w.val w.property
      let f (w : A.points) : Fin (n-3) := ⟨idx w-3,by have := lo w; have := hi w; omega⟩
      have inj : Function.Injective f := by
        intro w z he
        have eq := congrArg Fin.val he
        change idx w-3=idx z-3 at eq
        have ee : idx w=idx z := by have := lo w; have := lo z; omega
        exact Subtype.ext (h4 (hv.2.1 _ (Nat.le_of_lt (hi w))) (A.adj _ w.property) (a w).symm
          (A.adj _ z.property) (ee ▸ (a z).symm))
      have cnt : A.points.card ≤ n-3 := by simpa using Fintype.card_le_of_injective f inj
      omega
    obtain ⟨b,hb,miss⟩ := one
    have fb (i) (hi : i≤n) := A.fresh _ hb (i+1) (show i+1≤n+1 by omega)
    have ends (i) (hi : i≤n) (ha : G.Adj b (P.vertex i)) : i=2 ∨ i=n := by
      have lo := A.lower _ hb (i+1) (by omega) (by omega) ha
      by_contra! notends
      exact miss i (by omega) (by omega) ha
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
  obtain ⟨b,xb,b2,bn⟩ := doubleContact hx hy hxy nxy dx
  obtain ⟨c,yc,c2,cn⟩ := doubleContact hy hx hxy.symm (fun h => nxy h.symm) dy
  have ne : P.vertex 2≠P.vertex n := fun e => by have := P.inj (by omega) le_rfl e; omega
  have bc := h4 ne b2 bn c2 cn
  have be := h4 hxy xb (bc ▸ yc) hx.1.symm hy.1.symm
  rw [be] at b2
  have := (P.edges (by omega : 2≤n) (Nat.zero_le _)).1 b2
  omega

theorem min_neighborhood_independence_add_four (h4 : NoFourCycle G) {d : ℕ} (hd : 3≤d)
    (hmin : ∀ x,d≤G.indepNeighborsCard x) (a : V) (ha : d+2≤G.indepNeighborsCard a) :
    d+4≤G.path := by
  classical
  obtain ⟨u,p,hp,plen⟩ := exists_long_chordless_ending h4 (by omega) hmin a
  let P := (chainOfChordless p hp).reverse
  have root : P.vertex 0=a := by simp [P,Chain.reverse,chainOfChordless]
  obtain ⟨A⟩ := exists_independent_options P (by omega) h4
  have hgood := options_good_count P h4 A (D:=2) (fun w hw i hi ip h => A.lower _ hw i hi ip h)
  have hw := A.size
  have rα := congrArg (fun v => G.indepNeighborsCard v) root
  let good := A.points.filter (Good P)
  change A.points.card ≤ good.card+(p.length-2) at hgood
  have base := P.length_le
  by_contra! short
  have pcase : p.length=d+1 ∨ p.length=d+2 := by omega
  rcases pcase with eq|eq
  · obtain ⟨x,y,hx,hy,hxy⟩ := Finset.one_lt_card_iff.mp (by omega : 1<good.card)
    obtain ⟨xA,xg⟩ := Finset.mem_filter.mp hx
    obtain ⟨yA,yg⟩ := Finset.mem_filter.mp hy
    have := two_independent_near_saturated_branches P (by omega) h4 xg yg hxy (A.independent xA yA hxy)
      (by have := hmin x; omega) (by have := hmin y; omega)
    omega
  · obtain ⟨x,hx⟩ := Finset.card_pos.mp (by omega : 0<good.card)
    have := (grow P x (Finset.mem_filter.mp hx).2).length_le
    omega

end Wall133
