import Wall133.OddIndependenceCore
import Wall133.ShortGirthRooted

namespace Wall133
open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- Rerouting the near end around position two keeps the specified far endpoint. -/
private theorem reroute_ending {n : ℕ} (P : Chain G n) (hn : 2≤n) (h4 : NoFourCycle G)
    {x y b : V} (hx : Good P x) (hy : Good P y) (xy : x≠y) (nxy : ¬G.Adj x y)
    (xb : G.Adj x b) (ob : Off P b (·=2)) :
    ∃ R : Chain G (n+2), R.vertex (n+2)=P.vertex n := by
  let f : ℕ → V
    | 0 => y | 1 => P.vertex 0 | 2 => x | 3 => b | j+4 => P.vertex (j+2)
  have nyb : ¬G.Adj y b := fun e =>
    ob.fresh 0 (by omega) (h4 xy xb e hx.1.symm hy.1.symm)
  have ax := offGood hx
  have ay := offGood hy
  have edges (i j : ℕ) (hi : i≤n+2) (hj : j≤n+2) :
      G.Adj (f i) (f j) ↔ i+1=j ∨ j+1=i := by
    rcases i with _|_|_|_|i <;> rcases j with _|_|_|_|j
    all_goals dsimp [f]
    all_goals first
      | rw [P.edges (by omega) (by omega)]; omega
      | rw [ob.contact _ (by omega)]; omega
      | rw [ax.contact _ (by omega)]; omega
      | rw [ay.contact _ (by omega)]; omega
      | rw [G.adj_comm,ob.contact _ (by omega)]; omega
      | rw [G.adj_comm,ax.contact _ (by omega)]; omega
      | rw [G.adj_comm,ay.contact _ (by omega)]; omega
      | simp [xb,xb.symm,nyb,mt Adj.symm nyb,nxy,mt Adj.symm nxy]
  have separate (i j : ℕ) (lt : i<j) (hj : j≤n+2) (eq : f i=f j) : False := by
    have row (k : ℕ) (hk : k≤n+2) : (i+1=k ∨ k+1=i) ↔ (j+1=k ∨ k+1=j) := by
      rw [←edges i k (by omega) hk,←edges j k hj hk,eq]
    by_cases lo : 0 < i
    · have := row (i-1) (by omega); omega
    · have := row 1 (by omega); have := row 3 (by omega); omega
  refine ⟨⟨f,fun {i j} hi hj eq => by
    rcases lt_trichotomy i j with h|h|h
    · exact (separate i j h hj eq).elim
    · exact h
    · exact (separate j i h hi eq.symm).elim, fun {_ _} hi hj => edges _ _ hi hj⟩,?_⟩
  change f (n+2)=P.vertex n
  rw [show n+2=(n-2)+4 by omega]
  change P.vertex (n-2+2)=_
  rw [Nat.sub_add_cancel hn]

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- In a four-cycle-free graph of minimum neighborhood independence d, an
independent set of equality vertices guarantees a rooted path of d+2 edges. -/
theorem exists_rooted_chain_of_independent_low (h4 : NoFourCycle G) {d : ℕ} (hd : 2≤d)
    (hmin : ∀ u,d≤G.indepNeighborsCard u)
    (boost : ∀ u v,G.Adj u v → G.indepNeighborsCard u=d → d<G.indepNeighborsCard v)
    (a : V) : ∃ P : Chain G (d+2), P.vertex (d+2)=a := by
  classical
  obtain ⟨u,p,hp,plen⟩ := exists_long_chordless_ending h4 hd hmin a
  let T := chainOfChordless p hp
  let P : Chain G (d+1) := ⟨fun i => T.vertex (p.length-(d+1)+i),
    fun {i j} hi hj e => by have := T.inj (by omega) (by omega) e; omega,
    fun {i j} hi hj => by rw [T.edges (by omega) (by omega)]; omega⟩
  have endP : P.vertex (d+1)=a := by
    change p.getVert (p.length-(d+1)+(d+1))=a
    rw [Nat.sub_add_cancel plen,Walk.getVert_length]
  by_contra short
  have noGood (w) : ¬Good P w := fun hw => short ⟨grow P w hw,endP⟩
  obtain ⟨A⟩ := exists_independent_options P (by omega) h4
  have count := options_good_count P h4 A (D:=2) (fun w hw i hi pos h => A.lower _ hw i hi pos h)
  have size := A.size
  have empty : A.points.filter (Good P)=∅ := Finset.filter_eq_empty_iff.mpr (fun w _ => noGood w)
  rw [empty,Finset.card_empty] at count
  have low : G.indepNeighborsCard (P.vertex 0)=d := by have := hmin (P.vertex 0); omega
  let Q : Chain G d := ⟨fun i => P.vertex (i+1),fun {i j} hi hj e => by
    have := P.inj (by omega) (by omega) e; omega,fun {i j} hi hj => by rw [P.edges (by omega) (by omega)]; omega⟩
  have high : d<G.indepNeighborsCard (Q.vertex 0) :=
    boost _ _ ((P.edges (by omega : 0≤d+1) (by omega : 1≤d+1)).2 (Or.inl rfl)) low
  obtain ⟨B⟩ := exists_independent_options Q hd h4
  have goodCount := options_good_count Q h4 B (D:=2) (fun w hw i hi pos h => B.lower _ hw i hi pos h)
  have sz := B.size
  obtain ⟨x,y,hx,hy,xy⟩ := Finset.one_lt_card_iff.mp (by omega : 1<(B.points.filter (Good Q)).card)
  obtain ⟨xB,gx⟩ := Finset.mem_filter.mp hx
  obtain ⟨yB,gy⟩ := Finset.mem_filter.mp hy
  let R := grow Q x gx
  obtain ⟨C⟩ := exists_independent_options R (by omega) h4
  have nx : d≤G.indepNeighborsCard (R.vertex 0) := hmin x
  have szC := C.size
  have leave : ∃ b∈C.points,∀ j,3≤j → j≤d → ¬G.Adj b (Q.vertex j) := by
    by_contra! all
    choose idx ilo ihi hit using fun b:C.points => all b.val b.property
    let f (b:C.points) : Fin (d-2) := ⟨idx b-3,by have := ilo b; have := ihi b; omega⟩
    have inj : Function.Injective f := by
      intro b c eq
      have ident := congrArg Fin.val eq
      change idx b-3=idx c-3 at ident
      have same : idx b=idx c := by have := ilo b; have := ilo c; omega
      exact Subtype.ext (h4 (gx.2.1 _ (ihi b)) (C.adj _ b.property) (hit b).symm
        (C.adj _ c.property) (same ▸ (hit c).symm))
    have cnt : C.points.card≤d-2 := by simpa using Fintype.card_le_of_injective f inj
    omega
  obtain ⟨b,hb,miss⟩ := leave
  have only (i) (hi : i≤d) (e : G.Adj b (Q.vertex i)) : i=2 := by
    have := C.lower _ hb (i+1) (by omega) (by omega) e
    by_contra ne
    exact miss i (by omega) hi e
  have e2 : G.Adj b (Q.vertex 2) := by
    by_contra m
    have good : Good R b := by
      refine ⟨C.adj _ hb,C.fresh _ hb,?_⟩
      rintro (_|i) hi hpos e
      · exact hpos rfl
      · exact m (only i (by omega) e ▸ e)
    exact short ⟨grow R b good,endP⟩
  obtain ⟨L,hL⟩ := reroute_ending Q hd h4 gx gy xy (B.independent xB yB xy) (C.adj _ hb)
    ⟨fun i hi => C.fresh _ hb (i+1) (by omega),fun i hi => ⟨only i hi,fun e => e ▸ e2⟩⟩
  exact short ⟨L,hL.trans endP⟩

/-- A vertex with d+3 mutually independent higher neighbors supplies two
clean extensions to the rooted chain and gives another two path vertices. -/
theorem path_of_high_independent_neighbors (h4 : NoFourCycle G) {d : ℕ} (hd : 2≤d)
    (hmin : ∀ u,d≤G.indepNeighborsCard u)
    (boost : ∀ u v,G.Adj u v → G.indepNeighborsCard u=d → d<G.indepNeighborsCard v)
    (a : V) (star : IndependentCoreStar G {u | d<G.indepNeighborsCard u} a (d+3)) :
    d+5≤G.path := by
  classical
  obtain ⟨L,root⟩ := exists_rooted_chain_of_independent_low h4 hd hmin boost a
  let P := L.reverse
  have anchor : P.vertex 0=a := by simpa [P,Chain.reverse] using root
  obtain ⟨A,inside,ind⟩ := (anchor ▸ star : IndependentCoreStar G _ (P.vertex 0) (d+3)).options h4 (by omega)
  let good := A.points.filter (Good P)
  let bad := A.points.filter (fun w => ¬Good P w)
  have mem (w : bad) : w.val∈A.points := (Finset.mem_filter.mp w.property).1
  have contact (w:bad) : ∃ i≤d+2,i≠0 ∧ G.Adj w.val (P.vertex i) := by
    by_contra! none
    exact (Finset.mem_filter.mp w.property).2 ⟨A.adj _ (mem w),A.fresh _ (mem w),none⟩
  choose idx hi pos hit using contact
  have lo (w:bad) : 3 ≤ idx w := A.lower _ (mem w) _ (hi w) (pos w) (hit w)
  let f (w:bad) : Fin d := ⟨idx w-3,by have := hi w; have := lo w; omega⟩
  have inj : Function.Injective f := by
    intro w z eq
    have e := congrArg Fin.val eq
    change idx w-3=idx z-3 at e
    have same : idx w=idx z := by have := lo w; have := lo z; omega
    have ne : P.vertex 0≠P.vertex (idx w) := fun h => pos w ((P.inj (Nat.zero_le _) (hi w) h).symm)
    exact Subtype.ext (h4 ne (A.adj _ (mem w)) (hit w).symm (A.adj _ (mem z)) (same ▸ (hit z).symm))
  have cap : bad.card ≤ d := by simpa using Fintype.card_le_of_injective f inj
  have cnt := Finset.card_filter_add_card_filter_not (s:=A.points) (Good P)
  change good.card+bad.card=A.points.card at cnt
  have size := A.size
  obtain ⟨x,y,hx,hy,xy⟩ := Finset.one_lt_card_iff.mp (by omega : 1<good.card)
  obtain ⟨xA,xg⟩ := Finset.mem_filter.mp hx
  obtain ⟨yA,yg⟩ := Finset.mem_filter.mp hy
  have xh : d<G.indepNeighborsCard x := inside x xA
  have yh : d<G.indepNeighborsCard y := inside y yA
  exact two_independent_near_saturated_branches P (by omega) h4 xg yg xy (ind xA yA xy)
    (by omega) (by omega)

/-- In the fifth floor band a nonempty induced core of minimum neighborhood
independence three, with independent equality vertices and six independent
higher neighbors at one vertex, settles radius three. -/
theorem radius_add_five_of_high_star (h4 : NoFourCycle G) (S : Finset V) (hr : G.radius.toNat≤3)
    (hmin : ∀ u:S,3≤(G.induce (S:Set V)).indepNeighborsCard u)
    (boost : ∀ u v:S,(G.induce (S:Set V)).Adj u v →
      (G.induce (S:Set V)).indepNeighborsCard u=3 → 3<(G.induce (S:Set V)).indepNeighborsCard v)
    (a : S) (star : IndependentCoreStar (G.induce (S:Set V))
      {u | 3<(G.induce (S:Set V)).indepNeighborsCard u} a 6) : G.radius.toNat+5≤G.path := by
  let H := G.induce (S:Set V)
  have four : NoFourCycle H := fun {x y _ _} ne hx hy hx' hy' =>
    Subtype.ext (h4 (x:=x.val) (y:=y.val) (fun e => ne (Subtype.ext e)) hx hy hx' hy')
  have bound := path_of_high_independent_neighbors (G:=H) four (d:=3) (by decide) hmin boost a star
  have mono : H.path≤G.path := G.path_induce_le (S:Set V)
  omega

/-- A short path forces enough minimum vertices to absorb the excess
neighborhood independence over d+2. Each triangle-free minimum vertex
can contribute to the neighborhood of just d higher vertices. -/
theorem independence_sum_of_short_odd_core (h4 : NoFourCycle G) {d : ℕ} (hd : 2≤d)
    (hmin : ∀ u,d≤G.indepNeighborsCard u)
    (boost : ∀ u v,G.Adj u v → G.indepNeighborsCard u=d → d<G.indepNeighborsCard v)
    (degree : ∀ u,G.indepNeighborsCard u=d → G.degree u=d) (short : G.path<d+5) :
    ∑ u,G.indepNeighborsCard u ≤ (d+2)*Fintype.card V+
      (d-2)*(Finset.univ.filter (fun u => G.indepNeighborsCard u=d)).card := by
  classical
  let L := Finset.univ.filter (fun u => G.indepNeighborsCard u=d)
  let H := (Lᶜ : Finset V)
  let numLow (u : V) := (Finset.bipartiteAbove G.Adj L u).card
  have low {u} : u∈L ↔ G.indepNeighborsCard u=d := by simp [L]
  have bound (u : V) : G.indepNeighborsCard u ≤ d+2+numLow u := by
    let J := G.induce (G.neighborSet u)
    obtain ⟨I,hI⟩ := exists_isNIndepSet_indepNum (G:=J)
    let emb := Function.Embedding.subtype (·∈G.neighborSet u)
    let A := I.map emb
    let B := A.filter (fun v => d<G.indepNeighborsCard v)
    have adj {v} (hv : v∈A) : G.Adj u v := by
      obtain ⟨w,_,rfl⟩ := Finset.mem_map.mp hv
      exact w.property
    have independent : G.IsIndepSet (A : Set V) := by
      intro v hv w hw ne
      obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp hv
      obtain ⟨b,hb,rfl⟩ := Finset.mem_map.mp hw
      exact hI.isIndepSet ha hb (fun e => ne (congrArg emb e))
    have size : A.card=G.indepNeighborsCard u := by change (I.map emb).card=J.indepNum; rw [Finset.card_map,hI.card_eq]
    have small : B.card≤d+2 := by
      by_contra! big
      apply short.not_ge
      apply path_of_high_independent_neighbors h4 hd hmin boost u
      refine ⟨B,by omega,?_,fun _ hv => (Finset.mem_filter.mp hv).2,fun _ hv => adj (Finset.mem_filter.mp hv).1⟩
      intro v hv w hw ne
      exact independent (Finset.mem_filter.mp hv).1 (Finset.mem_filter.mp hw).1 ne
    have rest : A \ B ⊆ Finset.bipartiteAbove G.Adj L u := by
      intro v hv
      obtain ⟨av,nb⟩ := Finset.mem_sdiff.mp hv
      apply Finset.mem_filter.mpr
      refine ⟨low.mpr ?_,adj av⟩
      have nh : ¬d<G.indepNeighborsCard v := fun h => nb (Finset.mem_filter.mpr ⟨av,h⟩)
      exact (hmin v).antisymm' (by omega)
    have card := Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ A : B⊆A)
    change (A \ B).card+B.card=A.card at card
    have cnt : (A \ B).card≤numLow u := Finset.card_le_card rest
    omega
  have neighbors (u : V) : Finset.bipartiteBelow G.Adj Finset.univ u=G.neighborFinset u := by
    ext w
    simp [G.adj_comm]
  have charge : ∑ u,numLow u = d*L.card := by
    change ∑ u,(Finset.bipartiteAbove G.Adj L u).card=_
    rw [Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow]
    calc
      _ = ∑ _u∈L,d := Finset.sum_congr rfl (fun u hu => by
        rw [neighbors u,G.card_neighborFinset_eq_degree,degree _ (low.mp hu)])
      _ = _ := by simp [Nat.mul_comm]
  have subsetSum := Finset.sum_le_univ_sum_of_nonneg (s:=H) (f:=numLow) (fun _ => Nat.zero_le _)
  have highSum := Finset.sum_le_sum (s:=H) (fun u _ => bound u)
  rw [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul] at highSum
  change (∑ u∈H,G.indepNeighborsCard u) ≤ H.card*(d+2)+∑ u∈H,numLow u at highSum
  have lowSum : ∑ u∈L,G.indepNeighborsCard u=d*L.card := by
    calc
      _ = ∑ _u∈L,d := Finset.sum_congr rfl (fun _ hu => low.mp hu)
      _ = _ := by simp [Nat.mul_comm]
  have full := Finset.sum_add_sum_compl L (fun u => G.indepNeighborsCard u)
  change (∑ u∈L,G.indepNeighborsCard u)+(∑ u∈H,G.indepNeighborsCard u)=_ at full
  have sumCards : H.card+L.card=Fintype.card V := Finset.card_compl_add_card L
  change _ ≤ (d+2)*Fintype.card V+(d-2)*L.card
  calc
    _ ≤ H.card*(d+2)+d*L.card+d*L.card := by omega
    _ = _ := by
      rw [←sumCards]
      have l : d=d-2+2 := (Nat.sub_add_cancel hd).symm
      nth_rw 2 [l]
      nlinarith [congrArg (fun a => a*L.card) l]

/-- For odd average threshold 2d−1, any shortfall below d+5 forces a
dense induced core with at least (d−3)/(d−2) of its vertices at the minimum.
At floor seven this proportion is one half. -/
theorem many_low_in_short_odd_core [Nonempty V] (h4 : NoFourCycle G) {d : ℕ} (hd : 3≤d)
    (hav : ((2*d-1:ℕ):ℝ) ≤ l G) (short : G.path<d+5) :
    ∃ S : Finset V, S.Nonempty ∧
      let H := G.induce (S:Set V)
      let count := (Finset.univ.filter (fun u:S => H.indepNeighborsCard u=d)).card
      (2*d-1)*S.card ≤ ∑ u:S,H.indepNeighborsCard u ∧
      (∑ u:S,H.indepNeighborsCard u) ≤ (d+2)*S.card+(d-2)*count ∧
      (d-3)*S.card ≤ (d-2)*count := by
  classical
  obtain ⟨S,hS,budget,hmin,extra⟩ := exists_odd_independence_core h4 (by omega) hav
  let H := G.induce (S:Set V)
  have cc : NoFourCycle H := fun {x y _ _} ne hx hy hx' hy' =>
    Subtype.ext (h4 (x:=x.val) (y:=y.val) (fun e => ne (Subtype.ext e)) hx hy hx' hy')
  have degrees (u:S) (eq : H.indepNeighborsCard u=d) : H.degree u=d := by
    let J := H.induce (H.neighborSet u)
    have independent : J.IsIndepSet (↑(Finset.univ : Finset (H.neighborSet u)) : Set _) := by
      intro v _ w _ _
      exact (extra u eq).1 _ _ v.property w.property
    have le := independent.card_le_indepNum (t:=Finset.univ)
    rw [Finset.card_univ,H.card_neighborSet_eq_degree] at le
    change H.degree u≤H.indepNeighborsCard u at le
    exact ((indepNeighborsCard_le_degree u).antisymm le).symm.trans eq
  have shortH := lt_of_le_of_lt (G.path_induce_le (S:Set V)) short
  have lim := independence_sum_of_short_odd_core (G:=H) cc (by omega : 2≤d) hmin
    (fun u v ha eq => (extra u eq).2 _ ha) degrees shortH
  have sc : Fintype.card (S:Set V)=S.card := Fintype.card_coe S
  rw [sc] at lim
  refine ⟨S,hS,budget,lim,?_⟩
  change (2*d-1)*S.card ≤ ∑ u:S,H.indepNeighborsCard u at budget
  rw [show 2*d-1=(d+2)+(d-3) by omega,Nat.add_mul] at budget
  exact Nat.le_of_add_le_add_left (budget.trans lim)

/-- Average neighborhood independence at least five supplies an induced
core with a five-edge chain rooted at a vertex with five independent neighbors. -/
theorem exists_five_rooted_dense_core [Nonempty V] (h4 : NoFourCycle G) (avg : (5:ℝ)≤l G) :
    ∃ (S : Finset V) (P : Chain (G.induce (S:Set V)) 5),
      NoFourCycle (G.induce (S:Set V)) ∧ 5≤(G.induce (S:Set V)).indepNeighborsCard (P.vertex 0) ∧
        ∀ u:S,3≤(G.induce (S:Set V)).indepNeighborsCard u := by
  classical
  obtain ⟨S,hs,budget,hmin,extra⟩ := exists_odd_independence_core h4 (d:=3) (by decide) avg
  let H := G.induce (S:Set V)
  have cc : NoFourCycle H := fun {x y _ _} ne hx hy hx' hy' =>
    Subtype.ext (h4 (x:=x.val) (y:=y.val) (fun e => ne (Subtype.ext e)) hx hy hx' hy')
  have high : ∃ a:S,5≤H.indepNeighborsCard a := by
    by_contra! small
    have le := Finset.sum_lt_sum_of_nonempty (s:=Finset.univ) (by
      have : Nonempty S := hs.to_subtype
      exact Finset.univ_nonempty) (fun (u:S) _ => small u)
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul] at le
    change (∑ u:S,H.indepNeighborsCard u) < S.card*5 at le
    change 5*S.card ≤ ∑ u:S,H.indepNeighborsCard u at budget
    omega
  obtain ⟨a,ha⟩ := high
  obtain ⟨P,e⟩ := exists_rooted_chain_of_independent_low (G:=H) cc (by decide : 2≤3)
    hmin (fun u v edge low => (extra u low).2 _ edge) a
  refine ⟨S,P.reverse,cc,?_,hmin⟩
  simpa only [Chain.reverse,Nat.sub_zero,e] using ha

end Wall133
