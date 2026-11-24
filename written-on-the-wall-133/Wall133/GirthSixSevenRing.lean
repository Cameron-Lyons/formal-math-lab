import Wall133.GirthSixOddDensity
import Wall133.FiveCycle
import Wall133.OddNeighborhoodCore
import Wall133.LeafPruning

/-! # The odd threshold five at girth six -/

namespace Wall133
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

private abbrev Near (i j : Fin 7) := CyclicEdge i j
private abbrev Two (i j : Fin 7) := i ≠ j ∧ ∃ k : Fin 7, Near i k ∧ Near j k
private abbrev Far (i j : Fin 7) := i ≠ j ∧ ¬Near i j ∧ ¬Two i j

private theorem far_pair : ∀ i j k : Fin 7, Far i j → Far i k → j=k ∨ Near j k := by decide
set_option maxRecDepth 5000 in
set_option maxHeartbeats 3000000 in
private theorem rich_pair : ∀ I : Finset (Fin 7), (∀ i ∉ I, ∃ j ∈ I, Far i j) →
    ∃ i ∈ I, ∃ j ∈ I, Two i j := by decide

private theorem six_arc : ∀ i j : Fin 7, Two i j → ∃ b : Bool,
    let t := forwardArc (n:=7) (k:=6) i b
    t 0=i ∧ t 5=j ∧ Function.Injective t ∧
    ∀ a b : Fin 6, Near (t a) (t b) ↔ a.val+1=b.val ∨ b.val+1=a.val := by decide

private structure Seven (G : SimpleGraph V) where
  v : Fin 7 → V
  inj : Function.Injective v
  edge (i j) : G.Adj (v i) (v j) ↔ Near i j
  outside (x : V) (hx : ∀ i,x ≠ v i) {i j} : G.Adj x (v i) → G.Adj x (v j) → i=j
  no5 {u : V} (p : G.Walk u u) : p.length ≠ 5
  no3 {u : V} (p : G.Walk u u) : p.length ≠ 3

namespace Seven
variable (R : Seven G)
private def Arm (i : Fin 7) (x : V) := (∀ j,x ≠ R.v j) ∧ G.Adj x (R.v i)
private def Away (y : V) := (∀ j,y ≠ R.v j) ∧ ∀ j,¬G.Adj y (R.v j)

include R in
private theorem noPent {a b c d e : V}
    (ab : G.Adj a b) (bc : G.Adj b c) (cd : G.Adj c d) (de : G.Adj d e) (ea : G.Adj e a) : False :=
  R.no5 (.cons ab (.cons bc (.cons cd (.cons de (.cons ea .nil))))) rfl

include R in
private theorem noTri {a b c : V} (ab : G.Adj a b) (bc : G.Adj b c) (ca : G.Adj c a) : False :=
  R.no3 (.cons ab (.cons bc (.cons ca .nil))) rfl

private theorem other_bad {i : Fin 7} {x y : V} (h4 : NoFourCycle G) (hx : R.Arm i x)
    (hy : G.Adj x y) (hne : y ≠ R.v i) (bad : ¬ R.Away y) : ∃ j, Far i j ∧ R.Arm j y := by
  classical
  have out (j) : y ≠ R.v j := by
    intro e
    have := R.outside x hx.1 hx.2 (e ▸ hy)
    exact hne (this ▸ e)
  obtain ⟨j,hyj⟩ : ∃ j,G.Adj y (R.v j) := by
    by_contra! none
    exact bad ⟨out,none⟩
  refine ⟨j,⟨?_,?_,?_⟩,out,hyj⟩
  · rintro rfl
    exact R.noTri hy hyj hx.2.symm
  · intro hi
    exact hne (h4 (hx.1 j) hy hyj.symm hx.2 ((R.edge _ _).2 hi).symm)
  · rintro ⟨_,k,hik,hjk⟩
    exact R.noPent hx.2 ((R.edge _ _).2 hik) ((R.edge _ _).2 hjk).symm hyj.symm hy.symm

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
private noncomputable def seconds (x : V) : Finset V := by
  classical
  exact (G.neighborFinset x).filter R.Away

omit [DecidableEq V] in
private theorem mem_seconds {x y : V} : y∈R.seconds x ↔ G.Adj x y ∧ R.Away y := by
  classical
  simp [seconds]

private theorem branch_count (h4 : NoFourCycle G) {i : Fin 7} {x : V} (hx : R.Arm i x) :
    G.degree x ≤ (R.seconds x).card+2 ∧
    (3≤G.degree x → (R.seconds x).card<2 → ∃ j y, Far i j ∧ R.Arm j y ∧ G.Adj x y) := by
  classical
  let N := (G.neighborFinset x).erase (R.v i)
  let B := N.filter (fun y => ¬R.Away y)
  have data (y : V) (hy : y∈B) : G.Adj x y ∧ ∃ j, Far i j ∧ R.Arm j y := by
    obtain ⟨hN,bad⟩ := Finset.mem_filter.mp hy
    obtain ⟨hne,had⟩ := Finset.mem_erase.mp hN
    have ha := (G.mem_neighborFinset _ _).1 had
    exact ⟨ha,R.other_bad h4 hx ha hne bad⟩
  have small : B.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro y hy z hz
    obtain ⟨hxy,j,hj,ry⟩ := data y hy
    obtain ⟨hxz,k,hk,rz⟩ := data z hz
    rcases far_pair i j k hj hk with rfl|e
    · exact h4 (hx.1 _) hxy ry.2.symm hxz rz.2.symm
    · exact (R.noPent hxy ry.2 ((R.edge _ _).2 e) rz.2.symm hxz.symm).elim
  have equal : N.filter R.Away = R.seconds x := by
    ext z
    rw [Finset.mem_filter,R.mem_seconds]
    simp only [N,Finset.mem_erase,G.mem_neighborFinset]
    exact ⟨fun h => ⟨h.1.2,h.2⟩,fun h => ⟨⟨h.2.1 _,h.1⟩,h.2⟩⟩
  have size := N.card_filter_add_card_filter_not R.Away
  change _+B.card=N.card at size
  rw [equal] at size
  have pos := (G.degree_pos_iff_exists_adj x).2 ⟨_,hx.2⟩
  have ns : N.card=G.degree x-1 := by simp [N,Finset.card_erase_of_mem,hx.2]
  refine ⟨by omega,?_⟩
  intro hd hs
  obtain ⟨y,hy⟩ := Finset.card_pos.mp (by omega : 0<B.card)
  obtain ⟨hxy,j,hj,hA⟩ := data y hy
  exact ⟨j,y,hj,hA,hxy⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem no_cross {i j : Fin 7} (pair : Two i j) {x w : V} (hx : R.Arm i x) (hw : R.Arm j w) :
    x≠w ∧ ¬G.Adj x w := by
  obtain ⟨neq,k,hik,hjk⟩ := pair
  refine ⟨fun he => neq (R.outside x hx.1 hx.2 (he ▸ hw.2)),?_⟩
  intro h
  exact R.noPent hx.2 ((R.edge _ _).2 hik) ((R.edge _ _).2 hjk).symm hw.2.symm h.symm

private theorem choose_ends (h4 : NoFourCycle G) {i j : Fin 7} (pair : Two i j)
    {x w : V} (hx : R.Arm i x) (hw : R.Arm j w)
    (manyX : 2≤(R.seconds x).card) (manyW : 2≤(R.seconds w).card) :
    ∃ y z, y ∈ R.seconds x ∧ z ∈ R.seconds w ∧ ¬G.Adj y w ∧ ¬G.Adj x z ∧ ¬G.Adj y z := by
  classical
  have nxw := R.no_cross pair hx hw
  obtain ⟨y₁,y₂,h₁,h₂,ne⟩ := Finset.one_lt_card_iff.mp manyX
  have getY : ∃ y∈R.seconds x, ¬G.Adj y w := by
    by_contra! h
    exact ne (h4 nxw.1 (R.mem_seconds.mp h₁).1 (h _ h₁).symm
      (R.mem_seconds.mp h₂).1 (h _ h₂).symm)
  obtain ⟨y,hy,hyW⟩ := getY
  have hxy := (R.mem_seconds.mp hy).1
  have nyw : y ≠ w := fun he => (R.mem_seconds.mp hy).2.2 j (he ▸ hw.2)
  obtain ⟨z₁,z₂,h₁,h₂,ne⟩ := Finset.one_lt_card_iff.mp manyW
  refine ⟨y,?_⟩
  by_contra! h
  have test (z) (hz : z∈R.seconds w) : G.Adj x z ∨ G.Adj y z := by
    have := h z hy hz hyW
    tauto
  have wz₁ := (R.mem_seconds.mp h₁).1
  have wz₂ := (R.mem_seconds.mp h₂).1
  rcases test _ h₁ with xx|yy <;> rcases test _ h₂ with x'|y'
  · exact ne (h4 nxw.1 xx wz₁ x' wz₂)
  · exact R.noPent xx wz₁.symm wz₂ y'.symm hxy.symm
  · exact R.noPent yy wz₁.symm wz₂ x'.symm hxy
  · exact ne (h4 nyw yy wz₁ y' wz₂)

private theorem ten (h4 : NoFourCycle G) {i j : Fin 7} (pair : Two i j) {x w : V}
    (hx : R.Arm i x) (hw : R.Arm j w) (manyX : 2≤(R.seconds x).card)
    (manyW : 2≤(R.seconds w).card) : 10≤G.path := by
  obtain ⟨y,z,hy,hz,nyw,nxz,nyz⟩ := R.choose_ends h4 pair hx hw manyX manyW
  obtain ⟨b,hi,hj,inj,edges⟩ := six_arc i j pair
  let t := forwardArc (n:=7) (k:=6) i b
  let q (k : Fin 6) := R.v (t k)
  have rq (a b : Fin 6) : G.Adj (q a) (q b) ↔ a.val+1=b.val ∨ b.val+1=a.val :=
    (R.edge _ _).trans (edges a b)
  have xq (a : Fin 6) : G.Adj x (q a) ↔ a=0 := by
    refine ⟨fun h => inj ((R.outside x hx.1 h hx.2).trans hi.symm),?_⟩
    rintro rfl
    simpa only [q,t,hi] using (show G.Adj x (R.v i) from hx.2)
  have wq (a : Fin 6) : G.Adj w (q a) ↔ a=5 := by
    refine ⟨fun h => inj ((R.outside w hw.1 h hw.2).trans hj.symm),?_⟩
    rintro rfl
    simpa only [q,t,hj] using (show G.Adj w (R.v j) from hw.2)
  have qx (a) := (G.adj_comm (q a) x).trans (xq a)
  have qw (a) := (G.adj_comm (q a) w).trans (wq a)
  have yq (a) : ¬G.Adj y (q a) := (R.mem_seconds.mp hy).2.2 _
  have zq (a) : ¬G.Adj z (q a) := (R.mem_seconds.mp hz).2.2 _
  have qy (a) : ¬G.Adj (q a) y := fun h => yq a h.symm
  have qz (a) : ¬G.Adj (q a) z := fun h => zq a h.symm
  have xy := (R.mem_seconds.mp hy).1
  have wz := (R.mem_seconds.mp hz).1
  have nxw := (R.no_cross pair hx hw).2
  have nwx : ¬G.Adj w x := fun h => nxw h.symm
  have nwy : ¬G.Adj w y := fun h => nyw h.symm
  have nzx : ¬G.Adj z x := fun h => nxz h.symm
  have nzy : ¬G.Adj z y := fun h => nyz h.symm
  let f : Fin 10 → V := ![y,x,q 0,q 1,q 2,q 3,q 4,q 5,w,z]
  have e (a b : Fin 10) : G.Adj (f a) (f b) ↔ a.val+1=b.val ∨ b.val+1=a.val := by
    fin_cases a <;> fin_cases b <;> simp [f,rq,xq,wq,qx,qw,yq,zq,qy,qz,xy,xy.symm,
      wz,wz.symm,nxw,nwx,nyw,nwy,nxz,nzx,nyz,nzy]
  apply path_bound_of_indices f _ e
  intro i j he
  have distinguish : ∀ i j : Fin 10,
      (∀ t : Fin 10, (i.val+1=t.val ∨ t.val+1=i.val) ↔ (j.val+1=t.val ∨ t.val+1=j.val)) → i=j := by decide
  exact distinguish i j (fun t => (e i t).symm.trans (he ▸ e j t))

private theorem rich_path (h4 : NoFourCycle G) (hmin : ∀ v,3≤G.degree v)
    (next : ∀ x y, G.Adj x y → G.degree x=3 → 4≤G.degree y)
    (arms : ∀ i,∃ x,R.Arm i x) : 10≤G.path := by
  classical
  let I := Finset.univ.filter (fun i => ∃ x,R.Arm i x ∧ 2≤(R.seconds x).card)
  have rich (i : Fin 7) : i∈I ↔ ∃ x,R.Arm i x ∧ 2≤(R.seconds x).card := by simp [I]
  have dominate (i : Fin 7) (hi : i∉I) : ∃ j∈I,Far i j := by
    obtain ⟨x,hx⟩ := arms i
    have hsmall : (R.seconds x).card<2 := by
      by_contra! large
      exact hi ((rich _).2 ⟨x,hx,large⟩)
    obtain ⟨count,bad⟩ := R.branch_count h4 hx
    obtain ⟨j,y,far,armY,hxy⟩ := bad (hmin x) hsmall
    have dy := next x y hxy (by have := hmin x; omega)
    have cy := (R.branch_count h4 armY).1
    exact ⟨j,(rich j).2 ⟨y,armY,by omega⟩,far⟩
  obtain ⟨i,hi,j,hj,pair⟩ := rich_pair I dominate
  obtain ⟨x,hx,cx⟩ := (rich _).1 hi
  obtain ⟨w,hw,cw⟩ := (rich _).1 hj
  exact R.ten h4 pair hx hw cx cw

end Seven

private theorem ten_of_seven (C : ShortestOddWalk G) [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (seven : C.walk.length=7) (hmin : ∀ v,3≤G.degree v)
    (next : ∀ x y, G.Adj x y → G.degree x=3 → 4≤G.degree y) : 10≤G.path := by
  let v (i : Fin 7) := C.walk.getVert i.val
  have bound (i : Fin 7) : i.val<C.walk.length := by rw [seven];exact i.isLt
  have step {i j : Fin 7} (h : CycleStep 7 i.val j.val) : G.Adj (v i) (v j) := by
    have hstep := C.walk.adj_getVert_succ (i:=i.val) (by rw [seven];exact i.isLt)
    rcases h with e|⟨e,f⟩
    · simpa only [v,←e] using hstep
    · simpa only [v,f,e,←seven,C.walk.getVert_zero,C.walk.getVert_length] using hstep
  let R : Seven G :=
    { v := v
      inj := fun i j h => Fin.ext (C.inj (bound i) (bound j) h)
      edge := fun i j => by
        constructor
        · intro h
          rcases le_total i.val j.val with le|le
          · have := C.edge le (bound j) h
            unfold Near CyclicEdge CycleStep
            omega
          · have := C.edge le (bound i) h.symm
            unfold Near CyclicEdge CycleStep
            omega
        · rintro (h|h)
          · exact step h
          · exact (step h).symm
      outside := fun x out i j h h' => Fin.ext (C.private_neighbor h4
        (fun k hk => out ⟨k,by rwa [←seven]⟩) (bound i) (bound j) h h')
      no5 := fun p h => by have := C.minimal _ p (by simp [h]); omega
      no3 := fun p h => by have := C.minimal _ p (by simp [h]); omega }
  apply R.rich_path h4 hmin next
  intro i
  obtain ⟨x,hx,out⟩ := C.off_neighbor (i:=i.val) (bound i) (by omega) (hmin _)
  exact ⟨x,fun j => out j.val (bound j),hx⟩

/-- In girth at least five, two distinct common neighbors would give
two different paths of length two between the same pair of vertices. -/
theorem noFourCycle_of_girth_five (hg : 5 ≤ G.egirth) : NoFourCycle G := by
  intro x y a b hxy hxa hya hxb hyb
  let p : G.Walk x y := .cons hxa (.cons hya.symm .nil)
  let q : G.Walk x y := .cons hxb (.cons hyb.symm .nil)
  have hp : p.IsPath := by simp [p,Walk.isPath_def,hxa.ne,hxy,hya.ne.symm]
  have hq : q.IsPath := by simp [q,Walk.isPath_def,hxb.ne,hxy,hyb.ne.symm]
  by_contra ne
  have uneq : p≠q := fun e => ne (congrArg (fun w : G.Walk x y => w.getVert 1) e)
  obtain ⟨_,_,_,c,hc,hlen⟩ := hp.exists_isCycle_length_le_add_of_ne hq uneq
  have lb : 5≤c.length := ENat.natCast_le_natCast.mp (hg.trans (egirth_le_length hc))
  change c.length≤2+2 at hlen
  omega

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Average degree at least five forces a ten-vertex induced path in a
graph of girth at least six. -/
theorem ten_le_path_of_girth_six_density [Nonempty V] (hg : 6≤G.egirth)
    (hav : 5*Fintype.card V ≤ ∑ x,G.degree x) : 10≤G.path := by
  classical
  have h4 := noFourCycle_of_girth_five (G:=G) ((by decide : (5 : ℕ∞)≤6).trans hg)
  obtain ⟨S,hS,dense,hmin,leaf⟩ := exists_odd_neighborhood_core G (d:=3) (by decide) hav
  let H := G.induce (S : Set V)
  let : Nonempty S := hS.to_subtype
  have four : NoFourCycle H := fun _ _ _ _ hne a b c d =>
    Subtype.ext (h4 (fun he => hne (Subtype.ext he)) a b c d)
  have mono : H.path≤G.path := G.path_induce_le (S : Set V)
  apply le_trans _ mono
  by_cases bip : H.IsBipartite
  · obtain ⟨c⟩ := bip
    have dens : 5*Fintype.card S ≤ ∑ x : S,H.degree x := by simpa using dense
    have avg := le_l_of_sum_degree c (k:=5) (by convert dens using 1 <;> congr 2)
    exact add_five_le_path_of_bipartite_density ⟨c⟩ four (k:=5) (by decide) avg
  obtain ⟨C⟩ := exists_shortestOddWalk bip
  have hgH : 6≤H.egirth := hg.trans (IsContained.egirth_le ⟨Copy.induce G (S : Set V)⟩)
  have bound : 6≤C.walk.length := ENat.natCast_le_natCast.mp (hgH.trans (egirth_le_length C.isCycle))
  have odd := C.odd
  by_cases sev : C.walk.length=7
  · apply ten_of_seven C four sev hmin
    intro x y hxy dx
    by_contra! hy
    have dy : H.degree y=3 := by have h : 3 ≤ H.degree y := hmin y; omega
    have cap := leaf x {y} (fun z hz => by rw [Finset.mem_singleton.mp hz]; exact ⟨hxy,dy⟩)
    change ({y} : Finset S).card ≤ 2*(H.degree x-3) at cap
    simp [dx] at cap
  have := C.add_one_le_path four (by omega) hmin
  omega

/-- The fifth density threshold gives the full radius bound at all radii
in graphs of girth at least six. -/
theorem radius_add_five_density_le_path_girth_six (hc : G.Connected) (hg : 6≤G.egirth)
    (hav : 5*Fintype.card V ≤ ∑ x,G.degree x) :
    G.radius.toNat+5 ≤ G.path := by
  have : Nonempty V := hc.nonempty
  have := ten_le_path_of_girth_six_density hg hav
  have := chung_bound_nat G hc
  omega

end Wall133
