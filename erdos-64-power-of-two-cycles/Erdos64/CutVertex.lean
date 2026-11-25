import Erdos64.Terminals

/-! Repairing degree defects in a bipartite graph while preserving the absence
of dyadic cycles. This applies to pieces of a minimum-order counterexample. -/
namespace Erdos64.CutVertex
open Terminals
universe u
variable {V : Type u}

def Bipartite (G : Graph V) : Prop :=
  ∃ color : V → Bool, ∀ a b, G.adj a b → color a ≠ color b

/-- A finite nonempty unrestricted counterexample with at most the stated
number of vertices. Repetitions in a covering list only raise the bound. -/
def CounterexampleAtMost (n : Nat) : Prop :=
  ∃ (W : Type u) (H : Graph W) (l : List W), Nonempty W ∧ (∀ w, w ∈ l) ∧
    l.length ≤ n ∧ MinDegreeThree H ∧ ¬HasDyadicCycle H

private theorem weaken {n m : Nat} (h : CounterexampleAtMost.{u} n) (le : n ≤ m) :
    CounterexampleAtMost.{u} m := by
  obtain ⟨W,H,l,inh,all,len,deg,no⟩ := h
  exact ⟨W,H,l,inh,all,Nat.le_trans len le,deg,no⟩

private theorem twoExcept {G : Graph V} {v : V} (d : ThreeAt G v) (t : V) :
    ∃ a b, G.adj v a ∧ G.adj v b ∧ a ≠ b ∧ a ≠ t ∧ b ≠ t := by
  obtain ⟨a,b,c,ha,hb,hc,ab,ac,bc⟩ := d
  by_cases e : a = t
  · exact ⟨b,c,hb,hc,bc,by grind,by grind⟩
  · by_cases f : b = t
    · exact ⟨a,c,ha,hc,ac,e,by grind⟩
    · exact ⟨a,b,ha,hb,ab,e,f⟩

private theorem neighborExcept {G : Graph V} {v : V} (d : TwoAt G v) (t : V) :
    ∃ a, G.adj v a ∧ a ≠ t := by
  obtain ⟨a,b,ha,hb,ab⟩ := d
  by_cases e : a = t
  · exact ⟨b,hb,by grind⟩
  · exact ⟨a,ha,e⟩

def induced (G : Graph V) (P : V → Prop) : Graph {x // P x} where
  adj a b := G.adj a.val b.val
  symm := G.symm
  loopless := fun x => G.loopless x.val

private theorem retainedDeg {G : Graph V} {P : V → Prop} (z : {v // P v}) (d : ThreeAt G z.val)
    (all : ∀ a, G.adj z.val a → P a) : ThreeAt (induced G P) z := by
  obtain ⟨a,b,c,ha,hb,hc,ab,ac,bc⟩ := d
  exact ⟨⟨a,all _ ha⟩,⟨b,all _ hb⟩,⟨c,all _ hc⟩,ha,hb,hc,
    by simp [ab],by simp [ac],by simp [bc]⟩

private theorem lostAtMostOne {G : Graph V} {P : V → Prop} (z : {v // P v}) (d : ThreeAt G z.val)
    (t : V) (kept : ∀ a, G.adj z.val a → a ≠ t → P a) : TwoAt (induced G P) z := by
  obtain ⟨a,b,ha,hb,ab,at',bt⟩ := twoExcept d t
  exact ⟨⟨a,kept _ ha at'⟩,⟨b,kept _ hb bt⟩,ha,hb,by simp [ab]⟩

private theorem inducedNoCycle {G : Graph V} (no : ¬HasDyadicCycle G) (P : V → Prop) :
    ¬HasDyadicCycle (induced G P) := by
  intro ⟨k,hk,f,inj,steps⟩
  exact no ⟨k,hk,fun i => (f i).val,fun i j e => inj i j (Subtype.ext e),steps⟩

private theorem oppositeNoCommon {G : Graph V} {x y : V} (color : V → Bool)
    (proper : ∀ a b, G.adj a b → color a ≠ color b) (opp : color x ≠ color y)
    (w : V) : ¬ (G.adj w x ∧ G.adj w y) := by
  intro ⟨a,b⟩
  have p := proper _ _ a; have q := proper _ _ b
  cases h₁ : color w <;> cases h₂ : color x <;> cases h₃ : color y <;> grind

private theorem evenPower {k : Nat} (hk : 2 ≤ k) : 2^k % 2 = 0 := by
  cases k with
  | zero => omega
  | succ k => rw [Nat.pow_succ]; omega

private theorem identifyOpposite {G : Graph V} {x y : V} (ne : x ≠ y)
    (l : List V) (all : ∀ w, w ∈ l) (color : V → Bool)
    (proper : ∀ a b, G.adj a b → color a ≠ color b) (opp : color x ≠ color y)
    (others : ∀ w, w ≠ x → w ≠ y → ThreeAt G w)
    (merged : ThreeAt (Identification.graph G x y) none) (no : ¬ HasDyadicCycle G) :
    CounterexampleAtMost.{u} (l.length-1) := by
  let Q := Identification.graph G x y
  have degree : MinDegreeThree Q := by
    intro w; cases w with
    | none => exact merged
    | some w =>
      exact Identification.threeAtOutside w (others _ w.property.1 w.property.2)
        (fun a b => False.elim (oppositeNoCommon color proper opp w.val ⟨a,b⟩))
  obtain ⟨labels,len,covers⟩ := Identification.shorterCover ne l all
  refine ⟨_,Q,labels,⟨none⟩,covers,by omega,degree,?_⟩
  intro ⟨k,hk,cycle⟩
  rcases Identification.cycleOrPath cycle with old | path
  · exact no ⟨k,hk,old⟩
  · exact opp ((pathColorParity color proper path).2 (evenPower hk))

private theorem identifySeparated {G : Graph V} {x y : V} (ne : x ≠ y) (far : ¬G.adj x y)
    (l : List V) (all : ∀ w, w ∈ l) (color : V → Bool)
    (proper : ∀ a b, G.adj a b → color a ≠ color b) (opp : color x ≠ color y)
    (dx : TwoAt G x) (dy : TwoAt G y) (others : ∀ w, w ≠ x → w ≠ y → ThreeAt G w)
    (no : ¬ HasDyadicCycle G) : CounterexampleAtMost.{u} (l.length-1) := by
  apply identifyOpposite ne l all color proper opp others ?_ no
  apply Identification.threeAtMerged ne (fun h => no ⟨2,by decide,h⟩)
  · obtain ⟨a,b,ha,hb,ab⟩ := dx; exact ⟨a,b,ha,hb,ab,by grind,by grind⟩
  · obtain ⟨a,b,ha,hb,ab⟩ := dy
    exact ⟨a,b,ha,hb,ab,by grind [→ Graph.symm],by grind [→ Graph.symm]⟩

private theorem fullEndpoint {G : Graph V} {x y : V}
    (dx : ThreeAt G x) (dy : TwoAt G y) (disjoint : ∀ w, ¬ (G.adj w x ∧ G.adj w y)) :
    ThreeAt (Identification.graph G x y) none := by
  obtain ⟨a,b,ha,hb,ab,ay,by'⟩ := twoExcept dx y
  obtain ⟨c,hc,cx⟩ := neighborExcept dy x
  exact ⟨some ⟨a,by grind [Graph.loopless],ay⟩,some ⟨b,by grind [Graph.loopless],by'⟩,
    some ⟨c,cx,by grind [Graph.loopless]⟩,Or.inl ha,Or.inl hb,Or.inr hc,
    by simp [ab],by simp; grind [→ Graph.symm],by simp; grind [→ Graph.symm]⟩

private theorem coverAfterTwo (l : List V) (all : ∀ v, v ∈ l) {x y : V} (ne : x ≠ y) :
    ∃ labels : List {v : V // v ≠ x ∧ v ≠ y},
      labels.length ≤ l.length-2 ∧ ∀ v, v ∈ labels := by
  classical
  let deleted := (l.erase x).erase y
  let selected := deleted.filter (fun v => decide (v ≠ x ∧ v ≠ y))
  let labels := selected.attachWith _ (by intro v h; exact of_decide_eq_true (List.mem_filter.mp h).2)
  have lenD : deleted.length = l.length-2 := by
    have hy := (List.mem_erase_of_ne ne.symm).mpr (all y)
    simp [deleted,List.length_erase_of_mem hy,List.length_erase_of_mem (all x)]; omega
  refine ⟨labels,?_,?_⟩
  · have h := List.length_filter_le (fun v => decide (v ≠ x ∧ v ≠ y)) deleted
    simpa [labels,selected,← lenD] using h
  · intro v; apply (List.mem_attachWith _ _).2
    exact List.mem_filter.mpr ⟨(List.mem_erase_of_ne v.property.2).mpr
      ((List.mem_erase_of_ne v.property.1).mpr (all v.val)),decide_eq_true v.property⟩

/-- If the adjacent ports are the only possible defects and both have degree
exactly two, delete them, then identify their remaining neighbors. -/
private theorem removeAdjacentPorts {G : Graph V} {x y : V} (ne : x ≠ y) (xy : G.adj x y)
    (l : List V) (all : ∀ w, w ∈ l) (color : V → Bool)
    (proper : ∀ a b, G.adj a b → color a ≠ color b)
    (dx : TwoAt G x) (dy : TwoAt G y) (lowX : ¬ThreeAt G x) (lowY : ¬ThreeAt G y)
    (others : ∀ w, w ≠ x → w ≠ y → ThreeAt G w) (no : ¬HasDyadicCycle G) :
    CounterexampleAtMost.{u} (l.length-3) := by
  obtain ⟨a,xa,ay⟩ := neighborExcept dx y
  obtain ⟨b,yb,bx⟩ := neighborExcept dy x
  have ax : a ≠ x := by grind [Graph.loopless]
  have by' : b ≠ y := by grind [Graph.loopless]
  have allX (w : V) (e : G.adj x w) : w = y ∨ w = a := by
    apply Classical.byContradiction; intro h; exact lowX ⟨a,y,w,xa,xy,e,ay,by grind,by grind⟩
  have allY (w : V) (e : G.adj y w) : w = x ∨ w = b := by
    apply Classical.byContradiction; intro h; exact lowY ⟨b,x,w,yb,G.symm xy,e,bx,by grind,by grind⟩
  have opp : color a ≠ color b := by
    have c₁ := proper _ _ xa; have c₂ := proper _ _ xy; have c₃ := proper _ _ yb
    cases e₁ : color x <;> cases e₂ : color y <;> cases e₃ : color a <;> cases e₄ : color b <;> grind
  have ab : a ≠ b := fun e => opp (congrArg color e)
  have far : ¬G.adj a b := fun e => no ⟨2,by decide,
    Identification.fourOfCommon bx (Ne.symm ay) (G.symm yb) (G.symm e) xy xa⟩
  let P := fun w => w ≠ x ∧ w ≠ y
  let A : {v // P v} := ⟨a,ax,ay⟩
  let B : {v // P v} := ⟨b,bx,by'⟩
  have twoA : TwoAt (induced G P) A := lostAtMostOne A (others _ ax ay) x (by
    intro w e h; exact ⟨h,fun f => ab (by have z := allY a (G.symm (f ▸ e)); grind)⟩)
  have twoB : TwoAt (induced G P) B := lostAtMostOne B (others _ bx by') y (by
    intro w e h; exact ⟨fun f => ab (by have z := allX b (G.symm (f ▸ e)); grind),h⟩)
  obtain ⟨labels,len,covers⟩ := coverAfterTwo l all ne
  have answer := identifySeparated (G := induced G P) (x := A) (y := B) (fun e => ab (congrArg Subtype.val e))
    far labels covers (fun v => color v.val) (fun _ _ e => proper _ _ e) opp twoA twoB
    (fun v na nb => retainedDeg v (others _ v.property.1 v.property.2) (by
      intro w e
      have va : v.val ≠ a := fun h => na (Subtype.ext h)
      have vb : v.val ≠ b := fun h => nb (Subtype.ext h)
      exact ⟨fun h => va (by have := allX v.val (G.symm (h ▸ e)); have := v.property; grind),
        fun h => vb (by have := allY v.val (G.symm (h ▸ e)); have := v.property; grind)⟩))
    (inducedNoCycle no P)
  exact weaken answer (by omega)

/-- A dyadic-cycle-free bipartite graph with at most two degree-two defects
and minimum degree three elsewhere produces an unrestricted counterexample
of at most the same order. The two designated ports may be adjacent. -/
theorem bipartiteRepair {G : Graph V} (l : List V) (all : ∀ w, w ∈ l) {x y : V}
    (ne : x ≠ y) (bip : Bipartite G) (dx : TwoAt G x) (dy : TwoAt G y)
    (others : ∀ w, w ≠ x → w ≠ y → ThreeAt G w) (no : ¬HasDyadicCycle G) :
    CounterexampleAtMost.{u} l.length := by
  obtain ⟨color,proper⟩ := bip
  by_cases same : color x = color y
  · have far : ¬ G.adj x y := fun e => proper x y e same
    refine ⟨_,addEdge G x y ne,l,⟨x⟩,all,Nat.le_refl _,degreeWithTerminalEdge ne far dx dy others,?_⟩
    intro bad
    obtain ⟨k,hk,path⟩ := (dyadicRemove bad).resolve_left no
    have even := (pathColorParity color proper path).1 same
    have evenPow := evenPower hk
    have pos := Nat.two_pow_pos k; omega
  · have disjoint := oppositeNoCommon color proper same
    by_cases far : ¬G.adj x y
    · exact weaken (identifySeparated ne far l all color proper same dx dy others no) (by omega)
    · by_cases fullX : ThreeAt G x
      · exact weaken (identifyOpposite ne l all color proper same others (fullEndpoint fullX dy disjoint) no) (by omega)
      · by_cases fullY : ThreeAt G y
        · exact weaken (identifyOpposite ne.symm l all color proper (Ne.symm same)
            (fun v a b => others v b a) (fullEndpoint fullY dx (fun v h => disjoint v h.symm)) no) (by omega)
        · exact weaken (removeAdjacentPorts ne (Classical.byContradiction far) l all color proper dx dy
            fullX fullY others no) (by omega)

/-- In a minimum-order counterexample, any proper induced subgraph with only
two possible degree defects, both of degree at least two, is nonbipartite.
This includes either side after deleting the unique cut vertex in the
balanced two-block structure of Ducoffe and Dumitru. -/
theorem nonbipartite_of_proper_twoPort {G : Graph V} (minimal : MinimumOrderCounterexample G)
    (P : V → Prop) (missing : ∃ v, ¬ P v) {x y : {v // P v}} (ne : x ≠ y)
    (dx : TwoAt (induced G P) x) (dy : TwoAt (induced G P) y)
    (others : ∀ w, w ≠ x → w ≠ y → ThreeAt (induced G P) w) :
    ¬Bipartite (induced G P) := by
  classical
  intro bip
  obtain ⟨outside,out⟩ := missing
  let smaller := minimal.vertices.erase outside
  let keep := smaller.filter (fun v => decide (P v))
  let labels := keep.attachWith P (by intro v h; exact of_decide_eq_true (List.mem_filter.mp h).2)
  have covers (w : {v // P v}) : w ∈ labels := by
    apply (List.mem_attachWith _ _).2
    exact List.mem_filter.mpr ⟨(List.mem_erase_of_ne (show w.val ≠ outside from fun e => out (e ▸ w.property))).mpr (minimal.covers w.val),
      decide_eq_true w.property⟩
  have le : labels.length < minimal.vertices.length := by
    have h := List.length_filter_le (fun v => decide (P v)) smaller
    have hs : smaller.length = minimal.vertices.length - 1 := List.length_erase_of_mem (minimal.covers outside)
    have pos := List.length_pos_of_mem (minimal.covers outside)
    simp only [labels,List.length_attachWith,keep]; omega
  obtain ⟨W,H,l,inh,all,len,degree,avoids⟩ := bipartiteRepair labels covers ne bip dx dy others
    (inducedNoCycle minimal.avoids P)
  exact avoids (minimal.smaller H l inh all (by omega) degree)

/-- If a side of a vertex cut meets the rest of the graph only at `v`, and
`v` has at most the two indicated neighbors in that side, the side by itself
is nonbipartite. No assumption on its order or its internal connectivity is
needed. -/
theorem cutSide_nonbipartite {G : Graph V} (minimal : MinimumOrderCounterexample G)
    (v : V) (P : V → Prop) (outside : ¬P v) {x y : {w // P w}} (ne : x ≠ y)
    (separated : ∀ a, P a → ∀ b, G.adj a b → b ≠ v → P b)
    (ports : ∀ w : {a // P a}, G.adj v w.val → w = x ∨ w = y) :
    ¬Bipartite (induced G P) := by
  have two (w : {a // P a}) : TwoAt (induced G P) w :=
    lostAtMostOne w (minimal.degree w.val) v (separated _ w.property)
  apply nonbipartite_of_proper_twoPort minimal P ⟨v,outside⟩ ne (two x) (two y)
  intro w wx wy
  apply retainedDeg w (minimal.degree w.val)
  intro b adj
  apply separated _ w.property _ adj
  intro eq
  exact (ports w (G.symm (eq ▸ adj))).elim wx wy

private theorem threeAfterOne {G : Graph V} {v : V} (z : {w // w ≠ v})
    (four : Identification.AtLeastFour G z.val) : ThreeAt (induced G (· ≠ v)) z := by
  obtain ⟨a,b,c,d,distinct,ha,hb,hc,hd⟩ := four
  simp at distinct
  have make (p q r : V) (hp : G.adj z.val p) (hq : G.adj z.val q) (hr : G.adj z.val r)
      (pq : p ≠ q) (pr : p ≠ r) (qr : q ≠ r) (pv : p ≠ v) (qv : q ≠ v) (rv : r ≠ v) :
      ThreeAt (induced G (· ≠ v)) z :=
    ⟨⟨p,pv⟩,⟨q,qv⟩,⟨r,rv⟩,hp,hq,hr,by simp [pq],by simp [pr],by simp [qr]⟩
  by_cases av : a = v
  · exact make b c d hb hc hd (by grind) (by grind) (by grind) (by grind) (by grind) (by grind)
  · by_cases bv : b = v
    · exact make a c d ha hc hd (by grind) (by grind) (by grind) av (by grind) (by grind)
    · by_cases cv : c = v
      · exact make a b d ha hb hd (by grind) (by grind) (by grind) av bv (by grind)
      · exact make a b c ha hb hc (by grind) (by grind) (by grind) av bv cv

private theorem coverByTwo {W : Type u} (P : W → Prop) (a b : W)
    (two : ∃ x y : W, x ≠ y) (bound : ∀ w, P w → w = a ∨ w = b) :
    ∃ x y : W, x ≠ y ∧ ∀ w, P w → w = x ∨ w = y := by
  by_cases ne : a = b
  · obtain ⟨x,y,xy⟩ := two
    by_cases ax : a = x
    · exact ⟨a,y,by grind,by grind⟩
    · exact ⟨a,x,ax,by grind⟩
  · exact ⟨a,b,ne,bound⟩

/-- Given any two labels, a vertex whose deletion makes a minimum-order
counterexample bipartite has another cubic neighbor. -/
private theorem anotherCubic {G : Graph V} (minimal : MinimumOrderCounterexample G)
    (v : V) (bip : Bipartite (induced G (· ≠ v))) (a b : V) :
    ∃ w, G.adj v w ∧ ¬ Identification.AtLeastFour G w ∧ w ≠ a ∧ w ≠ b := by
  classical
  apply Classical.byContradiction
  intro no
  obtain ⟨p,q,_,hp,hq,_,pq,_,_⟩ := minimal.degree v
  have pv : p ≠ v := by grind [Graph.loopless]
  have qv : q ≠ v := by grind [Graph.loopless]
  let W := {w : V // w ≠ v}
  let pick (z : V) : W := if e : z ≠ v then ⟨z,e⟩ else ⟨p,pv⟩
  let bad (w : W) := G.adj v w.val ∧ ¬ Identification.AtLeastFour G w.val
  have bound (w : W) (h : bad w) : w = pick a ∨ w = pick b := by
    have eq : w.val = a ∨ w.val = b := by
      apply Classical.byContradiction
      intro neither; exact no ⟨w.val,h.1,h.2,by grind,by grind⟩
    rcases eq with e | e
    · left; subst a; apply Subtype.ext; simp [pick,w.property]
    · right; subst b; apply Subtype.ext; simp [pick,w.property]
  obtain ⟨x,y,xy,cover⟩ := coverByTwo bad _ _ ⟨⟨p,pv⟩,⟨q,qv⟩,fun e => pq (congrArg Subtype.val e)⟩ bound
  have two (w : W) : TwoAt (induced G (· ≠ v)) w :=
    lostAtMostOne w (minimal.degree w.val) v (fun _ _ ne => ne)
  apply nonbipartite_of_proper_twoPort minimal (· ≠ v) ⟨v,fun h => h rfl⟩ xy (two x) (two y) ?_ bip
  intro w wx wy
  by_cases e : G.adj v w.val
  · have four : Identification.AtLeastFour G w.val := by
      apply Classical.byContradiction
      intro h
      exact (cover w ⟨e,h⟩).elim wx wy
    exact threeAfterOne w four
  · exact retainedDeg w (minimal.degree w.val) (fun z h eq => e (G.symm (eq ▸ h)))

/-- Every odd-cycle transversal consisting of a single vertex in a globally
minimum-order counterexample has at least three distinct neighbors of degree
exactly three. Minimum degree three is part of the minimality premise. -/
theorem threeCubicNeighbors_of_bipartite_deletion {G : Graph V} (minimal : MinimumOrderCounterexample G)
    (v : V) (bip : Bipartite (induced G (· ≠ v))) :
    ∃ a b c, [a,b,c].Nodup ∧ G.adj v a ∧ G.adj v b ∧ G.adj v c ∧
      ¬ Identification.AtLeastFour G a ∧ ¬ Identification.AtLeastFour G b ∧
      ¬ Identification.AtLeastFour G c := by
  obtain ⟨a,va,ca,_,_⟩ := anotherCubic minimal v bip v v
  obtain ⟨b,vb,cb,ba,_⟩ := anotherCubic minimal v bip a a
  obtain ⟨c,vc,cc,ca',cb'⟩ := anotherCubic minimal v bip a b
  exact ⟨a,b,c,by simp; grind,va,vb,vc,ca,cb,cc⟩

end Erdos64.CutVertex
