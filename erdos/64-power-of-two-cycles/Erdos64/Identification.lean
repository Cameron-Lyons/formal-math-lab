import Erdos64.ExtensionSoundness

/-! Identifying two vertices turns a cycle through their common image into
either a cycle of the same length or a path between the two original vertices.
This gives a necessary path condition for a minimum-order counterexample. -/
namespace Erdos64

/-- A simple undirected path of `k` edges. The first `k` vertices are indexed
cyclically, starting at `root`; the last edge ends at the extra vertex `b`.
Both possible orientations of the unordered endpoints are allowed. -/
private def HasSplitPath {V : Type u} (G : Graph V) (x y : V) (k : Nat) : Prop :=
  ∃ (root : Fin k) (f : Fin k → V) (a b : V),
    ((a = x ∧ b = y) ∨ (a = y ∧ b = x)) ∧ f root = a ∧
    (∀ i j, f i = f j → i = j) ∧ (∀ i, f i ≠ b) ∧
    ∀ i, G.adj (f i) (if cycleNext i = root then b else f (cycleNext i))

/-- An injective enumeration of the vertices of an undirected path, in traversal
order, with its two endpoints specified up to orientation. -/
def HasSimplePathBetween {V : Type u} (G : Graph V) (x y : V) (k : Nat) : Prop :=
  ∃ f : Fin (k+1) → V,
    ((f 0 = x ∧ f (Fin.last k) = y) ∨ (f 0 = y ∧ f (Fin.last k) = x)) ∧
    (∀ i j, f i = f j → i = j) ∧ ∀ i : Fin k, G.adj (f i.castSucc) (f i.succ)

def HasDyadicCycle {V : Type u} (G : Graph V) : Prop :=
  ∃ k : Nat, 2 ≤ k ∧ HasCycle G (2^k)

namespace Identification

variable {V : Type u}

/-- The identified vertex is `none`; all other vertices retain their labels. -/
abbrev Identified (x y : V) := Option {v : V // v ≠ x ∧ v ≠ y}

def graph (G : Graph V) (x y : V) : Graph (Identified x y) where
  adj
    | none, none => False
    | none, some v => G.adj x v.val ∨ G.adj y v.val
    | some v, none => G.adj v.val x ∨ G.adj v.val y
    | some v, some w => G.adj v.val w.val
  symm := by intro a b; cases a <;> cases b <;> simp_all <;> grind [→ Graph.symm]
  loopless := by intro a; cases a <;> simp [G.loopless]

private noncomputable def image (x y v : V) : Identified x y := by
  classical
  exact if hx : v = x then none else if hy : v = y then none else some ⟨v,hx,hy⟩

private def lift (x y a : V) : Identified x y → V
  | none => a
  | some v => v.val

private theorem image_lift {x y a : V} (ha : a = x ∨ a = y) (z : Identified x y) :
    image x y (lift x y a z) = z := by
  classical
  cases z with
  | none => rcases ha with rfl | rfl <;> simp [image,lift]
  | some v => simp [image,lift,v.property.1,v.property.2]

private theorem image_eq {x y a b : V} (h : image x y a = image x y b) :
    a = b ∨ (a = x ∧ b = y) ∨ (a = y ∧ b = x) := by
  classical
  unfold image at h
  split at h <;> split at h <;> grind

private theorem preservedEdge {G : Graph V} {x y v w : V} (e : G.adj v w)
    (distinct : image x y v ≠ image x y w) :
    (graph G x y).adj (image x y v) (image x y w) := by
  classical
  unfold image at *
  split <;> split <;> simp_all [graph] <;> grind

private theorem extraTwo {G : Graph V} (d : MinDegreeThree G) (v t : V) :
    ∃ a b, G.adj v a ∧ G.adj v b ∧ a ≠ b ∧ a ≠ t ∧ b ≠ t := by
  obtain ⟨p,q,r,hp,hq,hr,hpq,hpr,hqr⟩ := d v
  by_cases e : p = t
  · exact ⟨q,r,hq,hr,hqr,by grind,by grind⟩
  · by_cases f : q = t
    · exact ⟨p,r,hp,hr,hpr,e,by grind⟩
    · exact ⟨p,q,hp,hq,hpq,e,f⟩

theorem fourOfCommon {G : Graph V} {x y a b : V} (diff : x ≠ y) (ab : a ≠ b)
    (xa : G.adj x a) (xb : G.adj x b) (ya : G.adj y a) (yb : G.adj y b) : HasCycle G 4 := by
  let f (i : Fin 4) := if i.val = 0 then x else if i.val = 1 then a else if i.val = 2 then y else b
  refine ⟨f,?_,?_⟩
  · intro i j eq
    apply Fin.ext
    have := i.isLt; have := j.isLt
    simp only [f] at eq
    grind [Graph.loopless]
  · intro i
    have h : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 := by omega
    rcases h with h|h|h|h <;> simp [f,cycleNext,h] <;> grind [→ Graph.symm]

def AtLeastFour (G : Graph V) (w : V) : Prop :=
  ∃ a b c d, [a,b,c,d].Nodup ∧ G.adj w a ∧ G.adj w b ∧ G.adj w c ∧ G.adj w d

theorem threeAtOutside {G : Graph V} {x y : V} (w : {v : V // v ≠ x ∧ v ≠ y})
    (deg : ∃ a b c, G.adj w.val a ∧ G.adj w.val b ∧ G.adj w.val c ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c)
    (heavy : G.adj w.val x → G.adj w.val y → AtLeastFour G w.val) : ∃ a b c : Identified x y,
    (graph G x y).adj (some w) a ∧ (graph G x y).adj (some w) b ∧
    (graph G x y).adj (some w) c ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  classical
  have im : image x y w.val = some w := by simp [image,w.property.1,w.property.2]
  have maps {v : V} (e : G.adj w.val v) : (graph G x y).adj (some w) (image x y v) := by
    rw [← im]
    apply preservedEdge e
    intro same
    have := image_eq same
    grind [Graph.loopless]
  by_cases both : G.adj w.val x ∧ G.adj w.val y
  · obtain ⟨a,b,c,d,distinct,ha,hb,hc,hd⟩ := heavy both.1 both.2
    simp at distinct
    let f := image x y
    have collision (i j : V) (e : f i = f j) := image_eq e
    have two : ∃ a b, G.adj w.val a ∧ G.adj w.val b ∧ a ≠ b ∧
        a ≠ x ∧ a ≠ y ∧ b ≠ x ∧ b ≠ y := by
      by_cases ax : a = x ∨ a = y <;> by_cases bx : b = x ∨ b = y <;>
        by_cases cx : c = x ∨ c = y <;>
        first | exact ⟨a,b,ha,hb,by grind,by grind,by grind,by grind,by grind⟩
              | exact ⟨a,c,ha,hc,by grind,by grind,by grind,by grind,by grind⟩
              | exact ⟨a,d,ha,hd,by grind,by grind,by grind,by grind,by grind⟩
              | exact ⟨b,c,hb,hc,by grind,by grind,by grind,by grind,by grind⟩
              | exact ⟨b,d,hb,hd,by grind,by grind,by grind,by grind,by grind⟩
              | exact ⟨c,d,hc,hd,by grind,by grind,by grind,by grind,by grind⟩
    obtain ⟨i,j,hi,hj,ne,ix,iy,jx,jy⟩ := two
    exact ⟨f i,f j,f x,maps hi,maps hj,maps both.1,by grind,by grind,by grind⟩
  · obtain ⟨a,b,c,ha,hb,hc,ab,ac,bc⟩ := deg
    exact ⟨_,_,_,maps ha,maps hb,maps hc,
      fun e => by have := image_eq e; grind,
      fun e => by have := image_eq e; grind,
      fun e => by have := image_eq e; grind⟩

/-- The identified vertex has at least three neighbors whenever each original
endpoint had two distinct neighbors outside the pair and there is no 4-cycle. -/
theorem threeAtMerged {G : Graph V} {x y : V} (diff : x ≠ y) (noFour : ¬ HasCycle G 4)
    (atX : ∃ a b, G.adj x a ∧ G.adj x b ∧ a ≠ b ∧ a ≠ y ∧ b ≠ y)
    (atY : ∃ c d, G.adj y c ∧ G.adj y d ∧ c ≠ d ∧ c ≠ x ∧ d ≠ x) :
    ∃ a b c, (graph G x y).adj none a ∧ (graph G x y).adj none b ∧ (graph G x y).adj none c ∧
      a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  obtain ⟨a,b,ha,hb,ab,ay,by'⟩ := atX
  obtain ⟨c,d,hc,hd,cd,cx,dx⟩ := atY
  have eligible : (c ≠ a ∧ c ≠ b) ∨ (d ≠ a ∧ d ≠ b) := by
    apply Classical.byContradiction
    intro h
    apply noFour (fourOfCommon diff ab ha hb ?_ ?_) <;> grind
  obtain ⟨z,hz,za,zb,zx⟩ : ∃ z, G.adj y z ∧ z ≠ a ∧ z ≠ b ∧ z ≠ x := by
    rcases eligible with e | e
    · exact ⟨c,hc,e.1,e.2,cx⟩
    · exact ⟨d,hd,e.1,e.2,dx⟩
  exact ⟨some ⟨a,by grind [Graph.loopless],ay⟩,some ⟨b,by grind [Graph.loopless],by'⟩,
    some ⟨z,zx,by grind [Graph.loopless]⟩,Or.inl ha,Or.inl hb,Or.inr hz,
    by simp; grind,by simp; grind,by simp; grind⟩

theorem minDegree {G : Graph V} (deg : MinDegreeThree G) {x y : V} (diff : x ≠ y)
    (noFour : ¬ HasCycle G 4) (heavy : ∀ w, G.adj w x → G.adj w y → AtLeastFour G w) :
    MinDegreeThree (graph G x y) := by
  intro v
  cases v with
  | some w => exact threeAtOutside w (deg w.val) (heavy w.val)
  | none => exact threeAtMerged diff noFour (extraTwo deg x y) (extraTwo deg y x)

private theorem nextVal {k : Nat} (i : Fin k) :
    (cycleNext i).val = if i.val+1 = k then 0 else i.val+1 := by
  split
  next h => simp [cycleNext,h]
  next h => exact Nat.mod_eq_of_lt (by omega)

theorem nextInjective {k : Nat} {i j : Fin k} (h : cycleNext i = cycleNext j) : i = j := by
  have e := congrArg Fin.val h
  rw [nextVal,nextVal] at e
  apply Fin.ext
  split at e <;> split at e <;> omega

private theorem hasPrevious {k : Nat} (i : Fin k) : ∃ p : Fin k, cycleNext p = i := by
  by_cases e : i.val = 0
  · refine ⟨⟨k-1,by omega⟩, Fin.ext ?_⟩
    simp only [nextVal]
    split <;> omega
  · refine ⟨⟨i.val-1,by omega⟩,Fin.ext ?_⟩
    simp only [nextVal]
    split <;> omega

private theorem liftAway {x y : V} (a b : V) (z : Identified x y) (h : z ≠ none) :
    lift x y a z = lift x y b z := by cases z <;> simp_all [lift]

private theorem ordinaryEdge {G : Graph V} {x y a : V} {v w : Identified x y}
    (nv : v ≠ none) (nw : w ≠ none) (h : (graph G x y).adj v w) :
    G.adj (lift x y a v) (lift x y a w) := by
  cases v <;> cases w <;> simp_all [lift,graph]

private theorem rootEdge {G : Graph V} {x y : V} {z : Identified x y}
    (h : (graph G x y).adj none z) :
    ∃ a, (a = x ∨ a = y) ∧ G.adj a (lift x y x z) := by
  cases z with
  | none => contradiction
  | some w =>
    rcases h with h | h
    · exact ⟨x,Or.inl rfl,h⟩
    · exact ⟨y,Or.inr rfl,h⟩

/-- Any simple cycle in the quotient lifts to a simple cycle of the same length
or to a simple path of that length between the two identified vertices. -/
private theorem cycleOrSplitPath {G : Graph V} {x y : V} {k : Nat} (h : HasCycle (graph G x y) k) :
    HasCycle G k ∨ HasSplitPath G x y k := by
  classical
  obtain ⟨f,inj,edges⟩ := h
  have inject (a : V) (side : a = x ∨ a = y) :
      ∀ i j, lift x y a (f i) = lift x y a (f j) → i = j := by
    intro i j eq
    exact inj i j (by simpa only [image_lift side] using congrArg (image x y) eq)
  by_cases through : ∃ i, f i = none
  · obtain ⟨r,root⟩ := through
    obtain ⟨p,prev⟩ := hasPrevious r
    have after : (graph G x y).adj none (f (cycleNext r)) := root ▸ edges r
    have before : (graph G x y).adj none (f p) := by
      simpa only [prev,root] using (graph G x y).symm (edges p)
    obtain ⟨a,ha,outEdge⟩ := rootEdge after
    obtain ⟨b,hb,inEdge⟩ := rootEdge before
    let seq := fun i => lift x y a (f i)
    have start : seq r = a := by simp [seq,root,lift]
    have outside (i : Fin k) (ne : i ≠ r) : f i ≠ none :=
      fun e => ne (inj i r (e.trans root.symm))
    have nextEdges (i : Fin k) (ne : cycleNext i ≠ r) : G.adj (seq i) (seq (cycleNext i)) := by
      by_cases e : i = r
      · subst i; rw [start]; simpa only [seq,liftAway a x _ (outside _ ne)] using outEdge
      · exact ordinaryEdge (outside _ e) (outside _ ne) (edges i)
    have toLast (i : Fin k) (e : cycleNext i = r) : G.adj (seq i) b := by
      have ie := nextInjective (e.trans prev.symm)
      subst i
      have np : f p ≠ none := fun e => (graph G x y).loopless none (e ▸ before)
      simpa only [seq,liftAway a x _ np] using G.symm inEdge
    by_cases eq : a = b
    · left
      refine ⟨seq,inject a ha,?_⟩
      intro i
      by_cases e : cycleNext i = r
      · simpa only [e,start,eq] using toLast i e
      · exact nextEdges i e
    · right
      refine ⟨r,seq,a,b,by grind,start,inject a ha,?_,?_⟩
      · intro i
        cases h : f i with
        | none => simpa only [seq,h,lift] using eq
        | some z =>
          change lift x y a (f i) ≠ b
          rw [h]
          exact fun e => by have := z.property; change z.val = b at e; grind
      · intro i
        split
        next e => exact toLast i e
        next ne => exact nextEdges i ne
  · left
    exact ⟨fun i => lift x y x (f i),inject x (Or.inl rfl),fun i =>
      ordinaryEdge (fun e => through ⟨i,e⟩) (fun e => through ⟨cycleNext i,e⟩) (edges i)⟩

/-- Index `t` after the distinguished start of a cyclic enumeration. -/
def rotate {k : Nat} (r : Fin k) (t : Nat) : Fin k :=
  ⟨(r.val + t) % k, Nat.mod_lt _ r.pos⟩

theorem rotZero {k : Nat} (r : Fin k) : rotate r 0 = r := by
  apply Fin.ext
  simp [rotate,Nat.mod_eq_of_lt r.isLt]

theorem rotLast {k : Nat} (r : Fin k) : rotate r k = r := by
  apply Fin.ext
  simp [rotate,Nat.mod_eq_of_lt r.isLt]

theorem rotStep {k : Nat} (r : Fin k) (t : Nat) :
    cycleNext (rotate r t) = rotate r (t+1) := by
  apply Fin.ext
  simp only [rotate,cycleNext,Nat.mod_add_mod,Nat.add_assoc]

private theorem rotValue {k : Nat} (r : Fin k) {t : Nat} (ht : t < k) :
    (rotate r t).val = if r.val+t < k then r.val+t else r.val+t-k := by
  change (r.val+t)%k = _
  split
  next h => exact Nat.mod_eq_of_lt h
  next h =>
    rw [Nat.mod_eq_sub_mod (by omega : k ≤ r.val+t),Nat.mod_eq_of_lt (by omega)]

theorem rotInjective {k : Nat} (r : Fin k) {i j : Nat} (hi : i < k) (hj : j < k)
    (h : rotate r i = rotate r j) : i = j := by
  have e := congrArg Fin.val h
  rw [rotValue r hi,rotValue r hj] at e
  split at e <;> split at e <;> omega

private theorem straightPath {G : Graph V} {x y : V} {k : Nat} (h : HasSplitPath G x y k) :
    HasSimplePathBetween G x y k := by
  obtain ⟨r,v,a,b,ends,start,inj,noB,steps⟩ := h
  let f (i : Fin (k+1)) := if i.val = k then b else v (rotate r i.val)
  have pos := r.pos
  refine ⟨f,?_,?_,?_⟩
  · simpa [f,show 0 ≠ k by omega,rotZero,start] using ends
  · intro i j e
    apply Fin.ext
    by_cases hi : i.val = k <;> by_cases hj : j.val = k
    · omega
    · simp only [f,hi,hj,ite_true,ite_false] at e
      exact False.elim (noB _ e.symm)
    · simp only [f,hi,hj,ite_true,ite_false] at e
      exact False.elim (noB _ e)
    · apply rotInjective r (by omega) (by omega)
      apply inj
      simpa only [f,hi,hj,ite_false] using e
  · intro i
    have st := steps (rotate r i.val)
    have ne : i.val ≠ k := by omega
    by_cases last : i.val+1 = k
    · simpa only [rotStep,last,rotLast,ite_true,f,Fin.val_castSucc,Fin.val_succ,ne,ite_false]
        using st
    · have notRoot : rotate r (i.val+1) ≠ r := by
        intro e
        have := rotInjective r (by omega : i.val+1 < k) (by omega : 0 < k) (e.trans (rotZero r).symm)
        omega
      simpa only [rotStep,notRoot,ite_false,f,Fin.val_castSucc,Fin.val_succ,ne,last] using st

/-- Any simple cycle in the quotient lifts to a simple cycle of the same length
or to a simple path of that length between the two identified vertices. -/
theorem cycleOrPath {G : Graph V} {x y : V} {k : Nat} (h : HasCycle (graph G x y) k) :
    HasCycle G k ∨ HasSimplePathBetween G x y k :=
  (cycleOrSplitPath h).imp id straightPath

/-- The list of projected vertices loses one entry when it is formed after
removing `y`: the common image already occurs at `x`. -/
theorem shorterCover {x y : V} (ne : x ≠ y) (vertices : List V)
    (covers : ∀ v, v ∈ vertices) :
    ∃ l : List (Identified x y), l.length < vertices.length ∧ ∀ z, z ∈ l := by
  classical
  let l := (vertices.erase y).map (image x y)
  refine ⟨l,?_,?_⟩
  · have hy := covers y
    have hp : 0 < vertices.length := List.length_pos_of_mem hy
    simp only [l,List.length_map,List.length_erase_of_mem hy]
    omega
  · intro z
    let v := lift x y x z
    have vy : v ≠ y := by
      cases z with
      | none => exact ne
      | some w => exact w.property.2
    exact List.mem_map.mpr ⟨v,(List.mem_erase_of_ne vy).mpr (covers v), image_lift (Or.inl rfl) z⟩

end Identification

/-- Minimum possible order among all finite counterexamples. A covering list in
the minimality hypothesis may repeat vertices, so its length is an upper bound
on the smaller graph's order. The given graph uses a repetition-free list. -/
structure MinimumOrderCounterexample {V : Type u} (G : Graph V) where
  vertices : List V
  distinct : vertices.Nodup
  covers : ∀ v, v ∈ vertices
  nonempty : Nonempty V
  degree : MinDegreeThree G
  avoids : ¬ HasDyadicCycle G
  smaller : ∀ {W : Type u} (H : Graph W) (l : List W), Nonempty W →
    (∀ w, w ∈ l) → l.length < vertices.length → MinDegreeThree H → HasDyadicCycle H

/-- In a counterexample of minimum order, two distinct vertices whose common
neighbors all have degree at least four are joined by a power-of-two path. -/
theorem dyadicPath_of_minimumOrder {V : Type u} {G : Graph V}
    (minimal : MinimumOrderCounterexample G) {x y : V} (ne : x ≠ y)
    (heavy : ∀ w, G.adj w x → G.adj w y → Identification.AtLeastFour G w) :
    ∃ k : Nat, 2 ≤ k ∧ HasSimplePathBetween G x y (2^k) := by
  have noFour : ¬ HasCycle G 4 := fun h => minimal.avoids ⟨2,by decide,h⟩
  obtain ⟨l,len,all⟩ := Identification.shorterCover ne minimal.vertices minimal.covers
  obtain ⟨k,hk,cycle⟩ := minimal.smaller (Identification.graph G x y) l ⟨none⟩ all len
    (Identification.minDegree minimal.degree ne noFour heavy)
  rcases Identification.cycleOrPath cycle with old | path
  · exact False.elim (minimal.avoids ⟨k,hk,old⟩)
  · exact ⟨k,hk,path⟩

/-- The specified edge closes the cyclic order between its last and its
first vertex. The endpoints can occur in either orientation. -/
def HasCycleThroughEdge {V : Type u} (G : Graph V) (x y : V) (n : Nat) : Prop :=
  ∃ f : Fin n → V, (∀ i j, f i = f j → i = j) ∧
    (∀ i, G.adj (f i) (f (cycleNext i))) ∧
    ∃ i, (f i = x ∧ f (cycleNext i) = y) ∨ (f i = y ∧ f (cycleNext i) = x)

private theorem closePath {V : Type u} {G : Graph V} {x y : V} {n : Nat}
    (adj : G.adj x y) (path : HasSimplePathBetween G x y n) :
    HasCycleThroughEdge G x y (n+1) := by
  obtain ⟨f,ends,inj,steps⟩ := path
  have last : cycleNext (Fin.last n) = 0 := Fin.ext (by simp [cycleNext,Fin.last])
  refine ⟨f,inj,?_,Fin.last n,by rw [last]; grind⟩
  intro i
  by_cases eq : i.val = n
  · have e : i = Fin.last n := Fin.ext eq
    rw [e,last]; grind [→ Graph.symm]
  · have hi : i.val < n := by omega
    have e : cycleNext i = (⟨i.val,hi⟩ : Fin n).succ := Fin.ext (Nat.mod_eq_of_lt (by omega))
    rw [e]
    exact steps ⟨i.val,hi⟩

/-- Every eligible edge of a minimum-order counterexample belongs to a cycle
of length one more than a power of two. In particular an edge outside all
triangles is eligible. -/
theorem oddCycleThroughEdge_of_minimumOrder {V : Type u} {G : Graph V}
    (minimal : MinimumOrderCounterexample G) {x y : V} (adj : G.adj x y)
    (heavy : ∀ w, G.adj w x → G.adj w y → Identification.AtLeastFour G w) :
    ∃ k : Nat, 2 ≤ k ∧ HasCycleThroughEdge G x y (2^k+1) := by
  obtain ⟨k,hk,path⟩ := dyadicPath_of_minimumOrder minimal (x := x) (y := y) (fun e => G.loopless y (e ▸ adj)) heavy
  exact ⟨k,hk,closePath adj path⟩

/-- A cubic vertex has a neighbor outside all triangles through their edge:
two edges of the three-vertex neighborhood would give a 4-cycle. Hence the
specified cubic vertex itself lies on a dyadic-plus-one cycle. -/
theorem oddCycleAtCubic_of_minimumOrder {V : Type u} {G : Graph V}
    (minimal : MinimumOrderCounterexample G) (x : V)
    (cubic : ∃ a b c, ∀ w, G.adj x w → w = a ∨ w = b ∨ w = c) :
    ∃ y, G.adj x y ∧ ∃ k : Nat, 2 ≤ k ∧ HasCycleThroughEdge G x y (2^k+1) := by
  obtain ⟨a,b,c,ha,hb,hc,ab,ac,bc⟩ := minimal.degree x
  obtain ⟨p,q,r,all⟩ := cubic
  have exhaust (w : V) (e : G.adj x w) : w = a ∨ w = b ∨ w = c := by
    have := all a ha; have := all b hb; have := all c hc; have := all w e
    grind
  have noFour : ¬ HasCycle G 4 := fun h => minimal.avoids ⟨2,by decide,h⟩
  have isolated (u v w : V) (xu : G.adj x u) (xv : G.adj x v) (xw : G.adj x w)
      (vw : v ≠ w) : ¬ (G.adj u v ∧ G.adj u w) := by
    intro ⟨uv,uw⟩
    exact noFour (Identification.fourOfCommon (x := x) (y := u) (fun h => G.loopless u (h ▸ xu)) vw xv xw uv uw)
  have first := isolated a b c ha hb hc bc
  have second := isolated b a c hb ha hc ac
  have third := isolated c a b hc ha hb ab
  have choose : ∃ y, G.adj x y ∧ ∀ w, G.adj w x → ¬G.adj w y := by
    by_cases e : G.adj a b
    · refine ⟨c,hc,?_⟩
      intro w wx; have := exhaust w (G.symm wx); grind [→ Graph.symm,Graph.loopless]
    · by_cases f : G.adj a c
      · refine ⟨b,hb,?_⟩
        intro w wx; have := exhaust w (G.symm wx); grind [→ Graph.symm,Graph.loopless]
      · refine ⟨a,ha,?_⟩
        intro w wx; have := exhaust w (G.symm wx); grind [→ Graph.symm,Graph.loopless]
  obtain ⟨y,xy,none⟩ := choose
  exact ⟨y,xy,oddCycleThroughEdge_of_minimumOrder minimal xy
    (fun w wx wy => False.elim (none w wx wy))⟩

theorem pathColorParity {V : Type u} {G : Graph V} {x y : V} {n : Nat}
    (color : V → Bool) (proper : ∀ a b, G.adj a b → color a ≠ color b)
    (path : HasSimplePathBetween G x y n) : color x = color y ↔ n % 2 = 0 := by
  obtain ⟨f,ends,_,steps⟩ := path
  have parity (t : Nat) (ht : t ≤ n) :
      color (f ⟨t,by omega⟩) = if t%2 = 0 then color (f 0) else !(color (f 0)) := by
    induction t with
    | zero => simp
    | succ t ih =>
      have before := ih (by omega)
      have h := proper _ _ (steps ⟨t,by omega⟩)
      change color (f ⟨t,_⟩) ≠ color (f ⟨t+1,_⟩) at h
      have flip (a b : Bool) (h : a ≠ b) : b = !a := by cases a <;> cases b <;> simp_all
      rw [flip _ _ h,before]
      split <;> split <;> first | omega | simp
  have last := parity n (Nat.le_refl _)
  change color (f (Fin.last n)) = (if n%2=0 then color (f 0) else !(color (f 0))) at last
  rcases ends with ⟨a,b⟩ | ⟨a,b⟩ <;> rw [a,b] at last <;>
    split at last <;> cases hx : color x <;> cases hy : color y <;> simp_all

/-- A counterexample of minimum order among all finite graphs cannot have a
proper two-coloring. Minimality within bipartite graphs alone is weaker. -/
theorem minimumOrder_not_bipartite {V : Type u} {G : Graph V}
    (minimal : MinimumOrderCounterexample G) :
    ¬ ∃ color : V → Bool, ∀ x y, G.adj x y → color x ≠ color y := by
  intro ⟨color,proper⟩
  let x := Classical.choice minimal.nonempty
  obtain ⟨y,_,_,xy,_,_,_,_,_⟩ := minimal.degree x
  have diff := proper x y xy
  have heavy (w : V) (wx : G.adj w x) (wy : G.adj w y) : Identification.AtLeastFour G w := by
    have hx := proper w x wx
    have hy := proper w y wy
    cases h₁ : color w <;> cases h₂ : color x <;> cases h₃ : color y <;> grind
  obtain ⟨k,hk,path⟩ := dyadicPath_of_minimumOrder minimal (x := x) (y := y) (fun e => G.loopless y (e ▸ xy)) heavy
  apply diff ((pathColorParity color proper path).2 ?_)
  cases k with
  | zero => omega
  | succ k => rw [Nat.pow_succ]; omega

end Erdos64
