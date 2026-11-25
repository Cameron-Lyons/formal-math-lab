import Erdos64.Identification

/-! Consequences of the unrestricted finite-graph conjecture for graphs with
two distinguished vertices of degree at least two. -/
namespace Erdos64
namespace Terminals

universe u

/-- The unrestricted conjecture, with a covering list witnessing finiteness. -/
def Conjecture : Prop := ∀ {V : Type u} (G : Graph V), Nonempty V →
  (∃ l : List V, ∀ v, v ∈ l) → MinDegreeThree G → HasDyadicCycle G

def TwoAt {V : Type u} (G : Graph V) (x : V) : Prop :=
  ∃ a b, G.adj x a ∧ G.adj x b ∧ a ≠ b

def ThreeAt {V : Type u} (G : Graph V) (x : V) : Prop :=
  ∃ a b c, G.adj x a ∧ G.adj x b ∧ G.adj x c ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c

variable {V : Type u}

def addEdge (G : Graph V) (x y : V) (ne : x ≠ y) : Graph V where
  adj v w := G.adj v w ∨ (v = x ∧ w = y) ∨ (v = y ∧ w = x)
  symm := by grind [→ Graph.symm]
  loopless := by grind [Graph.loopless]

/-- Deleting the potentially added edge of a cycle leaves a simple path from
one endpoint to the other with one fewer edge. -/
private theorem removeEdge {G : Graph V} {x y : V} {ne : x ≠ y} {n : Nat}
    (cycle : HasCycle (addEdge G x y ne) (n+3)) :
    HasCycle G (n+3) ∨ HasSimplePathBetween G x y (n+2) := by
  classical
  obtain ⟨f,inj,steps⟩ := cycle
  by_cases all : ∀ i, G.adj (f i) (f (cycleNext i))
  · exact Or.inl ⟨f,inj,all⟩
  · obtain ⟨i,bad⟩ : ∃ i, ¬G.adj (f i) (f (cycleNext i)) := by
      apply Classical.byContradiction
      intro no; exact all (fun i => Classical.byContradiction (fun h => no ⟨i,h⟩))
    let r := cycleNext i
    let g (j : Fin (n+3)) := f (Identification.rotate r j.val)
    have start : g 0 = f r := by simp [g,Identification.rotZero]
    have last : g (Fin.last (n+2)) = f i := by
      apply congrArg f
      apply Identification.nextInjective
      change cycleNext (Identification.rotate r (n+2)) = r
      simp only [Identification.rotStep, Identification.rotLast]
    have ends : (g 0 = x ∧ g (Fin.last (n+2)) = y) ∨
        (g 0 = y ∧ g (Fin.last (n+2)) = x) := by
      have e := steps i
      change G.adj (f i) (f (cycleNext i)) ∨ _ at e
      rw [start,last]; change (f (cycleNext i) = x ∧ f i = y) ∨ _; grind
    have gi (a b : Fin (n+3)) (eq : g a = g b) : a = b :=
      Fin.ext (Identification.rotInjective r a.isLt b.isLt (inj _ _ eq))
    right; refine ⟨g,ends,gi,?_⟩
    intro j
    have e := steps (Identification.rotate r j.val)
    rw [Identification.rotStep] at e
    change G.adj (g j.castSucc) (g j.succ) ∨
      (g j.castSucc = x ∧ g j.succ = y) ∨ (g j.castSucc = y ∧ g j.succ = x) at e
    rcases e with e | alt
    · exact e
    · have notBoth : ¬ ((g j.castSucc = g 0 ∧ g j.succ = g (Fin.last (n+2))) ∨
          (g j.castSucc = g (Fin.last (n+2)) ∧ g j.succ = g 0)) := by
        intro h
        rcases h with ⟨p,q⟩ | ⟨p,q⟩ <;>
          have hp := congrArg Fin.val (gi _ _ p) <;>
          have hq := congrArg Fin.val (gi _ _ q) <;> simp only [Fin.val_castSucc,Fin.val_succ,Fin.val_zero,Fin.val_last] at hp hq <;> omega
      grind

theorem dyadicRemove {G : Graph V} {x y : V} {ne : x ≠ y}
    (cycle : HasDyadicCycle (addEdge G x y ne)) :
    HasDyadicCycle G ∨ ∃ k, 2 ≤ k ∧ HasSimplePathBetween G x y (2^k-1) := by
  obtain ⟨k,hk,h⟩ := cycle
  have len : 4 ≤ 2^k := Nat.pow_le_pow_right (by decide : 0 < 2) hk
  have eq : 2^k = (2^k-3)+3 := by omega
  rw [eq] at h
  rcases removeEdge h with old | path
  · exact Or.inl ⟨k,hk,eq ▸ old⟩
  · exact Or.inr ⟨k,hk,(show (2^k-3)+2 = 2^k-1 by omega) ▸ path⟩

private def layers (G : Graph V) : Graph (Bool × V) where
  adj a b := a.1 = b.1 ∧ G.adj a.2 b.2
  symm := by grind [→ Graph.symm]
  loopless := by simp [Graph.loopless]

private theorem layerConstant {G : Graph V} {n : Nat} (f : Fin (n+1) → Bool × V)
    (edges : ∀ i : Fin n, (layers G).adj (f i.castSucc) (f i.succ)) :
    ∀ i, (f i).1 = (f 0).1 := by
  intro ⟨t,ht⟩
  induction t with
  | zero => rfl
  | succ t ih => exact ((edges ⟨t,by omega⟩).1).symm.trans (ih (by omega))

private theorem layerCycle {G : Graph V} {k : Nat} (cycle : HasCycle (layers G) k) :
    HasCycle G k := by
  cases k with
  | zero =>
    obtain ⟨f,_,_⟩ := cycle
    exact ⟨fun i => (f i).2,fun i => Fin.elim0 i,fun i => Fin.elim0 i⟩
  | succ n =>
    obtain ⟨f,inj,edges⟩ := cycle
    have same := layerConstant f (G := G) (fun i => (show (layers G).adj (f i.castSucc) (f i.succ) by
      have e : cycleNext i.castSucc = i.succ := Fin.ext (Nat.mod_eq_of_lt (show i.val+1 < n+1 by omega))
      simpa only [e] using edges i.castSucc))
    exact ⟨fun i => (f i).2,fun i j e => inj _ _ (Prod.ext ((same i).trans (same j).symm) e),
      fun i => (edges i).2⟩

/-- Two disjoint copies joined by a single bridge at the exceptional vertex
remove a one-vertex degree deficit without creating any new simple cycle. -/
theorem oneDefect (eg : Conjecture.{u}) (G : Graph V) (l : List V) (all : ∀ v, v ∈ l)
    (w : V) (dw : TwoAt G w) (others : ∀ v, v ≠ w → ThreeAt G v) : HasDyadicCycle G := by
  let a : Bool × V := (false,w)
  let b : Bool × V := (true,w)
  have ne : a ≠ b := by simp [a,b]
  let H := addEdge (layers G) a b ne
  have degH : MinDegreeThree H := by
    intro ⟨side,v⟩
    by_cases eq : v = w
    · subst v
      obtain ⟨p,q,hp,hq,pq⟩ := dw
      refine ⟨(side,p),(side,q),(!side,w),Or.inl ⟨rfl,hp⟩,Or.inl ⟨rfl,hq⟩,?_,?_,?_,?_⟩
      · cases side <;> simp [H,addEdge,a,b]
      · simp [pq]
      · cases side <;> simp
      · cases side <;> simp
    · obtain ⟨p,q,r,hp,hq,hr,pq,pr,qr⟩ := others v eq
      exact ⟨(side,p),(side,q),(side,r),Or.inl ⟨rfl,hp⟩,Or.inl ⟨rfl,hq⟩,Or.inl ⟨rfl,hr⟩,
        by simp [pq],by simp [pr],by simp [qr]⟩
  have finite : ∃ l' : List (Bool × V), ∀ v, v ∈ l' := by
    refine ⟨(l.map (fun v => (false,v))) ++ (l.map (fun v => (true,v))),?_⟩
    intro ⟨s,v⟩; cases s <;> simp [all]
  rcases dyadicRemove (G := layers G) (x := a) (y := b) (eg H ⟨a⟩ finite degH) with cycle | ⟨k,_,path⟩
  · obtain ⟨k,hk,cycle⟩ := cycle; exact ⟨k,hk,layerCycle cycle⟩
  · obtain ⟨f,ends,_,steps⟩ := path
    have same := layerConstant f steps (Fin.last (2^k-1))
    rcases ends with ⟨e₁,e₂⟩ | ⟨e₁,e₂⟩ <;> simp [a,b,e₁,e₂] at same

private theorem mergedDefect {G : Graph V} {x y : V} (ne : x ≠ y) (far : ¬G.adj x y)
    (dx : TwoAt G x) (dy : TwoAt G y) (others : ∀ v, v ≠ x → v ≠ y → ThreeAt G v)
    (noFour : ¬ HasCycle G 4) :
    let Q := Identification.graph G x y
    ∃ z, TwoAt Q z ∧ ∀ w, w ≠ z → ThreeAt Q w := by
  let Q := Identification.graph G x y
  have merged : ThreeAt Q none := by
    apply Identification.threeAtMerged ne noFour
    · obtain ⟨a,b,ha,hb,ab⟩ := dx; exact ⟨a,b,ha,hb,ab,by grind,by grind⟩
    · obtain ⟨a,b,ha,hb,ab⟩ := dy; exact ⟨a,b,ha,hb,ab,by grind [→ Graph.symm],by grind [→ Graph.symm]⟩
  let Common (w : {v : V // v ≠ x ∧ v ≠ y}) := G.adj w.val x ∧ G.adj w.val y
  have ordinary (w : {v : V // v ≠ x ∧ v ≠ y}) (h : ¬ Common w) : ThreeAt Q (some w) :=
    Identification.threeAtOutside w (others w.val w.property.1 w.property.2)
      (fun a b => False.elim (h ⟨a,b⟩))
  by_cases ex : ∃ w, Common w
  · obtain ⟨z,hx,hy⟩ := ex
    have dz := others z.val z.property.1 z.property.2
    obtain ⟨a,b,c,ha,hb,hc,ab,ac,bc⟩ := dz
    have out : ∃ p, G.adj z.val p ∧ p ≠ x ∧ p ≠ y := by
      by_cases aout : a ≠ x ∧ a ≠ y
      · exact ⟨a,ha,aout⟩
      · by_cases bout : b ≠ x ∧ b ≠ y
        · exact ⟨b,hb,bout⟩
        · exact ⟨c,hc,by grind,by grind⟩
    obtain ⟨p,hp,px,py⟩ := out
    refine ⟨some z,⟨none,some ⟨p,px,py⟩,Or.inl hx,hp,by simp⟩,?_⟩
    intro w diff
    cases w with
    | none => exact merged
    | some w =>
      apply ordinary w
      intro ⟨wx,wy⟩
      exact noFour (Identification.fourOfCommon ne
        (show z.val ≠ w.val from fun e => diff (by rw [Subtype.ext e]))
        (G.symm hx) (G.symm wx) (G.symm hy) (G.symm wy))
  · obtain ⟨a,b,c,ha,hb,_,ab,_,_⟩ := merged
    refine ⟨none,⟨a,b,ha,hb,ab⟩,?_⟩
    intro w diff
    cases w with
    | none => contradiction
    | some w => exact ordinary w (fun h => ex ⟨w,h⟩)

/-- Adding the missing terminal edge supplies a third neighbor at both ends. -/
theorem degreeWithTerminalEdge {G : Graph V} {x y : V} (ne : x ≠ y) (far : ¬G.adj x y)
    (dx : TwoAt G x) (dy : TwoAt G y) (others : ∀ v, v ≠ x → v ≠ y → ThreeAt G v) :
    MinDegreeThree (addEdge G x y ne) := by
  intro w
  by_cases wx : w = x
  · subst w
    obtain ⟨a,b,ha,hb,ab⟩ := dx
    exact ⟨a,b,y,Or.inl ha,Or.inl hb,Or.inr (Or.inl ⟨rfl,rfl⟩),ab,by grind,by grind⟩
  · by_cases wy : w = y
    · subst w
      obtain ⟨a,b,ha,hb,ab⟩ := dy
      exact ⟨a,b,x,Or.inl ha,Or.inl hb,Or.inr (Or.inr ⟨rfl,rfl⟩),ab,
        by grind [→ Graph.symm],by grind [→ Graph.symm]⟩
    · obtain ⟨a,b,c,ha,hb,hc,ab,ac,bc⟩ := others w wx wy
      exact ⟨a,b,c,Or.inl ha,Or.inl hb,Or.inl hc,ab,ac,bc⟩

/-- Assuming the unrestricted conjecture, a graph with two nonadjacent
terminals of degree at least two and minimum degree three elsewhere contains
a dyadic cycle, or it has terminal paths of both indicated lengths. The
exponents may differ. -/
theorem cycleOrTerminalPaths (eg : Conjecture.{u}) {G : Graph V} (l : List V) (all : ∀ v, v ∈ l)
    {x y : V} (ne : x ≠ y) (far : ¬G.adj x y) (dx : TwoAt G x) (dy : TwoAt G y)
    (others : ∀ v, v ≠ x → v ≠ y → ThreeAt G v) :
    HasDyadicCycle G ∨
    ((∃ k : Nat, 2 ≤ k ∧ HasSimplePathBetween G x y (2^k)) ∧
     (∃ k : Nat, 2 ≤ k ∧ HasSimplePathBetween G x y (2^k-1))) := by
  by_cases old : HasDyadicCycle G
  · exact Or.inl old
  right
  constructor
  · let Q := Identification.graph G x y
    have noFour : ¬HasCycle G 4 := fun h => old ⟨2,by decide,h⟩
    obtain ⟨w,two,rest⟩ := mergedDefect ne far dx dy others noFour
    obtain ⟨cover,_,covered⟩ := Identification.shorterCover ne l all
    obtain ⟨k,hk,h⟩ := oneDefect eg Q cover covered w two rest
    rcases Identification.cycleOrPath h with h | path
    · exact False.elim (old ⟨k,hk,h⟩)
    · exact ⟨k,hk,path⟩
  · have d := degreeWithTerminalEdge ne far dx dy others
    exact (dyadicRemove (eg (addEdge G x y ne) ⟨x⟩ ⟨l,all⟩ d)).resolve_left old

/-- A universal terminal-path statement with a specified sequence of target
lengths, allowing disconnected finite host graphs. -/
def TerminalPrinciple (length : Nat → Nat) : Prop :=
  ∀ {V : Type u} (G : Graph V) (l : List V), (∀ v, v ∈ l) →
  ∀ x y, x ≠ y → ¬G.adj x y → TwoAt G x → TwoAt G y →
    (∀ v, v ≠ x → v ≠ y → ThreeAt G v) →
    HasDyadicCycle G ∨ ∃ k : Nat, 2 ≤ k ∧ HasSimplePathBetween G x y (length k)

private theorem conjectureOfTerminal {length : Nat → Nat}
    (principle : TerminalPrinciple.{u} length) : Conjecture.{u} := by
  intro V G nonempty finite degree
  obtain ⟨l,all⟩ := finite
  let v := Classical.choice nonempty
  let a : Bool × V := (false,v)
  let b : Bool × V := (true,v)
  have deg (z : Bool × V) : ThreeAt (layers G) z := by
    obtain ⟨p,q,r,hp,hq,hr,pq,pr,qr⟩ := degree z.2
    exact ⟨(z.1,p),(z.1,q),(z.1,r),⟨rfl,hp⟩,⟨rfl,hq⟩,⟨rfl,hr⟩,
      by simp [pq],by simp [pr],by simp [qr]⟩
  have two (z : Bool × V) : TwoAt (layers G) z := by
    obtain ⟨p,q,_,hp,hq,_,pq,_,_⟩ := deg z; exact ⟨p,q,hp,hq,pq⟩
  let labels := (l.map (fun z => (false,z))) ++ (l.map (fun z => (true,z)))
  have cov : ∀ z, z ∈ labels := by intro ⟨s,z⟩; cases s <;> simp [labels,all]
  rcases principle (layers G) labels cov a b (by simp [a,b]) (by simp [layers,a,b])
    (two a) (two b) (fun z _ _ => deg z) with cycle | ⟨k,_,path⟩
  · obtain ⟨k,hk,cycle⟩ := cycle; exact ⟨k,hk,layerCycle cycle⟩
  · obtain ⟨f,ends,_,steps⟩ := path
    have same := layerConstant f steps (Fin.last (length k))
    rcases ends with ⟨e₁,e₂⟩ | ⟨e₁,e₂⟩ <;> simp [a,b,e₁,e₂] at same

/-- Each individual length sequence already characterizes the unrestricted
conjecture when terminal graphs of arbitrary connectivity are allowed. -/
theorem terminalEquivalences :
    (Conjecture.{u} ↔ TerminalPrinciple.{u} (fun k => 2^k)) ∧
    (Conjecture.{u} ↔ TerminalPrinciple.{u} (fun k => 2^k-1)) := by
  constructor
  · refine ⟨?_,conjectureOfTerminal⟩
    intro eg V G l all x y ne far dx dy others
    exact (cycleOrTerminalPaths eg l all ne far dx dy others).imp id And.left
  · refine ⟨?_,conjectureOfTerminal⟩
    intro eg V G l all x y ne far dx dy others
    exact (cycleOrTerminalPaths eg l all ne far dx dy others).imp id And.right

/-- Reachability by a finite walk starting at a chosen vertex. -/
inductive Reach (G : Graph V) (root : V) : V → Prop
  | refl : Reach G root root
  | step {v w} : Reach G root v → G.adj v w → Reach G root w

def Connected (G : Graph V) : Prop := ∃ root, ∀ v, Reach G root v

def ExactlyTwoAt (G : Graph V) (x : V) : Prop :=
  ∃ a b, a ≠ b ∧ ∀ w, G.adj x w ↔ w = a ∨ w = b

private theorem ExactlyTwoAt.two {G : Graph V} {x : V} (h : ExactlyTwoAt G x) : TwoAt G x := by
  obtain ⟨a,b,ne,all⟩ := h
  exact ⟨a,b,(all a).2 (Or.inl rfl),(all b).2 (Or.inr rfl),ne⟩

private theorem labelOnWalk {W : Type u} {T : Type v} {n : Nat} (f : Fin (n+1) → W) (tag : W → T)
    (step : ∀ i : Fin n, tag (f i.castSucc) = tag (f i.succ)) :
    ∀ i, tag (f i) = tag (f 0) := by
  intro ⟨i,hi⟩; induction i with
  | zero => rfl
  | succ j ih => exact (step ⟨j,by omega⟩).symm.trans (ih (by omega))

private theorem labelOnPath {G : Graph V} {x y : V} {n : Nat} {T : Type v} (tag : V → T)
    (stable : ∀ v w, G.adj v w → tag v = tag w) (p : HasSimplePathBetween G x y n) :
    tag x = tag y := by
  obtain ⟨f,ends,_,step⟩ := p
  have same := labelOnWalk f tag (fun i => stable _ _ (step i)) (Fin.last n)
  grind

private theorem removeBridge {G : Graph V} {x y : V} {ne : x ≠ y}
    (tag : V → Bool) (distinct : tag x ≠ tag y) (stable : ∀ v w, G.adj v w → tag v = tag w)
    (cycle : HasDyadicCycle (addEdge G x y ne)) : HasDyadicCycle G := by
  rcases dyadicRemove cycle with h | ⟨_,_,p⟩
  · exact h
  · exact False.elim (distinct (labelOnPath tag stable p))

private def component (G : Graph V) (root : V) : Graph {x // Reach G root x} where
  adj v w := G.adj v.val w.val
  symm := G.symm
  loopless := fun v => G.loopless v.val

private theorem componentConnected (G : Graph V) (root : V) :
    Connected (component G root) := by
  refine ⟨⟨root,Reach.refl⟩,?_⟩
  intro ⟨v,h⟩
  induction h with
  | refl => exact Reach.refl
  | step path edge ih => exact Reach.step ih edge

private theorem componentDegree {G : Graph V} (root : V) (deg : MinDegreeThree G) :
    MinDegreeThree (component G root) := by
  intro ⟨v,path⟩
  obtain ⟨a,b,c,ha,hb,hc,ab,ac,bc⟩ := deg v
  exact ⟨⟨a,path.step ha⟩,⟨b,path.step hb⟩,⟨c,path.step hc⟩,ha,hb,hc,
    by simp [ab],by simp [ac],by simp [bc]⟩

/-- Three separate copies of a graph, along with the two new terminals. -/
private inductive Copies (V : Type u)
  | left (v : V)
  | middle (v : V)
  | right (v : V)
  | s | t

namespace Copies
private def tag : Copies V → Nat
  | left _ => 0 | middle _ => 1 | right _ => 2 | s => 3 | t => 4

private def proj (root : V) : Copies V → V
  | left v | middle v | right v => v
  | s | t => root

private def base (G : Graph V) : Graph (Copies V) where
  adj v w := match v,w with
    | left a,left b | middle a,middle b | right a,right b => G.adj a b
    | _,_ => False
  symm := by intro v w; cases v <;> cases w <;> simp_all [Graph.symm] <;> exact G.symm
  loopless := by intro v; cases v <;> simp [G.loopless]

private def first (G : Graph V) (r : V) := addEdge (base G) s (left r) (by intro h; cases h)
private def second (G : Graph V) (r : V) := addEdge (first G r) s (middle r) (by intro h; cases h)
private def third (G : Graph V) (r : V) := addEdge (second G r) t (right r) (by intro h; cases h)
private def joined (G : Graph V) (r : V) := addEdge (third G r) t (middle r) (by intro h; cases h)

private theorem baseStable {G : Graph V} {a b : Copies V} (e : (base G).adj a b) :
    tag a = tag b := by cases a <;> cases b <;> simp_all [tag,base]

private theorem baseEq {a b : Copies V} {r : V} (same : tag a = tag b) (eq : proj r a = proj r b) :
    a = b := by cases a <;> cases b <;> simp_all [tag,proj]

private theorem baseProjects {G : Graph V} (r : V) {a b : Copies V} (e : (base G).adj a b) :
    G.adj (proj r a) (proj r b) := by cases a <;> cases b <;> simp_all [base,proj]

private theorem baseCycle {G : Graph V} (r : V) (cycle : HasDyadicCycle (base G)) : HasDyadicCycle G := by
  obtain ⟨k,hk,f,inj,edges⟩ := cycle
  have aux {n : Nat} (g : Fin (n+1) → Copies V) (h : ∀ i, (base G).adj (g i) (g (cycleNext i))) :
      ∀ i, tag (g i) = tag (g 0) := by
    apply labelOnWalk
    intro i
    have e : cycleNext i.castSucc = i.succ := Fin.ext (Nat.mod_eq_of_lt (show i.val+1<n+1 by omega))
    exact baseStable (e ▸ h i.castSucc)
  have pos : 0 < 2^k := Nat.two_pow_pos _
  obtain ⟨n,hn⟩ : ∃ n, 2^k = n+1 := ⟨2^k-1,by omega⟩
  refine ⟨k,hk,fun i => proj r (f i),?_,fun i => baseProjects r (edges i)⟩
  intro i j eq
  apply inj
  apply baseEq (r := r) ?_ eq
  revert f inj edges i j eq
  rw [hn]
  intro f _ e i j _
  exact (aux f e i).trans (aux f e j).symm

private theorem stableAdded {G : Graph V} {x y : V} {ne : x ≠ y}
    {T : Type v} (c : V → T) (st : ∀ v w, G.adj v w → c v = c w)
    (eq : c x = c y) : ∀ v w, (addEdge G x y ne).adj v w → c v = c w := by
  intro v w h
  rcases h with h | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact st _ _ h
  · exact eq
  · exact eq.symm

private theorem joinedCycle {G : Graph V} (r : V) (h : HasDyadicCycle (joined G r)) :
    HasDyadicCycle G := by
  let split (p : Nat → Bool) := fun v : Copies V => p (tag v)
  have stable (p : Nat → Bool) : ∀ a b, (base G).adj a b → split p a = split p b :=
    fun _ _ e => congrArg p (baseStable e)
  have h₃ : HasDyadicCycle (third G r) := removeBridge (split (fun i => i == 2 || i == 4)) (by intro e; contradiction)
    (stableAdded _ (stableAdded _ (stableAdded _ (stable (fun i => i == 2 || i == 4)) rfl) rfl) rfl) h
  have h₂ : HasDyadicCycle (second G r) := removeBridge (split (fun i => i == 2)) (by intro e; contradiction)
    (stableAdded _ (stableAdded _ (stable (fun i => i == 2)) rfl) rfl) h₃
  have h₁ : HasDyadicCycle (first G r) := removeBridge (split (fun i => i == 1)) (by intro e; contradiction)
    (stableAdded _ (stable (fun i => i == 1)) rfl) h₂
  exact baseCycle r (removeBridge (split (fun i => i == 0)) (by intro e; contradiction) (stable (fun i => i == 0)) h₁)

private theorem baseIn {G : Graph V} (r : V) {a b : Copies V}
    (e : (base G).adj a b) : (joined G r).adj a b := Or.inl (Or.inl (Or.inl (Or.inl e)))

private theorem terminalS (G : Graph V) (r : V) (w : Copies V) :
    (joined G r).adj s w ↔ w = left r ∨ w = middle r := by
  cases w <;> simp [joined,third,second,first,addEdge,base]

private theorem terminalT (G : Graph V) (r : V) (w : Copies V) :
    (joined G r).adj t w ↔ w = middle r ∨ w = right r := by
  cases w <;> simp [joined,third,second,first,addEdge,base]

private theorem joinedConnected {G : Graph V} {r : V} (conn : ∀ v, Reach G r v) : Connected (joined G r) := by
  let J := joined G r
  have es : J.adj (middle r) s := J.symm ((terminalS G r _).2 (Or.inr rfl))
  have et : J.adj (middle r) t := J.symm ((terminalT G r _).2 (Or.inl rfl))
  have branch (label : V → Copies V) (maps : ∀ x y, G.adj x y → J.adj (label x) (label y))
      (atRoot : Reach J (middle r) (label r)) (v : V) : Reach J (middle r) (label v) := by
    have path := conn v
    induction path with
    | refl => exact atRoot
    | step path edge ih => exact ih.step (maps _ _ edge)
  refine ⟨middle r,?_⟩
  intro w; cases w with
  | s => exact Reach.refl.step es
  | t => exact Reach.refl.step et
  | left v =>
    exact branch left (fun _ _ e => baseIn r e)
      ((Reach.refl.step es).step ((terminalS G r _).2 (Or.inl rfl))) v
  | middle v => exact branch middle (fun _ _ e => baseIn r e) Reach.refl v
  | right v =>
    exact branch right (fun _ _ e => baseIn r e)
      ((Reach.refl.step et).step ((terminalT G r _).2 (Or.inr rfl))) v

private theorem joinedDegrees {G : Graph V} (r : V) (deg : MinDegreeThree G) :
    ∀ w : Copies V, w ≠ s → w ≠ t → ThreeAt (joined G r) w := by
  intro w ns nt; cases w with
  | s | t => contradiction
  | left v | middle v | right v =>
    obtain ⟨a,b,c,ha,hb,hc,ab,ac,bc⟩ := deg v
    first
    | exact ⟨left a,left b,left c,baseIn r ha,baseIn r hb,baseIn r hc,by simp [ab],by simp [ac],by simp [bc]⟩
    | exact ⟨middle a,middle b,middle c,baseIn r ha,baseIn r hb,baseIn r hc,by simp [ab],by simp [ac],by simp [bc]⟩
    | exact ⟨right a,right b,right c,baseIn r ha,baseIn r hb,baseIn r hc,by simp [ab],by simp [ac],by simp [bc]⟩

private theorem internalEdge {G : Graph V} {r : V} {a b : Copies V}
    (as' : a ≠ s) (at' : a ≠ t) (bs : b ≠ s) (bt : b ≠ t) (e : (joined G r).adj a b) :
    (base G).adj a b := by
  unfold joined third second first addEdge at e
  grind

private theorem touchesRoot {G : Graph V} {r : V} {a b : Copies V} (endpt : a = s ∨ a = t)
    (e : (joined G r).adj a b) : proj r b = r := by
  rcases endpt with rfl | rfl
  · rcases (terminalS G r b).1 e with rfl|rfl <;> rfl
  · rcases (terminalT G r b).1 e with rfl|rfl <;> rfl

/-- All internal vertices of a simple terminal path stay in one copy. The
first and last of these are both its root, so there can be only one. -/
private theorem noLongPath {G : Graph V} (r : V) (len : Nat) (long : 3 ≤ len) :
    ¬ HasSimplePathBetween (joined G r) s t len := by
  obtain ⟨n,rfl⟩ : ∃ n, len = n+3 := ⟨len-3,by omega⟩
  intro ⟨f,ends,inj,steps⟩
  let inside (i : Fin (n+2)) : Fin ((n+3)+1) := ⟨i.val+1,by omega⟩
  let g := fun i => f (inside i)
  have notEnd (i : Fin (n+2)) : g i ≠ s ∧ g i ≠ t := by
    have h₁ : g i ≠ f 0 := fun e => by have h := congrArg Fin.val (inj _ _ e); change i.val+1 = 0 at h; omega
    have h₂ : g i ≠ f (Fin.last (n+3)) := fun e => by
      have h := congrArg Fin.val (inj _ _ e); change i.val+1 = n+3 at h; omega
    grind
  have same := labelOnWalk g tag (fun i => by
    have a := notEnd i.castSucc; have b := notEnd i.succ
    exact baseStable (internalEdge a.1 a.2 b.1 b.2 (steps ⟨i.val+1,by omega⟩))) (Fin.last (n+1))
  have gl : proj r (g 0) = r := touchesRoot (by grind : f 0 = s ∨ f 0 = t) (steps ⟨0,by omega⟩)
  have gr : proj r (g (Fin.last (n+1))) = r :=
    touchesRoot (by grind : f (Fin.last (n+3)) = s ∨ f (Fin.last (n+3)) = t)
      ((joined G r).symm (steps (Fin.last (n+2))))
  have eq := inj _ _ (baseEq same (gr.trans gl.symm))
  have v := congrArg Fin.val eq
  change (n+1)+1 = 0+1 at v
  omega

end Copies

def ConnectedTerminalPrinciple (length : Nat → Nat) : Prop :=
  ∀ {V : Type u} (G : Graph V) (l : List V), (∀ v, v ∈ l) → Connected G →
  ∀ x y, x ≠ y → ¬G.adj x y → ExactlyTwoAt G x → ExactlyTwoAt G y →
    (∀ v, v ≠ x → v ≠ y → ThreeAt G v) →
    HasDyadicCycle G ∨ ∃ k : Nat, 2 ≤ k ∧ HasSimplePathBetween G x y (length k)

private theorem connectedOfTerminal {length : Nat → Nat} (h : TerminalPrinciple.{u} length) :
    ConnectedTerminalPrinciple.{u} length :=
  fun G l all _ x y ne far dx dy others => h G l all x y ne far dx.two dy.two others

private theorem conjectureOfConnected {length : Nat → Nat}
    (long : ∀ k, 2 ≤ k → 3 ≤ length k) (h : ConnectedTerminalPrinciple.{u} length) : Conjecture.{u} := by
  classical
  intro V G nonempty finite deg
  obtain ⟨l,all⟩ := finite
  let root := Classical.choice nonempty
  let K := component G root
  let C := {x // Reach G root x}
  obtain ⟨r,conn⟩ := componentConnected G root
  let selected := l.filter (fun w => decide (Reach G root w))
  let cl : List C := selected.attachWith _ (by intro x hx; exact of_decide_eq_true (List.mem_filter.mp hx).2)
  have selectedAll (v : C) : v ∈ cl := by
    apply (List.mem_attachWith _ _).2
    exact List.mem_filter.mpr ⟨all v.val,decide_eq_true v.property⟩
  let labels : List (Copies C) := Copies.s :: Copies.t ::
    (cl.map Copies.left ++ cl.map Copies.middle ++ cl.map Copies.right)
  have covered : ∀ v, v ∈ labels := by intro v; cases v <;> simp [labels,selectedAll]
  have ns : Copies.s (V := C) ≠ Copies.t := by intro e; cases e
  have result := h (Copies.joined K r) labels covered (Copies.joinedConnected conn)
    Copies.s Copies.t ns (by simp [Copies.terminalS])
    ⟨Copies.left r,Copies.middle r,⟨by simp,Copies.terminalS K r⟩⟩
    ⟨Copies.middle r,Copies.right r,⟨by simp,Copies.terminalT K r⟩⟩
    (Copies.joinedDegrees r (componentDegree root deg))
  rcases result with cycle | ⟨k,hk,path⟩
  · obtain ⟨k,hk,f,inj,steps⟩ := Copies.joinedCycle r cycle
    exact ⟨k,hk,fun i => (f i).val,fun i j e => inj i j (Subtype.ext e),steps⟩
  · exact False.elim (Copies.noLongPath r (length k) (long k hk) path)

/-- Either terminal path length characterizes the unrestricted conjecture even
on connected hosts with exactly the two specified vertices of degree two. -/
theorem connectedTerminalEquivalences :
    (Conjecture.{u} ↔ ConnectedTerminalPrinciple.{u} (fun k => 2^k)) ∧
    (Conjecture.{u} ↔ ConnectedTerminalPrinciple.{u} (fun k => 2^k-1)) := by
  have bound (k : Nat) (h : 2 ≤ k) : 4 ≤ 2^k := Nat.pow_le_pow_right (by decide : 0 < 2) h
  exact ⟨⟨fun eg => connectedOfTerminal (terminalEquivalences.1.mp eg),
    conjectureOfConnected (by intro k hk; have := bound k hk; omega)⟩,
    ⟨fun eg => connectedOfTerminal (terminalEquivalences.2.mp eg),
    conjectureOfConnected (by intro k hk; have := bound k hk; omega)⟩⟩

end Terminals
end Erdos64
