import Ramsey556.Basic

namespace Ramsey556.SixClique

/-- Two prescribed distinct edges of K₆ can be traversed with insertions.
Anchor positions 0 and 1 attach vertices 6 and 7, and anchors r and s
attach vertex 8. Each row of the table fixes r and varies s. -/
private def routeCodes : Vector Nat 36 := #v[
  0x0,0x0,0x825431760,0x835421760,0x845321760,0x854321760,
  0x0,0x0,0x543281760,0x542381760,0x532481760,0x432581760,
  0x825431760,0x543281760,0x0,0x543821760,0x534821760,0x435821760,
  0x835421760,0x542381760,0x543821760,0x0,0x548321760,0x458321760,
  0x845321760,0x532481760,0x534821760,0x548321760,0x0,0x584321760,
  0x854321760,0x432581760,0x435821760,0x458321760,0x584321760,0x0]

private def route (r s : Fin 6) (i : Fin 9) : Fin 9 :=
  ⟨((routeCodes[6*r.val+s.val]'(by omega) >>> (4*i.val)) % 16) % 9, by omega⟩

private def undirected {α : Type} (a b x y : α) := (a=x ∧ b=y) ∨ (a=y ∧ b=x)
private instance [DecidableEq α] (a b x y : α) : Decidable (undirected a b x y) :=
  inferInstanceAs (Decidable ((_ ∧ _) ∨ (_ ∧ _)))

private def permitted (r s : Fin 6) (a b : Fin 9) : Prop :=
  (a.val < 6 ∧ b.val < 6 ∧ a≠b) ∨ undirected a b 0 6 ∨ undirected a b 6 7 ∨
  undirected a b 7 1 ∨ undirected a.val b.val 8 r.val ∨ undirected a.val b.val 8 s.val

private instance (r s : Fin 6) (a b : Fin 9) : Decidable (permitted r s a b) :=
  inferInstanceAs (Decidable ((_ ∧ _ ∧ _) ∨ _ ∨ _ ∨ _ ∨ _ ∨ _))

set_option synthInstance.maxSize 4096 in
private theorem route_spec : ∀ r s : Fin 6, r≠s → ¬undirected r s 0 1 →
    (∀ i j, route r s i=route r s j → i=j) ∧ ∀ i, permitted r s (route r s i) (route r s (i+1)) := by
  decide +kernel

private def swap (a b i : Fin 6) := if i=a then b else if i=b then a else i
private def perm (a b i : Fin 6) := swap 0 a (swap 1 (swap 0 a b) i)
private def back (a b i : Fin 6) := swap 1 (swap 0 a b) (swap 0 a i)
private theorem perm_spec : ∀ a b, a≠b → perm a b 0 = a ∧ perm a b 1 = b ∧
    (∀ i, perm a b (back a b i)=i) ∧ ∀ i j, perm a b i=perm a b j → i=j := by decide +kernel

/-- A clique of order six absorbs an adjacent pair of exterior vertices
through one anchor edge and a third exterior vertex through a different
anchor edge. -/
theorem two_insertions {n : Nat} (c : Coloring n) (k : Fin 3) (A : Fin 6 → Fin n)
    (X : Fin 3 → Fin n) (ai : ∀ ⦃i j⦄, A i=A j → i=j) (xi : ∀ ⦃i j⦄, X i=X j → i=j)
    (apart : ∀ i j, A i≠X j) (clique : ∀ i j, i≠j → c.edge (A i) (A j)=k)
    {p q u v : Fin 6} (pq : p≠q) (uv : u≠v)
    (different : ¬((u=p ∧ v=q) ∨ (u=q ∧ v=p)))
    (link : c.edge (X 0) (X 1)=k) (p0 : c.edge (X 0) (A p)=k)
    (q1 : c.edge (X 1) (A q)=k) (u2 : c.edge (X 2) (A u)=k)
    (v2 : c.edge (X 2) (A v)=k) : HasMonoC9 c := by
  obtain ⟨first,second,inv,permInj⟩ := perm_spec p q pq
  let r := back p q u
  let s := back p q v
  have rs : r≠s := by intro e; exact uv ((inv u).symm.trans ((congrArg (perm p q) e).trans (inv v)))
  have distinct : ¬undirected r s 0 1 := by
    intro h; apply different
    rcases h with ⟨a,b⟩|⟨a,b⟩
    · exact Or.inl ⟨(inv u).symm.trans ((congrArg (perm p q) a).trans first),(inv v).symm.trans ((congrArg (perm p q) b).trans second)⟩
    · exact Or.inr ⟨(inv u).symm.trans ((congrArg (perm p q) a).trans second),(inv v).symm.trans ((congrArg (perm p q) b).trans first)⟩
  obtain ⟨pi,pe⟩ := route_spec r s rs distinct
  let f (i : Fin 9) := if h : i.val<6 then A (perm p q ⟨i.val,h⟩) else X ⟨i.val-6,by omega⟩
  have fi : ∀ ⦃i j⦄, f i=f j → i=j := by
    intro i j e
    simp only [f] at e
    split at e <;> split at e
    · exact Fin.ext (congrArg (fun x : Fin 6 => x.val) (permInj _ _ (ai e)))
    · exact (apart _ _ e).elim
    · exact (apart _ _ e.symm).elim
    · have h := congrArg Fin.val (xi e); apply Fin.ext; dsimp at h; omega
  have symmetry (i j : Fin 9) (h : c.edge (f i) (f j)=k) {a b : Fin 9}
      (eq : undirected a b i j) : c.edge (f a) (f b)=k := by
    rcases eq with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact h
    · exact (c.symm _ _).trans h
  have atSlot (z : Fin 6) : f (⟨z.val,by omega⟩ : Fin 9) = A (perm p q z) := by simp [f,z.isLt]
  have uval (i : Fin 6) {a b : Fin 9} (h : undirected a.val b.val 8 i.val) :
      undirected a b 8 ⟨i.val,by omega⟩ := by
    rcases h with ⟨x,y⟩|⟨x,y⟩
    · exact Or.inl ⟨Fin.ext x,Fin.ext y⟩
    · exact Or.inr ⟨Fin.ext x,Fin.ext y⟩
  refine ⟨k,fun i => f (route r s i),fun {_ _} e => pi _ _ (fi e),?_⟩
  intro i
  let a := route r s i
  let b := route r s (i+1)
  have good : permitted r s a b := pe i
  rcases good with ⟨ha,hb,ne⟩|h|h|h|h|h
  · change c.edge (f a) (f b)=k
    simp only [f,ha,hb,↓reduceDIte]
    apply clique
    intro e
    exact ne (Fin.ext (congrArg (fun z : Fin 6 => z.val) (permInj _ _ e)))
  · apply symmetry 0 6 _ h
    change c.edge (A (perm p q 0)) (X 0)=k
    rw [first]; exact (c.symm _ _).trans p0
  · exact symmetry 6 7 link h
  · apply symmetry 7 1 _ h
    change c.edge (X 1) (A (perm p q 1))=k
    rwa [second]
  · apply symmetry 8 _ _ (uval r h)
    rw [atSlot, inv]; exact u2
  · apply symmetry 8 _ _ (uval s h)
    rw [atSlot, inv]; exact v2

/-- If two of three exterior vertices are joined in the clique color, then
any choice of two clique neighbors at each of them must be the same pair. -/
theorem linked_pairs {n : Nat} (c : Coloring n) (k : Fin 3) (A : Fin 6 → Fin n)
    (X : Fin 3 → Fin n) (ai : ∀ ⦃i j⦄, A i=A j → i=j) (xi : ∀ ⦃i j⦄, X i=X j → i=j)
    (apart : ∀ i j, A i≠X j) (clique : ∀ i j, i≠j → c.edge (A i) (A j)=k)
    (free : ¬HasMonoC9 c) (link : c.edge (X 0) (X 1)=k)
    {p q r s u v : Fin 6} (pq : p≠q) (rs : r≠s) (uv : u≠v)
    (p0 : c.edge (X 0) (A p)=k) (q0 : c.edge (X 0) (A q)=k)
    (r1 : c.edge (X 1) (A r)=k) (s1 : c.edge (X 1) (A s)=k)
    (u2 : c.edge (X 2) (A u)=k) (v2 : c.edge (X 2) (A v)=k) :
    ((p=u ∧ q=v) ∨ (p=v ∧ q=u)) ∧ ((r=u ∧ s=v) ∨ (r=v ∧ s=u)) := by
  have must (a b : Fin 6) (h : c.edge (X 0) (A a)=k) (h' : c.edge (X 1) (A b)=k) :
      a=b ∨ ((u=a ∧ v=b) ∨ (u=b ∧ v=a)) := by
    by_cases e : a=b
    · exact Or.inl e
    · exact Or.inr (Classical.byContradiction (fun differ =>
        free (two_insertions c k A X (@ai) (@xi) apart clique e uv differ link h h' u2 v2)))
  have pr := must p r p0 r1
  have ps := must p s p0 s1
  have qr := must q r q0 r1
  have qs := must q s q0 s1
  grind

namespace Forest

private def codes : Vector Nat 36 := #v[
  0x0,0x0,0x827354160,0x837254160,0x845372160,0x854372160,
  0x0,0x0,0x543728160,0x542738160,0x537248160,0x437258160,
  0x827354160,0x543728160,0x0,0x0,0x548273160,0x458273160,
  0x837254160,0x542738160,0x0,0x0,0x548372160,0x458372160,
  0x845372160,0x537248160,0x548273160,0x548372160,0x0,0x584372160,
  0x854372160,0x437258160,0x458273160,0x458372160,0x584372160,0x0]

private def route (r s : Fin 6) (i : Fin 9) : Fin 9 :=
  ⟨((codes[6*r.val+s.val]'(by omega) >>> (4*i.val)) % 16) % 9, by omega⟩

private def permitted (r s : Fin 6) (a b : Fin 9) : Prop :=
  (a.val < 6 ∧ b.val < 6 ∧ a≠b) ∨ undirected a b 0 6 ∨ undirected a b 6 1 ∨
  undirected a b 2 7 ∨ undirected a b 7 3 ∨ undirected a.val b.val 8 r.val ∨ undirected a.val b.val 8 s.val

private instance (r s : Fin 6) (a b : Fin 9) : Decidable (permitted r s a b) :=
  inferInstanceAs (Decidable ((_ ∧ _ ∧ _) ∨ _ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _))

set_option synthInstance.maxSize 4096 in
private theorem spec : ∀ r s : Fin 6, r≠s → ¬undirected r s 0 1 → ¬undirected r s 2 3 →
    (∀ i j, route r s i=route r s j → i=j) ∧ ∀ i, permitted r s (route r s i) (route r s (i+1)) := by
  decide +kernel

private def order (a b c d i : Fin 6) :=
  let u := back a b c
  let v := swap 2 u (back a b d)
  perm a b (swap 2 u (swap 3 v i))

private def inverse (a b c d i : Fin 6) :=
  let u := back a b c
  let v := swap 2 u (back a b d)
  swap 3 v (swap 2 u (back a b i))

set_option maxHeartbeats 0 in
private theorem order_spec : ∀ a b c d : Fin 6, [a,b,c,d].Nodup →
    order a b c d 0=a ∧ order a b c d 1=b ∧ order a b c d 2=c ∧ order a b c d 3=d ∧
    (∀ i, order a b c d (inverse a b c d i)=i) ∧
    ∀ i j, order a b c d i=order a b c d j → i=j := by decide +kernel

/-- If two exterior vertices use disjoint pairs of a six-clique, a third
exterior vertex can only use one of those very same pairs. Any different
pair gives three distinct edges of a linear forest, which can be subdivided
by the exterior vertices on a Hamilton cycle through the clique. -/
theorem disjoint_pairs {n : Nat} (c : Coloring n) (k : Fin 3) (A : Fin 6 → Fin n)
    (X : Fin 3 → Fin n) (ai : ∀ ⦃i j⦄, A i=A j → i=j) (xi : ∀ ⦃i j⦄, X i=X j → i=j)
    (apart : ∀ i j, A i≠X j) (clique : ∀ i j, i≠j → c.edge (A i) (A j)=k)
    (free : ¬HasMonoC9 c) {p q l m u v : Fin 6} (nd : [p,q,l,m].Nodup) (uv : u≠v)
    (p0 : c.edge (X 0) (A p)=k) (q0 : c.edge (X 0) (A q)=k)
    (l1 : c.edge (X 1) (A l)=k) (m1 : c.edge (X 1) (A m)=k)
    (u2 : c.edge (X 2) (A u)=k) (v2 : c.edge (X 2) (A v)=k) :
    ((u=p ∧ v=q) ∨ (u=q ∧ v=p)) ∨ ((u=l ∧ v=m) ∨ (u=m ∧ v=l)) := by
  apply Classical.byContradiction; intro different
  let h := order p q l m
  obtain ⟨first,second,third,fourth,inv,permInj⟩ := order_spec _ _ _ _ nd
  let r := inverse p q l m u
  let s := inverse p q l m v
  have rs : r≠s := by intro e; exact uv ((inv u).symm.trans ((congrArg h e).trans (inv v)))
  have pull (i j : Fin 6) (e : undirected r s i j) : undirected u v (h i) (h j) := by
    rcases e with ⟨a,b⟩|⟨a,b⟩
    · exact Or.inl ⟨(inv u).symm.trans (congrArg h a),(inv v).symm.trans (congrArg h b)⟩
    · exact Or.inr ⟨(inv u).symm.trans (congrArg h a),(inv v).symm.trans (congrArg h b)⟩
  have d1 : ¬undirected r s 0 1 := by
    intro e; apply different; left
    simpa only [h,first,second,undirected] using pull _ _ e
  have d2 : ¬undirected r s 2 3 := by
    intro e; apply different; right
    simpa only [h,third,fourth,undirected] using pull _ _ e
  obtain ⟨pi,pe⟩ := spec r s rs d1 d2
  let f (i : Fin 9) := if h' : i.val<6 then A (h ⟨i.val,h'⟩) else X ⟨i.val-6,by omega⟩
  have fi : ∀ ⦃i j⦄, f i=f j → i=j := by
    intro i j e
    simp only [f] at e
    split at e <;> split at e
    · exact Fin.ext (congrArg (fun x : Fin 6 => x.val) (permInj _ _ (ai e)))
    · exact (apart _ _ e).elim
    · exact (apart _ _ e.symm).elim
    · have z := congrArg Fin.val (xi e); apply Fin.ext; dsimp at z; omega
  have symmetry (i j : Fin 9) (e : c.edge (f i) (f j)=k) {a b : Fin 9}
      (eq : undirected a b i j) : c.edge (f a) (f b)=k := by
    rcases eq with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact e
    · exact (c.symm _ _).trans e
  have atSlot (z : Fin 6) : f (⟨z.val,by omega⟩ : Fin 9) = A (order p q l m z) := by simp [f,h,z.isLt]
  have uval (i : Fin 6) {a b : Fin 9} (e : undirected a.val b.val 8 i.val) :
      undirected a b 8 ⟨i.val,by omega⟩ := by
    rcases e with ⟨x,y⟩|⟨x,y⟩
    · exact Or.inl ⟨Fin.ext x,Fin.ext y⟩
    · exact Or.inr ⟨Fin.ext x,Fin.ext y⟩
  apply free
  refine ⟨k,fun i => f (route r s i),fun {_ _} e => pi _ _ (fi e),?_⟩
  intro i
  let a := route r s i
  let b := route r s (i+1)
  have good : permitted r s a b := pe i
  rcases good with ⟨ha,hb,ne⟩|e|e|e|e|e|e
  · change c.edge (f a) (f b)=k
    simp only [f,ha,hb,↓reduceDIte]
    apply clique
    intro z
    exact ne (Fin.ext (congrArg (fun j : Fin 6 => j.val) (permInj _ _ z)))
  · apply symmetry 0 6 _ e
    change c.edge (A (order p q l m 0)) (X 0)=k
    rw [first]; exact (c.symm _ _).trans p0
  · apply symmetry 6 1 _ e
    change c.edge (X 0) (A (order p q l m 1))=k
    rwa [second]
  · apply symmetry 2 7 _ e
    change c.edge (A (order p q l m 2)) (X 1)=k
    rw [third]; exact (c.symm _ _).trans l1
  · apply symmetry 7 3 _ e
    change c.edge (X 1) (A (order p q l m 3))=k
    rwa [fourth]
  · apply symmetry 8 _ _ (uval r e)
    rw [atSlot, inv]; exact u2
  · apply symmetry 8 _ _ (uval s e)
    rw [atSlot, inv]; exact v2

end Forest

end Ramsey556.SixClique
