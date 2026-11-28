import Ramsey556.Extension

namespace Ramsey556.StarBiclique

/-- The three interior vertices on the left avoid the defective row. -/
private def leftSlot (a bad : Fin 7) (i : Fin 4) : Fin 7 :=
  let step : Fin 7 := ⟨i.val,by omega⟩
  if bad=a+1 ∨ bad=a+2 ∨ bad=a+3 then a-step else a+step

private theorem leftSpec : ∀ a bad : Fin 7, leftSlot a bad 0=a ∧
    (∀ i j, leftSlot a bad i=leftSlot a bad j → i=j) ∧
    ∀ i, i≠0 → leftSlot a bad i≠bad := by decide +kernel

private def swap (x y j : Fin 7) := if j=x then y else if j=y then x else j

private def rightSlot (q b : Fin 7) (i : Fin 4) : Fin 7 :=
  swap 0 q (swap 3 (swap 0 q b) ⟨i.val, by omega⟩)

private theorem rightSpec : ∀ q b : Fin 7, q≠b → rightSlot q b 0=q ∧ rightSlot q b 3=b ∧
    ∀ i j, rightSlot q b i=rightSlot q b j → i=j := by decide +kernel

private abbrev Slot := Fin 4 ⊕ Fin 4

private def sequence : Vector Slot 8 :=
  #v[.inl 0,.inr 0,.inl 1,.inr 1,.inl 2,.inr 2,.inl 3,.inr 3]

private theorem sequenceInj : ∀ i j : Fin 8, sequence[i]=sequence[j] → i=j := by decide

/-- A prescribed first edge leads into the six complete rows. -/
theorem star_path_from {n : Nat} (c : Coloring n) (k : Fin 3) (A B : Fin 7 → Fin n)
    (ai : ∀ ⦃i j⦄, A i = A j → i = j) (bi : ∀ ⦃i j⦄, B i = B j → i = j)
    (disj : ∀ i j, A i ≠ B j) (bad q : Fin 7) (cross : ∀ i j, i≠bad → c.edge (A i) (B j)=k)
    (a b : Fin 7) (qb : q≠b) (firstEdge : c.edge (A a) (B q)=k) :
    ∃ p : Fin 8 → Fin n, (∀ ⦃i j⦄, p i=p j → i=j) ∧ p 0=A a ∧ p 7=B b ∧
      (∀ i : Fin 8, ∀ h : i.val+1<8, c.edge (p i) (p ⟨i.val+1,h⟩)=k) ∧
      ∀ i, (∃ j, p i=A j) ∨ (∃ j, p i=B j) := by
  let vertex : Slot → Fin n := Sum.elim (fun i => A (leftSlot a bad i)) (fun i => B (rightSlot q b i))
  obtain ⟨start,li,avoid⟩ := leftSpec a bad
  obtain ⟨first,last,ri⟩ := rightSpec q b qb
  have vi : ∀ i j, vertex i=vertex j → i=j := by
    rintro (i|i) (j|j) e
    · exact congrArg Sum.inl (li _ _ (ai e))
    · exact (disj _ _ e).elim
    · exact (disj _ _ e.symm).elim
    · exact congrArg Sum.inr (ri _ _ (bi e))
  let p (i : Fin 8) := vertex sequence[i]
  refine ⟨p,fun {_ _} e => sequenceInj _ _ (vi _ _ e),congrArg A start,congrArg B last,?_,?_⟩
  · have beginEdge : c.edge (A (leftSlot a bad 0)) (B (rightSlot q b 0))=k :=
      by rwa [start,first]
    have inside (i j : Fin 4) (ne : i≠0) : c.edge (A (leftSlot a bad i)) (B (rightSlot q b j))=k :=
      cross _ _ (avoid _ ne)
    intro i hi
    have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 := by omega
    rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact beginEdge
    all_goals first | exact inside _ _ (by decide) | exact (c.symm _ _).trans (inside _ _ (by decide))
  · intro i
    cases h : sequence[i] with
    | inl j => exact Or.inl ⟨_,congrArg vertex h⟩
    | inr j => exact Or.inr ⟨_,congrArg vertex h⟩

/-- A K₇,₇ with up to five missing edges in one row contains a seven-edge
simple path between any prescribed opposite endpoints. Every vertex of
the path lies on one of its two shores. -/
theorem star_path {n : Nat} (c : Coloring n) (k : Fin 3) (A B : Fin 7 → Fin n)
    (ai : ∀ ⦃i j⦄, A i = A j → i = j) (bi : ∀ ⦃i j⦄, B i = B j → i = j)
    (disj : ∀ i j, A i ≠ B j) (bad u v : Fin 7) (uv : u≠v)
    (cross : ∀ i j, i≠bad ∨ j=u ∨ j=v → c.edge (A i) (B j)=k) (a b : Fin 7) :
    ∃ p : Fin 8 → Fin n, (∀ ⦃i j⦄, p i=p j → i=j) ∧ p 0=A a ∧ p 7=B b ∧
      (∀ i : Fin 8, ∀ h : i.val+1<8, c.edge (p i) (p ⟨i.val+1,h⟩)=k) ∧
      ∀ i, (∃ j, p i=A j) ∨ (∃ j, p i=B j) := by
  let q := if u=b then v else u
  have qb : q≠b := by by_cases h : u=b <;> simp [q,h] <;> omega
  have good : q=u ∨ q=v := by by_cases h : u=b <;> simp [q,h]
  exact star_path_from c k A B (@ai) (@bi) disj bad q
    (fun i j h => cross i j (Or.inl h)) a b qb (cross a q (Or.inr good))

/-- An exterior vertex cannot see both shores in color k. -/
theorem star_spokes {n : Nat} (c : Coloring n) (k : Fin 3) (A B : Fin 7 → Fin n) (x : Fin n)
    (ai : ∀ ⦃i j⦄, A i = A j → i = j) (bi : ∀ ⦃i j⦄, B i = B j → i = j)
    (disj : ∀ i j, A i ≠ B j) (ax : ∀ i, A i ≠ x) (bx : ∀ i, B i ≠ x)
    (bad u v : Fin 7) (uv : u≠v)
    (cross : ∀ i j, i≠bad ∨ j=u ∨ j=v → c.edge (A i) (B j)=k) (free : ¬HasMonoC9 c)
    {a b : Fin 7} (ea : c.edge x (A a)=k) (eb : c.edge x (B b)=k) : False := by
  obtain ⟨p,pi,start,last,edges,shores⟩ := star_path c k A B (@ai) (@bi) disj bad u v uv cross a b
  apply free (closeC9Through c k p x pi _ edges (start ▸ ea) (last ▸ eb))
  intro i eq
  rcases shores i with ⟨j,h⟩|⟨j,h⟩
  · exact ax _ (h.symm.trans eq)
  · exact bx _ (h.symm.trans eq)

/-- An exterior vertex cannot see both shores in color k. -/
theorem star_spokes_from {n : Nat} (c : Coloring n) (k : Fin 3) (A B : Fin 7 → Fin n) (x : Fin n)
    (ai : ∀ ⦃i j⦄, A i = A j → i = j) (bi : ∀ ⦃i j⦄, B i = B j → i = j)
    (disj : ∀ i j, A i ≠ B j) (ax : ∀ i, A i ≠ x) (bx : ∀ i, B i ≠ x)
    (bad q : Fin 7) (cross : ∀ i j, i≠bad → c.edge (A i) (B j)=k)
    {a b : Fin 7} (qb : q≠b) (first : c.edge (A a) (B q)=k) (free : ¬HasMonoC9 c)
    (ea : c.edge x (A a)=k) (eb : c.edge x (B b)=k) : False := by
  obtain ⟨p,pi,start,last,edges,shores⟩ := star_path_from c k A B (@ai) (@bi) disj bad q cross a b qb first
  apply free (closeC9Through c k p x pi _ edges (start ▸ ea) (last ▸ eb))
  intro i eq
  rcases shores i with ⟨j,h⟩|⟨j,h⟩
  · exact ax _ (h.symm.trans eq)
  · exact bx _ (h.symm.trans eq)

end Ramsey556.StarBiclique
