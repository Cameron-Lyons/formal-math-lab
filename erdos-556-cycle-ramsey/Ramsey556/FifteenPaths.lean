import Ramsey556.BetweenCliques
import Ramsey556.VertexSets

namespace Ramsey556.Fifteen

private abbrev Slot := Fin 7 ⊕ Bool

private def fourCycle (a b p q : Fin 7) : List Slot :=
  let x := Sum.inr false
  let y := Sum.inr true
  let U := @Sum.inl (Fin 7) Bool
  let rest := ((List.finRange 7).filter (fun j => j != a && j != b && j != p && j != q)).map U
  (if a = q then [U b,x,U a,y,U p]
   else if b = q then [U a,x,U b,y,U p]
   else [U a,x,U b,U p,y,U q]) ++ rest

private def point (a b p q : Fin 7) (i : Fin 9) := (fourCycle a b p q)[i.val]?.getD (.inr false)

private def allowed (a b p q : Fin 7) : Slot → Slot → Bool
  | .inl i, .inl j => i != j
  | .inl i, .inr false | .inr false, .inl i => i == a || i == b
  | .inl i, .inr true | .inr true, .inl i => i == p || i == q
  | .inr _, .inr _ => false

private def routeOK (a b p q : Fin 7) : Prop :=
  let xs := fourCycle a b p q
  xs.length = 9 ∧ xs.Nodup ∧
    ∀ i : Fin 9, allowed a b p q (point a b p q i) (point a b p q (i+1)) = true

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem routes : ∀ a b p q : Fin 7, a ≠ b → p ≠ q → p ≠ a → p ≠ b →
    routeOK a b p q := by
  unfold routeOK
  decide +kernel

/-- Subdivide two different edges on a Hamiltonian cycle of the seven-clique. -/
private theorem pattern (a b p q : Fin 7) (ab : a ≠ b) (pq : p ≠ q) (pa : p ≠ a) (pb : p ≠ b) :
    (∀ i j, point a b p q i = point a b p q j → i = j) ∧
      ∀ i, allowed a b p q (point a b p q i) (point a b p q (i+1)) = true := by
  obtain ⟨len,nd,edges⟩ := routes a b p q ab pq pa pb
  refine ⟨?_,edges⟩
  intro i j eq
  have get (k : Fin 9) : point a b p q k = (fourCycle a b p q)[k.val]'(by rw [len]; exact k.isLt) := by
    simp [point, List.getElem?_eq_getElem (by rw [len]; exact k.isLt)]
  rw [get,get] at eq
  exact Fin.ext (nd.eq_of_getElem_eq _ _ eq)

/-- If one exterior vertex has green neighbors a and b in a green K₇, another
exterior vertex with two green neighbors must have both of them in {a,b}. -/
theorem clique_seven_pairs {n : Nat} (c : Coloring n) (k : Fin 3)
    (S : Fin 7 → Fin n) (x y : Fin n)
    (inj : ∀ ⦃i j⦄, S i = S j → i = j) (xy : x ≠ y)
    (awayX : ∀ i, S i ≠ x) (awayY : ∀ i, S i ≠ y)
    (clique : ∀ i j, i ≠ j → c.edge (S i) (S j) = k) (free : ¬ HasMonoC9 c)
    {a b p q : Fin 7} (ab : a ≠ b) (pq : p ≠ q)
    (xa : c.edge x (S a) = k) (xb : c.edge x (S b) = k)
    (yp : c.edge y (S p) = k) (yq : c.edge y (S q) = k) : p = a ∨ p = b := by
  apply Classical.byContradiction
  intro h
  have pa : p ≠ a := fun e => h (Or.inl e)
  have pb : p ≠ b := fun e => h (Or.inr e)
  obtain ⟨nd, edges⟩ := pattern a b p q ab pq pa pb
  let label : Slot → Fin n := fun t => match t with
    | .inl i => S i
    | .inr false => x
    | .inr true => y
  have li : Function.Injective label := by
    rintro (i|(_|_)) (j|(_|_)) eq <;> simp only [label] at eq ⊢ <;> grind
  have good (i j : Slot) (edge : allowed a b p q i j = true) : c.edge (label i) (label j) = k := by
    rcases i with i|(_|_) <;> rcases j with j|(_|_) <;>
      simp [label, allowed] at edge ⊢ <;> grind only [= c.symm]
  exact free ⟨k, fun i => label (point a b p q i), fun {_ _} e => nd _ _ (li e),
    fun i => good _ _ (edges i)⟩

def skip {m : Nat} (z : Fin (m+1)) (i : Fin m) : Fin (m+1) :=
  if i.val < z.val then i.castSucc else i.succ

theorem skip_spec {m : Nat} (z : Fin (m+1)) :
    (∀ i j, skip z i = skip z j → i = j) ∧ ∀ i, skip z i ≠ z := by
  unfold skip
  constructor
  · intro i j eq
    split at eq <;> split at eq <;> simp only [Fin.ext_iff, Fin.val_castSucc, Fin.val_succ] at eq <;> omega
  · intro i eq
    split at eq <;> simp only [Fin.ext_iff, Fin.val_castSucc, Fin.val_succ] at eq <;> omega

theorem skip_injective {m} (z : Fin (m+1)) : Function.Injective (skip z) :=
  fun _ _ => (skip_spec z).1 _ _

theorem skip_ne {m} (z : Fin (m+1)) (i : Fin m) : skip z i ≠ z := (skip_spec z).2 i

/-- Four distinct positions on a shore, starting at a prescribed endpoint. -/
private def fourFrom {n} (a : Fin (n+1)) (room : 3 ≤ n) : Fin 4 → Fin (n+1) :=
  Fin.cases a (fun i => skip a (i.castLE room))

private theorem fourFrom_injective {n} (a : Fin (n+1)) (room : 3 ≤ n) :
    Function.Injective (fourFrom a room) := by
  intro i j eq
  cases i using Fin.cases <;> cases j using Fin.cases
  · rfl
  · exact (skip_ne a _ eq.symm).elim
  · exact (skip_ne a _ eq).elim
  · exact congrArg Fin.succ (Fin.ext (congrArg (fun z : Fin n => z.val) (skip_injective a eq)))

/-- In a complete monochromatic bipartite graph with at least four vertices
on each shore, spokes from an exterior vertex to both shores close a C₉. -/
theorem biclique_spokes_of_sizes {n l r : Nat} (c : Coloring n) (k : Fin 3)
    (A : Fin (l+1) → Fin n) (B : Fin (r+1) → Fin n) (x : Fin n)
    (leftRoom : 3 ≤ l) (rightRoom : 3 ≤ r) (ai : Function.Injective A) (bi : Function.Injective B)
    (ab : ∀ i j, A i ≠ B j) (ax : ∀ i, A i ≠ x) (bx : ∀ i, B i ≠ x)
    (cross : ∀ i j, c.edge (A i) (B j) = k) (free : ¬ HasMonoC9 c)
    {a b} (ha : c.edge x (A a) = k) (hb : c.edge x (B b) = k) : False := by
  let left := A ∘ fourFrom a leftRoom
  let right := B ∘ fourFrom b rightRoom
  let route : Vector (Fin n) 8 := #v[left 0, right 1, left 1, right 2, left 2, right 3, left 3, right 0]
  have distinct : route.toList.Nodup := by
    have ll : Function.Injective left := ai.comp (fourFrom_injective a leftRoom)
    have rr : Function.Injective right := bi.comp (fourFrom_injective b rightRoom)
    have apart (i j) : left i ≠ right j := ab _ _
    have back (i j) : right i ≠ left j := (apart _ _).symm
    simp [route, Vector.toList, List.nodup_cons, ll.eq_iff, rr.eq_iff, apart, back]
  apply free (closeC9Through c k (fun i => route[i]) x ?_ ?_ ?_ ha hb)
  · exact fun {_ _} eq => Fin.ext (distinct.eq_of_getElem_eq _ _ eq)
  · have avoid : ∀ y ∈ route.toList, y ≠ x := by
      simp [route, Vector.toList, left, right, ax, bx]
    exact fun i => avoid _ (List.getElem_mem (l:=route.toList) (n:=i.val) i.isLt)
  · intro i hi
    have indices : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by omega
    rcases indices with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      first | exact cross _ _ | exact (c.symm _ _).trans (cross _ _)

/-- In a monochromatic K₇,₇ an exterior vertex cannot see both shores in the same color. -/
theorem biclique_spokes {n : Nat} (c : Coloring n) (k : Fin 3) (A B : Fin 7 → Fin n) (x : Fin n)
    (ai : ∀ ⦃i j⦄, A i = A j → i = j) (bi : ∀ ⦃i j⦄, B i = B j → i = j)
    (ab : ∀ i j, A i ≠ B j) (ax : ∀ i, A i ≠ x) (bx : ∀ i, B i ≠ x)
    (cross : ∀ i j, c.edge (A i) (B j) = k) (free : ¬ HasMonoC9 c)
    {a b : Fin 7} (ha : c.edge x (A a) = k) (hb : c.edge x (B b) = k) : False :=
  biclique_spokes_of_sizes c k A B x (by decide) (by decide) (@ai) (@bi) ab ax bx cross free ha hb

def AtMostOne (p : Fin 7 → Prop) := ∃ a, ∀ z, p z → z = a

theorem single_exception {α : Type} [Inhabited α] {p : α → Prop}
    (unique : ∀ i j, p i → p j → i = j) : ∃ a, ∀ z, p z → z = a := by
  by_cases ex : ∃ a, p a
  · obtain ⟨a,ha⟩ := ex
    exact ⟨a,fun z hz => unique z a hz ha⟩
  · exact ⟨default,fun z hz => (ex ⟨z,hz⟩).elim⟩

theorem one_of_unique {p : Fin 7 → Prop} (h : ∀ i j, p i → p j → i = j) : AtMostOne p :=
  single_exception h

private theorem two_of_many {p : Fin 7 → Prop} (h : ¬ AtMostOne p) :
    ∃ a b, a ≠ b ∧ p a ∧ p b := by
  apply Classical.byContradiction
  intro none
  exact h (one_of_unique (fun a b pa pb => Classical.byContradiction (fun ne => none ⟨a,b,ne,pa,pb⟩)))

/-- Omitting one exterior vertex leaves a common exceptional pair for every
remaining vertex with two or more neighbors of the clique color in B. -/
theorem omit_one {m : Nat} (c : Coloring 33) (k : Fin 3) (free : ¬ HasMonoC9 c)
    (B : Fin 7 → Fin 33) (w : Fin (m+1) → Fin 33)
    (bi : ∀ ⦃i j⦄, B i = B j → i = j) (wi : ∀ ⦃i j⦄, w i = w j → i = j)
    (away : ∀ a i, B a ≠ w i) (clique : ∀ i j, i ≠ j → c.edge (B i) (B j) = k) :
    ∃ (absent : Fin (m+1)) (a b : Fin 7), ∀ j, j ≠ absent →
      AtMostOne (fun z => c.edge (w j) (B z) = k) ∨
      ∀ z, c.edge (w j) (B z) = k → z = a ∨ z = b := by
  let p (j : Fin (m+1)) (z : Fin 7) := c.edge (w j) (B z) = k
  by_cases existsMany : ∃ o, ¬ AtMostOne (p o)
  · obtain ⟨o,many⟩ := existsMany
    obtain ⟨a,b,ab,ha,hb⟩ := two_of_many many
    refine ⟨o,a,b,?_⟩
    intro j ne
    by_cases single : AtMostOne (p j)
    · exact Or.inl single
    refine Or.inr (fun z hz => ?_)
    have partner : ∃ u, z ≠ u ∧ p j u := by
      apply Classical.byContradiction
      intro none
      exact single ⟨z,fun u hu => Classical.byContradiction (fun ne => none ⟨u,Ne.symm ne,hu⟩)⟩
    obtain ⟨u,zu,h⟩ := partner
    exact clique_seven_pairs c k B (w o) (w j) bi (fun e => ne (wi e).symm)
      (fun i => away i o) (fun i => away i j) clique free ab zu ha hb hz h
  · exact ⟨0,0,0,fun j _ => Or.inl (Classical.byContradiction (fun h => existsMany ⟨j,h⟩))⟩

theorem union_three {P Q : Fin 7 → Prop} {a b : Fin 7}
    (p : AtMostOne P ∨ ∀ z, P z → z = a ∨ z = b)
    (q : AtMostOne Q ∨ ∀ z, Q z → z = a ∨ z = b) :
    ∃ u v w : Fin 7, ∀ z, z ≠ u → z ≠ v → z ≠ w → ¬ P z ∧ ¬ Q z := by
  rcases p with ⟨i,pi⟩|pi <;> rcases q with ⟨j,qj⟩|qj
  · exact ⟨i,j,0,by grind⟩
  · exact ⟨i,a,b,by grind⟩
  · exact ⟨j,a,b,by grind⟩
  · exact ⟨a,b,0,by grind⟩

/-- Count a predicate on an embedded set after excluding a short list of exceptions. -/
theorem count_outside {m n : Nat} (p : Fin m → Bool) (core : Fin n → Fin m)
    (ci : Function.Injective core) (bad : List (Fin n)) (rest : ∀ z, z ∉ bad → p (core z) = true) :
    n ≤ ((List.finRange m).filter p).length + bad.length := by
  let all := List.finRange n
  let good := all.filter (fun i => !bad.contains i)
  have lost := List.Nodup.length_le_of_subset ((List.nodup_finRange n).filter bad.contains) (l₂ := bad)
    (fun {_} h => List.contains_iff_mem.mp (List.mem_filter.mp h).2)
  have kept : (good.map core).Nodup := ((List.nodup_finRange n).filter _).map core (fun _ _ ne eq => ne (ci eq))
  have bound := kept.length_le_of_subset (l₂ := (List.finRange m).filter p) (by
    intro x hx
    obtain ⟨i,mem,rfl⟩ := List.mem_map.mp hx
    exact List.mem_filter.mpr ⟨List.mem_finRange _,rest i (by simpa [good,all] using mem)⟩)
  have total : n = ((List.finRange n).filter bad.contains).length + good.length := by
    simpa [all,good,List.countP_eq_length_filter] using List.length_eq_countP_add_countP bad.contains (l:=all)
  simp only [List.length_map] at bound
  omega

theorem four_in_core {m : Nat} (p : Fin m → Bool) (core : Fin 7 → Fin m)
    (ci : ∀ ⦃i j⦄, core i = core j → i = j) {u v w : Fin 7}
    (rest : ∀ z, z ≠ u → z ≠ v → z ≠ w → p (core z) = true) :
    4 ≤ ((List.finRange m).filter p).length := by
  have bound := count_outside p core (@ci) [u,v,w] (by simpa [not_or] using rest)
  simp only [List.length_cons,List.length_nil] at bound
  omega

/-- On seven positions, three exceptions to the first color and no occurrences
of the second leave four common neighbors in the remaining color. -/
theorem four_common_on_seven {m : Nat} (f g : Fin m → Fin 3) (core : Fin 7 → Fin m)
    (ci : Function.Injective core) {green blue : Fin 3}
    (red : ∀ k : Fin 3, k ≠ green → k ≠ blue → k = 0)
    (few : ∃ u v w, ∀ z, z ≠ u → z ≠ v → z ≠ w → f (core z) ≠ green ∧ g (core z) ≠ green)
    (noneBlue : ∀ z, f (core z) ≠ blue ∧ g (core z) ≠ blue) :
    4 ≤ ((List.finRange m).filter (fun a => f a == 0 && g a == 0)).length := by
  obtain ⟨u,v,w,exceptions⟩ := few
  apply four_in_core _ core ci (u:=u) (v:=v) (w:=w)
  intro z zu zv zw
  obtain ⟨fx,gx⟩ := exceptions z zu zv zw
  simp [red _ fx (noneBlue z).1, red _ gx (noneBlue z).2]

theorem exterior {a b : Nat} (sum : a+b ≤ 33) (v : Fin a → Fin 33) :
    ∃ w : Fin b → Fin 33, (∀ ⦃i j⦄, w i = w j → i = j) ∧ ∀ a i, v a ≠ w i :=
  outside_vertices sum v

end Ramsey556.Fifteen
