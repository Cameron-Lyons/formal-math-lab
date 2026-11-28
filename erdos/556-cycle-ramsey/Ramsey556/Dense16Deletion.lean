import Ramsey556.EdgeBound
import Ramsey556.Cert16.Basic

namespace Ramsey556

def colorAdjacent {n : Nat} (c : Coloring n) (k : Fin 3) (i j : Fin n) : Bool :=
  decide (i ≠ j ∧ c.edge i j = k)

def colorDegree {n : Nat} (c : Coloring n) (k : Fin 3) (u : Fin n) : Nat :=
  (List.finRange n).countP (colorAdjacent c k u)

namespace DeletionCount

/-- Count each unordered edge once in a list of distinct vertices. -/
def pairs {α : Type} (r : α → α → Bool) : List α → Nat
  | [] => 0
  | x :: xs => xs.countP (r x) + pairs r xs

theorem perm {α : Type} (r : α → α → Bool) (sym : ∀ a b, r a b = r b a)
    {xs ys : List α} (p : xs.Perm ys) : pairs r xs = pairs r ys := by
  induction p with
  | nil => rfl
  | cons a h ih => simp only [pairs, h.countP_eq, ih]
  | swap a b l => simp [pairs, List.countP_cons, sym a b]; omega
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem map {α β : Type} (r : β → β → Bool) (f : α → β) (xs : List α) :
    pairs r (xs.map f) = pairs (fun i j => r (f i) (f j)) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [pairs, ih, List.countP_map, Function.comp_def]

theorem congr {α : Type} {r s : α → α → Bool} (xs : List α)
    (h : ∀ x ∈ xs, ∀ y ∈ xs, r x y = s x y) : pairs r xs = pairs s xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [pairs]
    rw [ih (fun a ha b hb => h _ (by simp [ha]) _ (by simp [hb]))]
    congr 1
    apply List.countP_congr
    intro y hy
    rw [h x (by simp) y (by simp [hy])]

theorem degree_sum {α : Type} (r : α → α → Bool) (sym : ∀ a b, r a b = r b a)
    (irr : ∀ a, r a a = false) (xs : List α) :
    (xs.map (fun u => xs.countP (r u))).sum = 2 * pairs r xs := by
  have step (x : α) (us vs : List α) :
      (vs.map (fun u => (x::us).countP (r u))).sum =
      vs.countP (r x) + (vs.map (fun u => us.countP (r u))).sum := by
    induction vs with
    | nil => simp
    | cons y ys ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih, List.countP_cons, List.countP_cons, sym y x]
      split <;> omega
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, pairs]
    rw [step, ih, List.countP_cons]
    simp only [irr, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    omega

theorem sum_lower {α : Type} (f : α → Nat) (xs : List α) (m : Nat)
    (h : ∀ x ∈ xs, m ≤ f x) : xs.length * m ≤ (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hl := ih (fun y hy => h y (by simp [hy]))
    have hx := h x (by simp)
    simp [Nat.succ_mul]
    omega

theorem adjacent_sym {n} (c : Coloring n) (k : Fin 3) (i j : Fin n) :
    colorAdjacent c k i j = colorAdjacent c k j i := by
  simp only [colorAdjacent, c.symm i j, (ne_comm (a := i) (b := j))]

theorem adjacent_induce {m n} (c : Coloring n) (k : Fin 3) (v : Fin m → Fin n)
    (inj : ∀ ⦃i j⦄, v i = v j → i = j) (a b : Fin m) :
    colorAdjacent (c.induce v) k a b = colorAdjacent c k (v a) (v b) := by
  have eq : (v a = v b) ↔ a = b := ⟨fun e => inj e, congrArg v⟩
  dsimp only [colorAdjacent, Coloring.induce]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, ne_eq, eq]

end DeletionCount

def colorEdgeCount {n} (c : Coloring n) (k : Fin 3) : Nat :=
  DeletionCount.pairs (colorAdjacent c k) (List.finRange n)

theorem colorEdgeCount_induce {n m} (c : Coloring n) (k : Fin 3) (v : Fin m → Fin n)
    (inj : ∀ ⦃i j⦄, v i = v j → i = j) : colorEdgeCount (c.induce v) k =
      DeletionCount.pairs (colorAdjacent c k) ((List.finRange m).map v) := by
  rw [colorEdgeCount, DeletionCount.map]
  exact DeletionCount.congr _ (fun a _ b _ => DeletionCount.adjacent_induce c k v inj a b)

theorem colorEdgeCount_relabel {n} (c : Coloring n) (k : Fin 3) (v : Fin n → Fin n)
    (inj : ∀ ⦃i j⦄, v i = v j → i = j) : colorEdgeCount (c.induce v) k = colorEdgeCount c k := by
  rw [colorEdgeCount_induce c k v inj]
  apply DeletionCount.perm _ (DeletionCount.adjacent_sym c k)
  exact Cert16.list_permutation v inj

/-- Counting by increasing larger endpoint gives the same total as counting
unordered pairs in any enumeration of the finite vertex set. -/
theorem cert16_count_eq {n g : Nat} (c : Coloring n) (k : Fin 3)
    (h : ∀ i j : Fin n, Cert16.edge g i.val j.val = decide (i ≠ j ∧ c.edge i j = k)) :
    Cert16.edgeCount n g = colorEdgeCount c k := by
  let r := Cert16.edge g
  have sym (a b : Nat) : r a b = r b a := by simp only [r, Cert16.edge, (bne_comm (a := a) (b := b)), Nat.max_comm a b, Nat.min_comm a b]
  have range (t : Nat) : Cert16.edgeCount t g = DeletionCount.pairs r (List.range t) := by
    induction t with
    | zero => rfl
    | succ t ih =>
      have p : ((List.range t) ++ [t]).Perm (t :: List.range t) := List.perm_append_singleton _ _
      rw [List.range_succ, DeletionCount.perm _ sym p]
      unfold Cert16.edgeCount
      simp only [List.range_succ, List.map_append, List.sum_append, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, Nat.add_zero, DeletionCount.pairs]
      change Cert16.edgeCount t g + _ = _ + _
      rw [ih, List.countP_eq_length_filter, Nat.add_comm]
  have finrange : (List.finRange n).map Fin.val = List.range n := by
    apply List.ext_getElem <;> simp
  rw [range, ← finrange, DeletionCount.map]
  apply DeletionCount.congr
  exact fun i _ j _ => h i j

def pairList {α : Type} : List α → List (α × α)
  | [] => []
  | x::xs => xs.map (fun y => (x,y)) ++ pairList xs

theorem count_pairList {α : Type} (r : α → α → Bool) (xs : List α) :
    DeletionCount.pairs r xs = (pairList xs).countP (fun (x,y) => r x y) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [DeletionCount.pairs, pairList, List.countP_map, Function.comp_def, ih]

theorem colorEdgeCount16_eq (c : Coloring 16) (k : Fin 3) : colorEdgeCount c k = edgeCount16 c k := by
  let xs := pairList (List.finRange 16)
  have distinct : ∀ e ∈ xs, e.1 ≠ e.2 := by decide +revert
  rw [colorEdgeCount, count_pairList]
  change xs.countP _ = _
  rw [show edgeCount16 c k = xs.countP (fun e => c.edge e.1 e.2 == k) by
    rw [List.countP_eq_length_filter]
    rfl]
  apply List.countP_congr
  intro e h
  obtain ⟨a,b⟩ := e
  simp [colorAdjacent, distinct (a,b) h]

/-- Deleting a minimum-degree vertex preserves enough edges for the next
catalog level. The embedding lists every remaining vertex exactly once. -/
theorem delete_min_degree {n : Nat} (c : Coloring (n+1)) (k : Fin 3) :
    ∃ (z : Fin (n+1)) (v : Fin n → Fin (n+1)),
      (∀ ⦃i j⦄, v i = v j → i = j) ∧ (∀ i, v i ≠ z) ∧
      (∀ u, u ≠ z → ∃ i, v i = u) ∧
      colorEdgeCount c k = colorEdgeCount (c.induce v) k + colorDegree c k z ∧
      (n+1) * colorDegree c k z ≤ 2 * colorEdgeCount c k ∧
      ∀ u, colorDegree c k z ≤ colorDegree c k u := by
  let xs := List.finRange (n+1)
  have nonempty : xs ≠ [] := by intro e; have := congrArg List.length e; simp [xs] at this
  let z := xs.minOn (colorDegree c k) nonempty
  have minDeg (u : Fin (n+1)) : colorDegree c k z ≤ colorDegree c k u :=
    List.apply_minOn_le_of_mem (List.mem_finRange _)
  let ys := xs.erase z
  have len : ys.length = n := by simp [ys, xs, List.length_erase_of_mem (List.mem_finRange z)]
  let v (i : Fin n) := ys[i.val]'(by rw [len]; exact i.isLt)
  have inj : ∀ ⦃i j⦄, v i = v j → i = j := fun {_ _} e =>
    Fin.ext (((List.nodup_finRange _).erase z).eq_of_getElem_eq _ _ e)
  have enum : (List.finRange n).map v = ys := by
    apply List.ext_getElem
    · simp [len]
    · intro i h h'
      simp [v]
  have away (i : Fin n) : v i ≠ z :=
    ((List.nodup_finRange _).mem_erase_iff.mp (List.getElem_mem (l := ys) (n := i.val) (by rw [len]; exact i.isLt))).1
  have p := List.perm_cons_erase (List.mem_finRange z)
  have same := DeletionCount.perm _ (DeletionCount.adjacent_sym c k) p
  have deg : colorDegree c k z = ys.countP (colorAdjacent c k z) := by
    simpa [colorDegree, ys, xs, List.countP_cons, colorAdjacent] using p.countP_eq (colorAdjacent c k z)
  refine ⟨z, v, @inj, away, ?_, ?_, ?_, minDeg⟩
  · intro u h
    have mem : u ∈ ys := (List.nodup_finRange _).mem_erase_iff.mpr ⟨h, List.mem_finRange _⟩
    rw [← enum] at mem
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp mem
    exact ⟨i, rfl⟩
  · rw [colorEdgeCount_induce c k v inj, enum, deg, Nat.add_comm (DeletionCount.pairs _ ys)]
    exact same
  · have lower := DeletionCount.sum_lower (colorDegree c k) xs (colorDegree c k z) (fun u _ => minDeg u)
    have handshake := DeletionCount.degree_sum _ (DeletionCount.adjacent_sym c k)
      (fun i => by simp [colorAdjacent]) xs
    simpa [xs, colorDegree, colorEdgeCount] using Nat.le_trans lower (Nat.le_of_eq handshake)

end Ramsey556
