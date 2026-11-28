import Ramsey556.Certified16

namespace Ramsey556.CriticalTemplates

/-- Either a cycle in the light color, or a permutation to a two-color template. -/
structure Witness (T : Type) where
  cycle : Bool
  heavyInside : Bool
  shape : T
  labels : Nat

def label {T : Type} {n : Nat} (positive : 0 < n) (w : Witness T) (i : Nat) : Fin n :=
  ⟨((w.labels >>> (4*i)) % 16) % n, Nat.mod_lt _ positive⟩

def Verified {n : Nat} {T : Type} (positive : 0 < n)
    (pattern : T → Fin n → Fin n → Bool) (g : Nat) (w : Witness T) : Prop :=
  let f := label positive w
  if w.cycle then
    (∀ i j : Fin 9, f i = f j → i = j) ∧
    (∀ i : Fin 9, Cert16.edge g (f i).val (f (i+1 : Fin 9)).val = false)
  else
    (∀ i j : Fin n, f i = f j → i = j) ∧
    (∀ i j : Fin n, i ≠ j → Cert16.edge g (f i).val (f j).val =
      (if pattern w.shape i j then w.heavyInside else !w.heavyInside))

def Matches {n : Nat} {T : Type} (pattern : T → Fin n → Fin n → Bool)
    (c : Coloring n) (r s : Fin 3) : Prop :=
  ∃ (t : T) (a b : Fin 3) (v : Fin n → Fin n),
    ((a = r ∧ b = s) ∨ (a = s ∧ b = r)) ∧
    Function.Injective v ∧
    ∀ i j, i ≠ j → c.edge (v i) (v j) = if pattern t i j then a else b

private theorem sum_edges {n : Nat} (c : Coloring n) (r s : Fin 3) (ne : r ≠ s)
    (uses : ∀ i j, i ≠ j → c.edge i j = r ∨ c.edge i j = s) :
    colorEdgeCount c r + colorEdgeCount c s =
      DeletionCount.pairs (fun i j : Fin n => decide (i ≠ j)) (List.finRange n) := by
  simp only [colorEdgeCount, count_pairList]
  generalize pairList (List.finRange n) = edges
  induction edges with
  | nil => rfl
  | cons edge rest ih =>
    obtain ⟨x,y⟩ := edge
    by_cases eq : x = y
    · simpa [List.countP_cons, colorAdjacent, eq] using ih
    · rcases uses x y eq with h | h <;>
        simp [colorAdjacent, eq, h, ne, ne.symm] at ih ⊢ <;> omega

/-- Read a checked witness in the original coloring via the catalog's vertex map. -/
private theorem matches_of_row {n g : Nat} {T : Type} {pattern : T → Fin n → Fin n → Bool}
    {c : Coloring n} {r s : Fin 3} (M : Cert16.Model g c r) (w : Witness T)
    {pos : 0 < n} (cert : Verified pos pattern g w) (ne : r ≠ s)
    (uses : ∀ i j, i ≠ j → c.edge i j = r ∨ c.edge i j = s)
    (free : ¬ HasMonoC9 c) : Matches pattern c r s := by
  let f := label pos w
  have fromGraph {a b : Fin n} (neq : a ≠ b) :
      c.edge (M.vertex a) (M.vertex b) = if Cert16.edge g a.val b.val then r else s := by
    have apart : M.vertex a ≠ M.vertex b := fun eq => neq (M.inj eq)
    rw [M.agree]
    rcases uses _ _ apart with eq|eq <;> simp [eq,apart,ne.symm]
  change (if w.cycle then _ else _) at cert
  split at cert
  · obtain ⟨inj,edges⟩ := cert
    refine (free ⟨s,fun j => M.vertex (f j.val),fun {_ _} eq => inj _ _ (M.inj eq),?_⟩).elim
    intro j
    have next : j ≠ j+1 := (by decide : ∀ t : Fin 9, t ≠ t+1) j
    rw [fromGraph (fun e => next (inj _ _ e)), edges]
    rfl
  · obtain ⟨inj,edges⟩ := cert
    refine ⟨w.shape,if w.heavyInside then r else s,if w.heavyInside then s else r,
      fun j => M.vertex (f j.val),?_,fun {_ _} eq => inj _ _ (M.inj eq),?_⟩
    · cases w.heavyInside <;> simp
    · intro j k neq
      rw [fromGraph (fun e => neq (inj _ _ e)), edges _ _ neq]
      cases w.heavyInside <;> cases pattern w.shape j k <;> simp

/-- The heavier color appears in the catalog. Each checked row then either
exhibits a cycle in the opposite color or identifies the entire coloring. -/
theorem classify {n count : Nat} {T : Type} (pos : 0 < n) (top : n ≤ 16)
    (rows : Vector (Witness T) count) (pattern : T → Fin n → Fin n → Bool)
    (num : (Cert16.table n).size = count)
    (checked : ∀ i : Fin count, Verified pos pattern ((Cert16.table n).get i.val) rows[i])
    (half : 2 * Cert16.threshold n ≤ 1 + DeletionCount.pairs (fun i j : Fin n => decide (i ≠ j)) (List.finRange n))
    (c : Coloring n) (r s : Fin 3) (ne : r ≠ s)
    (uses : ∀ i j, i ≠ j → c.edge i j = r ∨ c.edge i j = s)
    (free : ¬ HasMonoC9 c) : Matches pattern c r s := by
  have heavy (r s : Fin 3) (ne : r ≠ s)
      (uses : ∀ i j, i ≠ j → c.edge i j = r ∨ c.edge i j = s)
      (dense : Cert16.threshold n ≤ colorEdgeCount c r) : Matches pattern c r s := by
    obtain ⟨g,member,⟨M⟩⟩ := Cert16.model_exists Cert16.completeCatalog n c r pos top
      dense (fun h => free ⟨r,h⟩)
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp member
    let idx : Fin count := ⟨i,num ▸ List.mem_range.mp hi⟩
    exact matches_of_row M rows[idx] (checked idx) ne uses free
  have total := sum_edges c r s ne uses
  by_cases h : Cert16.threshold n ≤ colorEdgeCount c r
  · exact heavy r s ne uses h
  obtain ⟨t,a,b,v,colors,inj,edges⟩ := heavy s r ne.symm (fun i j ij => (uses i j ij).symm) (by omega)
  exact ⟨t,a,b,v,colors.symm,inj,edges⟩

end Ramsey556.CriticalTemplates
