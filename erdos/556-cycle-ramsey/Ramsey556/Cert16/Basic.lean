import Std

namespace Ramsey556.Cert16

/-- A simple graph with the lower triangular adjacency matrix packed into a natural number. -/
def edge (g i j : Nat) : Bool :=
  i != j && g.testBit ((max i j) * (max i j - 1) / 2 + min i j)

def extendEdge (n g m i j : Nat) : Bool :=
  if i = j then false else if i = n then m.testBit j else if j = n then m.testBit i else edge g i j

def edgeCount (n g : Nat) : Nat :=
  ((List.range n).map (fun i => ((List.range i).filter (edge g i)).length)).sum

def popcount (n m : Nat) : Nat := ((List.range n).filter m.testBit).length

def threshold (n : Nat) : Nat :=
  ([0,0,1,2,4,6,9,12,16,20,24,29,34,40,46,53,60] : List Nat)[n]!

def Safe (n g m : Nat) : Prop :=
  ∀ p : Fin 8 → Fin n, (∀ ⦃i j⦄, p i = p j → i = j) →
    (∀ i : Fin 7, edge g (p i.castSucc).val (p i.succ).val = true) →
    m.testBit (p 0).val = true → m.testBit (p 7).val ≠ true

/-- The graph of the extended coloring occurs in the next catalog up to relabeling. -/
def ExtendsTo (n g m h : Nat) : Prop :=
  ∃ f : Fin (n+1) → Fin (n+1), (∀ ⦃i j⦄, f i = f j → i = j) ∧
    ∀ i j : Fin (n+1), edge h (f i).val (f j).val = extendEdge n g m i.val j.val

theorem inverse_exists {n : Nat} (f : Fin n → Fin n)
    (inj : ∀ ⦃i j⦄, f i = f j → i = j) :
    ∃ g : Fin n → Fin n, (∀ i, f (g i) = i) ∧ (∀ i, g (f i) = i) := by
  classical
  have covers (v : Fin n) : ∃ i, f i = v := by
    apply Classical.byContradiction
    intro missing
    let xs := (List.finRange n).map f
    have nodup : xs.Nodup :=
      (List.nodup_finRange n).map f (fun _ _ hd he => hd (inj he))
    have fresh : v ∉ xs := by
      intro h
      obtain ⟨i, _, e⟩ := List.mem_map.mp h
      exact missing ⟨i, e⟩
    have extra : (v :: xs).Nodup := List.nodup_cons.mpr ⟨fresh,nodup⟩
    have le := extra.length_le_of_subset (l₂ := List.finRange n) (fun {_} _ => List.mem_finRange _)
    simp [xs] at le
    omega
  exact ⟨fun i => (covers i).choose, fun i => (covers i).choose_spec,
    fun i => inj ((covers (f i)).choose_spec)⟩

theorem list_permutation {n : Nat} (f : Fin n → Fin n)
    (inj : ∀ ⦃i j⦄, f i = f j → i = j) :
    ((List.finRange n).map f).Perm (List.finRange n) := by
  obtain ⟨g, right, _⟩ := inverse_exists f inj
  apply (List.perm_ext_iff_of_nodup
    ((List.nodup_finRange n).map f (fun _ _ hd he => hd (inj he))) (List.nodup_finRange _)).2
  exact fun i => ⟨fun _ => List.mem_finRange _, fun _ => List.mem_map.mpr ⟨g i,List.mem_finRange _,right _⟩⟩

end Ramsey556.Cert16
