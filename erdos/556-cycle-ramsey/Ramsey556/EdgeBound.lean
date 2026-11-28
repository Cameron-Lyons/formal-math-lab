import Ramsey556.TwoColor

namespace Ramsey556

/-- The unordered edges of K₁₆, each stored with its smaller endpoint first. -/
private def edges16 : List (Fin 16 × Fin 16) :=
  (List.finRange 16).flatMap fun i =>
    ((List.finRange 16).filter (i < ·)).map fun j => (i, j)

def edgeCount16 (c : Coloring 16) (k : Fin 3) : Nat :=
  (edges16.filter (fun e => c.edge e.1 e.2 == k)).length

/-- A single-color extremal statement. Theorem 9 of Dzido, Kubale and
Piwakowski (2006) gives a stronger threshold of 58 edges. The two-color
Ramsey argument needs only 60. -/
def DenseC9Free16Bipartite : Prop := ∀ (c : Coloring 16) (k : Fin 3),
  60 ≤ edgeCount16 c k → (¬ HasC9In c k) → IsBipartiteColor c k

set_option maxRecDepth 8192 in
private theorem denserColor (c : Coloring 16) (absent : ∀ i j, i ≠ j → c.edge i j ≠ 0) :
    ∃ k : Fin 3, k ≠ 0 ∧ 60 ≤ edgeCount16 c k := by
  have allEdges : ∀ e ∈ edges16, e.1 ≠ e.2 := by decide
  have partition (xs : List (Fin 16 × Fin 16)) (h : ∀ e ∈ xs, e.1 ≠ e.2) :
      (xs.filter (fun e => c.edge e.1 e.2 == 1)).length +
      (xs.filter (fun e => c.edge e.1 e.2 == 2)).length = xs.length := by
    induction xs with
    | nil => rfl
    | cons e xs ih =>
      have tail := ih (fun a ha => h a (List.mem_cons_of_mem e ha))
      obtain ⟨i,j⟩ := e
      have nonzero := absent i j (h _ List.mem_cons_self)
      have cases : c.edge i j = 1 ∨ c.edge i j = 2 := by omega
      rcases cases with h | h <;> simp [h] <;> omega
  have total := partition edges16 allEdges
  change edgeCount16 c 1 + edgeCount16 c 2 = edges16.length at total
  have size : edges16.length = 120 := by decide
  by_cases one : 60 ≤ edgeCount16 c 1
  · exact ⟨1, by decide, one⟩
  · exact ⟨2, by decide, by omega⟩

/-- The denser color has a bipartition. Its two sides are cliques in the
other color, so avoiding a C₉ forces both sizes to be exactly eight. -/
theorem twoColorOctets16_of_edgeBound (bound : DenseC9Free16Bipartite) : TwoColorOctets16 := by
  intro c absent free
  obtain ⟨k, hk, dense⟩ := denserColor c absent
  obtain ⟨side, cut⟩ := bound c k dense (fun h => free ⟨k, h⟩)
  have inside {i j : Fin 16} (ne : i ≠ j) (same : side i = side j) :
      c.edge i j = otherNonzero k := by
    have first := absent i j ne
    have second : c.edge i j ≠ k := fun he => cut i j ne he same
    exact (show ∀ k x : Fin 3, k ≠ 0 → x ≠ 0 → x ≠ k → x = otherNonzero k by decide)
      k _ hk first second
  let cell (b : Bool) := (List.finRange 16).filter (fun x => side x == b)
  have nd (b : Bool) : (cell b).Nodup := (List.nodup_finRange 16).filter _
  have tag (b : Bool) (i : Nat) (hi : i < (cell b).length) : side ((cell b)[i]) = b := by
    have mem : (cell b)[i] ∈ cell b := List.getElem_mem hi
    exact beq_iff_eq.mp (List.mem_filter.mp mem).2
  have small (b : Bool) : (cell b).length ≤ 8 := by
    apply Nat.le_of_not_gt
    intro enough
    let v (i : Fin 9) := (cell b)[i.val]'(by omega)
    have inj : ∀ ⦃i j⦄, v i = v j → i = j := fun {_ _} e =>
      Fin.ext ((nd b).eq_of_getElem_eq _ _ e)
    apply free
    refine ⟨otherNonzero k, v, inj, fun i => inside ?_ ((tag b _ _).trans (tag b _ _).symm)⟩
    exact fun e => (by decide : ∀ j : Fin 9, j ≠ j+1) i (inj e)
  have total : 16 = (cell true).length + (cell false).length := by
    simpa [cell, List.countP_eq_length_filter] using
      List.length_eq_countP_add_countP side (l := List.finRange 16)
  let bit (a : Fin 2) := decide (a = 1)
  have size (b : Bool) : (cell b).length = 8 := by
    have := small true
    have := small false
    cases b <;> omega
  let v (a : Fin 2) (i : Fin 8) := (cell (bit a))[i.val]'(by rw [size]; exact i.isLt)
  have inj (a : Fin 2) : ∀ ⦃i j⦄, v a i = v a j → i = j :=
    fun {_ _} e => Fin.ext ((nd _).eq_of_getElem_eq _ _ e)
  refine ⟨otherNonzero k, (by decide : ∀ j : Fin 3, otherNonzero j ≠ 0) k, ⟨⟨v, ?_, ?_⟩⟩⟩
  · intro a b i j e
    have bitInj : ∀ a b, bit a = bit b → a = b := by decide
    have eq := bitInj a b ((tag (bit a) _ _).symm.trans ((congrArg side e).trans (tag (bit b) _ _)))
    subst b
    exact ⟨rfl, inj a e⟩
  · intro a i j ne
    exact inside (fun e => ne (inj a e)) ((tag (bit a) _ _).trans (tag (bit a) _ _).symm)

end Ramsey556
