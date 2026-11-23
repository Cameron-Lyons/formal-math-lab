import Ramsey556.Split17
import Ramsey556.Split17.Lower

namespace Ramsey556

/-- The graph has n vertices, with all edges except pairs lying wholly outside
the first m vertices. Only the two colors on its actual edges are relevant. -/
def SplitForcesC9 (m n : Nat) : Prop :=
  ∀ c : Coloring n,
    (∀ i j, i ≠ j → (i.val < m ∨ j.val < m) → c.edge i j = 0 ∨ c.edge i j = 1) →
    ∃ (k : Fin 3) (p : Fin 9 → Fin n), (k = 0 ∨ k = 1) ∧
      (∀ ⦃i j⦄, p i = p j → i = j) ∧
      ∀ i, ((p i).val < m ∨ (p (i+1)).val < m) ∧ c.edge (p i) (p (i+1)) = k

private theorem split_upper (m n : Nat) (hm : 13 ≤ m) (hn : 17 ≤ n) : SplitForcesC9 m n := by
  intro c uses
  let f (i : Fin 17) : Fin n := ⟨i.val,by omega⟩
  have fi : ∀ ⦃i j⦄, f i = f j → i = j := fun {_ _} e => Fin.ext (congrArg (fun x : Fin n => x.val) e)
  let d : Coloring 17 := {
    edge := fun i j => if i.val < 13 ∨ j.val < 13 then c.edge (f i) (f j) else 2
    symm := fun i j => by simp only [or_comm (a := i.val < 13), c.symm (f i) (f j)] }
  have labels (i j : Fin 17) (ne : i ≠ j) (h : i.val < 13 ∨ j.val < 13) : d.edge i j = 0 ∨ d.edge i j = 1 := by
    simpa [d,h] using uses (f i) (f j) (fun e => ne (fi e)) (by change i.val<m ∨ j.val<m; omega)
  obtain ⟨k,p,pi,edges⟩ := Split17.hasMonoC9 d 0 1 (by decide) id (fun {_ _} e => e) labels
  have seen : ∃ i, (p i).val < 13 := by
    apply Classical.byContradiction
    intro fail
    have high (i) : 13 ≤ (p i).val := Nat.le_of_not_gt (fun h => fail ⟨i,h⟩)
    let q (i : Fin 9) : Fin 8 := ⟨(p i).val-13,by have := high i; omega⟩
    apply no_injection_nine_eight q
    intro i j eq
    apply pi
    apply Fin.ext
    have e := congrArg Fin.val eq
    dsimp [q] at e
    have := high i
    have := high j
    omega
  obtain ⟨i,hi⟩ := seen
  have ni (j : Fin 9) : p j ≠ p (j+1) := fun eq => (by decide : ∀ x : Fin 9, x ≠ x+1) j (pi eq)
  have pal := labels _ _ (ni i) (Or.inl hi)
  rw [edges i] at pal
  refine ⟨k,fun j => f (p j),pal,fun {_ _} e => pi (fi e),?_⟩
  intro j
  have e := edges j
  change (if (p j).val < 13 ∨ (p (j+1)).val < 13 then _ else (2 : Fin 3)) = k at e
  split at e
  · rename_i h
    exact ⟨by change (p j).val < m ∨ (p (j+1)).val < m; omega,e⟩
  · omega

private theorem split_small_order (m n : Nat) (hn : n ≤ 16) : ¬ SplitForcesC9 m n := by
  intro ramsey
  let v (i : Fin n) : Fin 32 := ⟨i.val,by omega⟩
  let rotate (k : Fin 3) := k+2
  let d := (lowerColoring.induce v).recolor rotate
  have perm : ∀ i j, rotate i = rotate j → i=j := by decide
  have uses (i j : Fin n) : d.edge i j = 0 ∨ d.edge i j = 1 := by
    exact (by decide : ∀ x y : Fin 32, x.val < 16 → y.val < 16 →
      lowerColoring.edge x y + 2 = 0 ∨ lowerColoring.edge x y + 2 = 1) (v i) (v j) (by dsimp [v];omega) (by dsimp [v];omega)
  obtain ⟨k,p,_,pi,edges⟩ := ramsey d (fun i j _ _ => uses i j)
  exact lowerColoring_no_monoC9 (hasMonoC9_of_copy lowerColoring v rotate
    (fun {_ _} e => Fin.ext (congrArg (fun z : Fin 32 => z.val) e)) (fun {_ _} => perm _ _)
    ⟨k,p,pi,fun i => (edges i).2⟩)

/-- A complete split graph forces a monochromatic nine-cycle in two colors
exactly when it has at least 17 vertices and a clique side of size at least 13. -/
theorem splitForcesC9_iff (m n : Nat) : SplitForcesC9 m n ↔ 13 ≤ m ∧ 17 ≤ n := by
  refine ⟨fun h => ⟨?_,?_⟩,fun ⟨hm,hn⟩ => split_upper m n hm hn⟩
  · apply Nat.le_of_not_gt
    intro hm
    obtain ⟨d,uses,no0,no1⟩ := Split17.small_core_example n
    obtain ⟨k,p,pal,pi,he⟩ := h d (fun i j ne h => uses i j ne (by omega))
    have cycle : HasC9In d k := ⟨p,pi,fun i => (he i).2⟩
    rcases pal with rfl|rfl
    · exact no0 cycle
    · exact no1 cycle
  · apply Nat.le_of_not_gt
    intro hn
    exact split_small_order m n (by omega) h

end Ramsey556
