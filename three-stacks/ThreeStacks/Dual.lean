import ThreeStacks.Model

namespace ThreeStacks

/-- Read a single-stack trace backwards before a continuation on its initial
    stack. Each former push is a pop, and each former pop is a push. -/
theorem Pass.undoAux {i s o : List Nat} (h : Pass i s o) {tail out : List Nat}
    (next : Pass tail s out) : Pass (o.reverse ++ tail) [] (i.reverse ++ out) := by
  induction h generalizing tail out with
  | done => simpa using next
  | @push a i s o _ ih => simpa using ih (Pass.pop (x := a) next)
  | @pop a i s o _ ih => simpa using ih (Pass.push (x := a) next)

theorem Pass.undo {i o : List Nat} (h : Pass i [] o) : Pass o.reverse [] i.reverse := by
  simpa using h.undoAux Pass.done

/-- Taking the three reversed traces in reverse stack order undoes a sorting run. -/
theorem SortsTo.undo {p q : List Nat} (h : SortsTo p q) : SortsTo q.reverse p.reverse := by
  obtain ⟨a,b,h₁,h₂,h₃⟩ := h
  exact ⟨b.reverse,a.reverse,h₃.undo,h₂.undo,h₁.undo⟩

theorem Pass.map {i s o : List Nat} (h : Pass i s o) (f : Nat → Nat) :
    Pass (i.map f) (s.map f) (o.map f) := by
  induction h with
  | done => exact .done
  | push _ ih => exact .push ih
  | pop _ ih => exact .pop ih

theorem SortsTo.map {p q : List Nat} (h : SortsTo p q) (f : Nat → Nat) :
    SortsTo (p.map f) (q.map f) := by
  obtain ⟨a,b,h₁,h₂,h₃⟩ := h
  exact ⟨a.map f,b.map f,h₁.map f,h₂.map f,h₃.map f⟩

/-- Reflect the permutation plot in the antidiagonal. Card labels start at 1,
    while `idxOf` is zero-based. -/
def dual (n : Nat) (p : List Nat) : List Nat :=
  (target n).reverse.map (fun v => n - p.idxOf v)

/-- The relabeling takes decreasing ordinary labels back to the original input. -/
private theorem relabelReverse {n : Nat} {p : List Nat} (hp : IsDeck n p) :
    (target n).reverse.map (fun x => (p[n-x]?).getD 0) = p := by
  have L : p.length = n := by simpa [target] using hp.length_eq
  apply List.ext_getElem
  · simp [target, L]
  · intro i h₁ h₂
    simp only [List.getElem_map, List.getElem_reverse, target, List.getElem_range',
      List.length_range',Nat.one_mul]
    have e : n - (1 + (n-1-i)) = i := by omega
    simp [e,List.getElem?_eq_getElem h₂]

private theorem relabelDual {n : Nat} {p : List Nat} (hp : IsDeck n p) :
    (dual n p).reverse.map (fun x => (p[n-x]?).getD 0) = target n := by
  have L : p.length = n := by simpa [target] using hp.length_eq
  simp only [dual, ← List.map_reverse, List.reverse_reverse, List.map_map]
  apply Eq.trans (List.map_congr_left (g := id) ?_) (List.map_id _)
  intro a ha
  have found := List.idxOf_lt_length_of_mem (hp.mem_iff.mpr ha)
  have e : n - (n - p.idxOf a) = p.idxOf a := by omega
  simp [e,List.getElem?_eq_getElem found,List.getElem_idxOf]

/-- A schedule sorting the exact reflected deck supplies a schedule for the original. -/
theorem dual_sorts {n : Nat} {p : List Nat} (hp : IsDeck n p)
    (h : Sortable n (dual n p)) : Sortable n p := by
  have run := SortsTo.map (SortsTo.undo h) (fun x => (p[n-x]?).getD 0)
  rw [relabelReverse hp,relabelDual hp] at run
  exact run

private theorem reverseRanks {n : Nat} {p : List Nat} (hp : IsDeck n p) :
    p.reverse.map (fun v => n - p.idxOf v) = target n := by
  have L : p.length = n := by simpa [target] using hp.length_eq
  have nd := hp.nodup_iff.mpr (List.nodup_range' 1)
  apply List.ext_getElem
  · simp [target,L]
  · intro i h₁ h₂
    simp only [List.getElem_map,List.getElem_reverse,nd.idxOf_getElem,target,
      List.getElem_range', Nat.one_mul]
    simp [target] at h₂
    omega

/-- The formula for reflection produces a permutation of precisely the same labels. -/
theorem dual_isDeck {n : Nat} {p : List Nat} (hp : IsDeck n p) : IsDeck n (dual n p) := by
  have rev : (target n).reverse.Perm p.reverse :=
    (List.reverse_perm _).trans (hp.symm.trans (List.reverse_perm _).symm)
  have hm := rev.map (fun v => n - p.idxOf v)
  rw [reverseRanks hp] at hm
  exact hm

/-- Reflection in either direction preserves sortability. -/
theorem dual_sortable_iff {n : Nat} {p : List Nat} (hp : IsDeck n p) :
    Sortable n (dual n p) ↔ Sortable n p := by
  refine ⟨dual_sorts hp, fun h => ?_⟩
  have run := (SortsTo.undo h).map (fun v => n - p.idxOf v)
  rw [reverseRanks hp] at run
  exact run

private theorem dualAt (n i : Nat) (p : List Nat) (hi : i < (dual n p).length) :
    (dual n p)[i] = n - p.idxOf (n-i) := by
  have bound : i < n := by simpa [dual,target] using hi
  simp only [dual,List.getElem_map,List.getElem_reverse,target,List.getElem_range',
    List.length_range',Nat.one_mul]
  congr 2
  omega

/-- Reflecting twice returns the original permutation, position by position. -/
theorem dual_dual {n : Nat} {p : List Nat} (hp : IsDeck n p) : dual n (dual n p) = p := by
  have len : p.length = n := by simpa [target] using hp.length_eq
  have nd := hp.nodup_iff.mpr (List.nodup_range' 1)
  have dd := (dual_isDeck hp).nodup_iff.mpr (List.nodup_range' 1)
  apply List.ext_getElem
  · simp [dual,target,len]
  · intro i hi hip
    have range := List.mem_range'_1.mp (hp.mem_iff.mp (List.getElem_mem hip))
    have hpos : n-p[i] < (dual n p).length := by
      simp [dual,target]; omega
    have card := dualAt n (n-p[i]) p hpos
    have trunc : n - (n-p[i]) = p[i] := by omega
    rw [trunc,nd.idxOf_getElem] at card
    have index := dd.idxOf_getElem (n-p[i]) hpos
    rw [card] at index
    rw [dualAt,index,trunc]

end ThreeStacks
