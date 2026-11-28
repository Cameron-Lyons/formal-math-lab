import ThreeStacks.Lower

namespace ThreeStacks

private theorem pass_contents {i s o : List Nat} (h : Pass i s o) :
    (s ++ i).Perm o := by
  induction h with
  | done => exact .nil
  | push _ ih => exact List.perm_middle.trans ih
  | pop _ ih => exact .cons _ ih

theorem pass_perm {u v : List Nat} (h : Pass u [] v) : u.Perm v :=
  pass_contents h

private theorem filter_order (p : Nat → Bool) {a b : Nat}
    (ha : p a = true) (hb : p b = true) (l : List Nat)
    (h : l.idxOf a < l.idxOf b) : (l.filter p).idxOf a < (l.filter p).idxOf b := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
    by_cases xa : x = a
    · subst x
      have ab : a ≠ b := by intro e; subst b; omega
      simp [ha, List.idxOf_cons, ab]
    · by_cases xb : x = b
      · subst x; simp at h
      · have ht : xs.idxOf a < xs.idxOf b := by
          simpa [List.idxOf_cons, xa, Ne.symm xa, xb, Ne.symm xb] using h
        cases hx : p x <;> simpa [List.filter_cons, hx, List.idxOf_cons, xa, Ne.symm xa, xb, Ne.symm xb] using ih ht

/-- A duplicate-free list supported on these three labels in this order is that triple. -/
private theorem exact_three {a b c : Nat} {l : List Nat} (hn : l.Nodup)
    (only : ∀ x ∈ l, x = a ∨ x = b ∨ x = c) (mc : c ∈ l)
    (ab : l.idxOf a < l.idxOf b) (bc : l.idxOf b < l.idxOf c) :
    l = [a,b,c] := by
  have sub : l ⊆ [a,b,c] := by
    intro x hx
    simpa using only x hx
  have bound : l.length ≤ 3 := hn.length_le_of_subset sub
  have hc := List.idxOf_lt_length_of_mem mc
  have len : l.length = 3 := by omega
  have ia : l.idxOf a = 0 := by omega
  have ib : l.idxOf b = 1 := by omega
  have ic : l.idxOf c = 2 := by omega
  have ga := List.getElem_idxOf (x := a) (xs := l) (by omega)
  have gb := List.getElem_idxOf (x := b) (xs := l) (by omega)
  have gc := List.getElem_idxOf hc
  simp only [ia] at ga
  simp only [ib] at gb
  simp only [ic] at gc
  apply List.ext_getElem (by simpa using len)
  intro i hi _
  have cases3 : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases cases3 with rfl | rfl | rfl
  · exact ga
  · exact gb
  · exact gc

private theorem impossible_triple {a b c : Nat} (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c) :
    ¬ Pass [a,b,c] [] [c,a,b] := by
  intro h
  repeat first | contradiction | cases ‹Pass _ _ _›

theorem pass_respects {u v : List Nat} (h : Pass u [] v) (hu : u.Nodup) : Respects u v := by
  intro a b c hab hbc hca' hab'
  let p := fun (x : Nat) => x == a || x == b || x == c
  have pa : p a = true := by simp [p]
  have pb : p b = true := by simp [p]
  have pc : p c = true := by simp [p]
  have support (l : List Nat) : ∀ x ∈ l.filter p, x = a ∨ x = b ∨ x = c := by
    intro x hx
    have hx' := (List.mem_filter.mp hx).2
    simpa [p, or_assoc] using hx'
  have perm := pass_perm h
  have cv : c ∈ v := List.idxOf_lt_length_iff.mp (Nat.lt_of_lt_of_le hca' List.idxOf_le_length)
  have bu : b ∈ u := List.idxOf_lt_length_iff.mp (Nat.lt_of_lt_of_le hbc List.idxOf_le_length)
  have cu : c ∈ u.filter p := List.mem_filter.mpr ⟨perm.mem_iff.mpr cv, pc⟩
  have bv : b ∈ v.filter p := List.mem_filter.mpr ⟨perm.mem_iff.mp bu, pb⟩
  have hin := exact_three (hu.filter _) (support u) cu (filter_order p pa pb u hab) (filter_order p pb pc u hbc)
  have hout := exact_three ((perm.nodup hu).filter _) (fun x hx => by
    rcases support v x hx with h | h | h <;> simp_all) bv (filter_order p pc pa v hca') (filter_order p pa pb v hab')
  have bad := h.filter p
  rw [hin, hout] at bad
  exact impossible_triple (by intro e; subst b; omega) (by intro e; subst c; omega)
    (by intro e; subst c; omega) bad

end ThreeStacks
