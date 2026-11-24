import BoxFree.LayerBound

namespace BoxFree

/-- A predicate on the layer indices holds at most once if no ordered pair satisfies it. -/
private theorem count_at_most_one {n : Nat} (p : Fin n → Bool)
    (h : ∀ a b, a < b → p a → ¬ p b) : (List.finRange n).countP p ≤ 1 := by
  rw [List.countP_eq_length_filter]
  have forbidden : ((List.finRange n).filter p).Pairwise (fun _ _ => False) :=
    List.pairwise_filter.mpr ((List.pairwise_lt_finRange n).imp (fun hab => h _ _ hab))
  match hs : (List.finRange n).filter p with
  | [] | [_] => simp
  | a :: b :: xs => exact False.elim (List.rel_of_pairwise_cons (hs ▸ forbidden) List.mem_cons_self)

/-- Each layer needs at least twelve of the 630 slots. A box-free coloring never reuses one. -/
theorem height_le_52 {n : Nat} {C : Coloring n} (free : BoxFree C) : n ≤ 52 := by
  let uses (z : Fin n) (s : Slot) := occupies (C z) s
  have once (s : Slot) : (List.finRange n).countP (fun z => uses z s) ≤ 1 := by
    obtain ⟨⟨rows, color⟩, cols⟩ := s
    apply count_at_most_one
    intro z w hzw hz hw
    exact free _ _ rows.lt _ _ cols.lt color z ((occupies_iff ..).mp hz) w hzw
      ((occupies_iff ..).mp hw)
  have bound : 12 * n ≤ 630 := calc
    12 * n = ((List.finRange n).map fun _ => 12).sum := by
      simp [List.map_const', List.sum_replicate_nat, Nat.mul_comm]
    _ ≤ ((List.finRange n).map fun z => slots.countP (uses z)).sum :=
      sum_mono _ _ _ (fun z => twelve_le (C z))
    _ = (slots.map fun s => (List.finRange n).countP (fun z => uses z s)).sum :=
      double_count _ _ uses
    _ ≤ (slots.map fun _ => 1).sum := sum_mono _ _ _ once
    _ = 630 := by decide +kernel
  omega

end BoxFree
