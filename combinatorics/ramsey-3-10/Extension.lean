import Ramsey39

namespace Ramsey310

/-- Each row is an independent nine-set in Exoo's graph. Every possible
    independent neighborhood of a new vertex misses at least one row. -/
private def blocks : List (List (Fin 39)) := [
  [2, 9, 13, 15, 22, 24, 26, 32, 35],
  [3, 6, 8, 12, 17, 20, 28, 34, 37],
  [4, 8, 11, 18, 20, 29, 31, 33, 37],
  [2, 9, 13, 19, 21, 24, 26, 32, 38],
  [1, 8, 12, 18, 20, 23, 25, 31, 37],
  [2, 7, 9, 10, 15, 24, 27, 32, 38],
  [3, 5, 8, 11, 16, 20, 28, 33, 37],
  [0, 2, 9, 19, 21, 24, 32, 34, 35],
  [1, 3, 8, 12, 17, 20, 28, 30, 37],
  [2, 9, 14, 15, 24, 27, 32, 36, 38]]

private abbrev IndependentNine (b : List (Fin 39)) : Prop :=
  b.length = 9 ∧ b.Nodup ∧ b.Pairwise (fun x y => adjacent x y = false)

private theorem blocks_valid : ∀ b ∈ blocks, IndependentNine b := by
  decide

/-- Try one vertex of each block. The blocked bit mask records all neighbors
    of previously chosen vertices. A vertex may hit more than one block. -/
private def canHit (blocked : Nat) : List (List (Fin 39)) → Bool
  | [] => true
  | b :: bs => b.any fun v =>
      !blocked.testBit v.val && canHit (blocked ||| rows[v.val]!) bs

private theorem canHit_of_independent (N : Fin 39 → Prop)
    (hind : ∀ v w, N v → N w → adjacent v w = false)
    (bs : List (List (Fin 39))) (blocked : Nat)
    (hfree : ∀ v, N v → blocked.testBit v.val = false)
    (hhit : ∀ b ∈ bs, ∃ v ∈ b, N v) : canHit blocked bs = true := by
  induction bs generalizing blocked with
  | nil => rfl
  | cons b bs ih =>
    obtain ⟨v, hv, hNv⟩ := hhit b (by simp)
    apply List.any_eq_true.mpr
    refine ⟨v, hv, ?_⟩
    simp only [hfree v hNv, Bool.not_false, Bool.true_and]
    apply ih
    · intro w hNw
      rw [Nat.testBit_or, hfree w hNw, Bool.false_or]
      exact hind v w hNv hNw
    · intro c hc
      exact hhit c (List.mem_cons_of_mem _ hc)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem blocks_cannot_be_hit : canHit 0 blocks = false := by decide +kernel

/-- For any proposed neighbors of a 40th vertex, Exoo's graph either has an
    edge between two of them (giving a triangle with the new vertex) or has
    nine independent vertices outside them (giving an independent ten-set). -/
theorem exoo_no_one_vertex_extension (N : Fin 39 → Prop) :
    (∃ x y, N x ∧ N y ∧ adjacent x y = true) ∨
    ∃ b : List (Fin 39), b.length = 9 ∧ b.Nodup ∧
      b.Pairwise (fun x y => adjacent x y = false) ∧ ∀ v ∈ b, ¬N v := by
  classical
  by_cases h : ∃ x y, N x ∧ N y ∧ adjacent x y = true
  · exact Or.inl h
  have independent : ∀ v w, N v → N w → adjacent v w = false := by grind
  have misses : ¬∀ b ∈ blocks, ∃ v ∈ b, N v := by
    intro hits
    have found := canHit_of_independent N independent blocks 0 (fun _ _ => by simp) hits
    simp [blocks_cannot_be_hit] at found
  obtain ⟨b, hb, missed⟩ : ∃ b ∈ blocks, ∀ v ∈ b, ¬N v := by simpa using misses
  obtain ⟨size, distinct, pairwise⟩ := blocks_valid b hb
  exact Or.inr ⟨b, size, distinct, pairwise, missed⟩

end Ramsey310
