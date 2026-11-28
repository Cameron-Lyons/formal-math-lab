import E1486

namespace E1486.Simple

/-- Fix a square q = z⋆z. The two squares x⋆x and (x⋆q)⋆(x⋆q) determine x. -/
def squarePair {S : Type} (op : S → S → S) (z x : S) : S × S :=
  let b := op x (op z z)
  (op x x, op b b)

theorem squarePair_injective {S : Type} {op : S → S → S} (h : Law op) (z : S) :
    Function.Injective (squarePair op z) := by
  let q := op z z
  have hq : Square op q := ⟨z, rfl⟩
  apply Function.LeftInverse.injective (g := fun p : S × S => op p.1 (op p.2 q))
  intro x
  change op (op x x) (op (op (op x q) (op x q)) q) = x
  rw [recover_target h x hq]
  exact recover_source h x hq

/-- If a list of k labels contains all square values, the order is at most k². -/
theorem card_le_square_of_cover {n : Nat} (op : Fin n → Fin n → Fin n) (h : Law op)
    (squares : List (Fin n)) (covers : ∀ x, op x x ∈ squares) :
    n ≤ squares.length * squares.length := by
  cases n with
  | zero => exact Nat.zero_le _
  | succ n =>
    let pairs := squares.flatMap fun a => squares.map fun b => (a,b)
    let code := squarePair op 0
    have inj := squarePair_injective h (0 : Fin (n+1))
    have distinct : ((List.finRange (n+1)).map code).Nodup :=
      List.pairwise_map.mpr ((List.nodup_finRange _).imp (fun hne he => hne (inj he)))
    have sub : (List.finRange (n+1)).map code ⊆ pairs := by
      intro p hp
      obtain ⟨x,_,rfl⟩ := List.mem_map.mp hp
      exact List.mem_flatMap.mpr ⟨op x x, covers x, List.mem_map.mpr ⟨_,covers _,rfl⟩⟩
    simpa [pairs,List.length_flatMap,List.map_const',List.sum_replicate_nat]
      using distinct.length_le_of_subset sub

/-- For order 15, any initial segment that contains all squares has at least four labels. -/
theorem four_le_square_labels {op : Fin 15 → Fin 15 → Fin 15} (h : Law op)
    {k : Nat} (hk : k ≤ 15) (bound : ∀ q, Square op q → q.val < k) : 4 ≤ k := by
  let embed (q : Fin k) : Fin 15 := ⟨q.val, Nat.lt_of_lt_of_le q.isLt hk⟩
  let labels := (List.finRange k).map embed
  have cover (x : Fin 15) : op x x ∈ labels := by
    let idx : Fin k := ⟨(op x x).val, bound (op x x) ⟨x,rfl⟩⟩
    exact List.mem_map.mpr ⟨idx, List.mem_finRange _, rfl⟩
  have hn : 15 ≤ k*k := by simpa [labels] using card_le_square_of_cover op h labels cover
  by_cases low : k ≤ 3
  · have := Nat.mul_self_le_mul_self low; omega
  · omega

end E1486.Simple
