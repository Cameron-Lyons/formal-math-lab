import ThreeStacks.OrderProof.Learned20

namespace ThreeStacks

/-- No pair of intermediate permutations satisfies the three single-stack
    order constraints for the published 21-card permutation. -/
theorem noWitnessOrders (A B : List Nat) (hA : IsDeck 21 A) (hB : IsDeck 21 B)
    (h₁ : Respects published A) (h₂ : Respects A B) (h₃ : Respects B (target 21)) :
    False :=
  OrderProof.c17680 ⟨A, B, hA, hB, h₁, h₂, h₃⟩

end ThreeStacks
