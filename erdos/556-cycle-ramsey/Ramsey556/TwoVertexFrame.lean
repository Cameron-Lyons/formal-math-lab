import Ramsey556.TwoColor

namespace Ramsey556

/-- An independent set of sixteen vertices divided into two octets. Each exterior
vertex has red (color zero) edges to at least seven vertices of its chosen octet. -/
structure SupportedOctets (c : Coloring 33) where
  anchor : Fin 2 → Fin 8 → Fin 33
  outer : Fin 17 → Fin 33
  tag : Fin 17 → Fin 2
  anchorInj : ∀ ⦃s t i j⦄, anchor s i = anchor t j → s = t ∧ i = j
  outerInj : ∀ ⦃i j⦄, outer i = outer j → i = j
  disjoint : ∀ s i v, anchor s i ≠ outer v
  independent : ∀ s t i j, (s,i) ≠ (t,j) → c.edge (anchor s i) (anchor t j) ≠ 0
  supports : ∀ v, ∃ bad : Fin 8, ∀ i, i ≠ bad → c.edge (outer v) (anchor (tag v) i) = 0

def SupportedOctets.members {c : Coloring 33} (S : SupportedOctets c) (s : Fin 2) : List (Fin 17) :=
  (List.finRange 17).filter (fun v => S.tag v == s)

/-- Every 17-vertex set contains a red edge. -/
def NoIndependent17 (c : Coloring 33) : Prop :=
  ∀ v : Fin 17 → Fin 33, (∀ ⦃i j⦄, v i = v j → i = j) →
    ∃ i j, i ≠ j ∧ c.edge (v i) (v j) = 0

/-- Two vertex-disjoint red edges going from the chosen exterior type to its complement. -/
structure OuterMatching {c : Coloring 33} (S : SupportedOctets c) (big : Fin 2) where
  left : Fin 2 → Fin 17
  right : Fin 2 → Fin 17
  leftType : ∀ i, S.tag (left i) = big
  rightType : ∀ i, S.tag (right i) ≠ big
  leftNe : left 0 ≠ left 1
  rightNe : right 0 ≠ right 1
  edge : ∀ i, c.edge (S.outer (left i)) (S.outer (right i)) = 0

end Ramsey556
