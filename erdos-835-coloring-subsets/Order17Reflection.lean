import Order17

namespace Erdos835.TwentyPoint

open Finset

abbrev Vertex := Fin 20

/-- The generator rotates 0,...,16 and fixes 17,18,19. -/
def shift (j : Fin 17) (x : Vertex) : Vertex :=
  if x.val < 17 then ⟨(x.val + j.val) % 17, by omega⟩ else x

def translate (j : Fin 17) (Q : Finset Vertex) := Q.image (shift j)

/-- Negation on the 17-cycle, fixing all three remaining points individually. -/
def reflect (x : Vertex) : Vertex :=
  if x.val < 17 then ⟨(17 - x.val) % 17, by omega⟩ else x

private def leftQuad : Finset Vertex := {1, 16, 17, 18}
private def rightQuad : Finset Vertex := {1, 16, 17, 19}
private def sharedTriple : Finset Vertex := {1, 16, 17}

/-- No seed has its reflection carried back to itself by a rotation.
Equivalently, the reflection cannot carry the seed to any one of its
17 developed classes. -/
theorem no_reflection_fixing_three {D : Finset Vertex → Prop}
    (hD : QuadrupleSeed univ translate D) (k : Fin 17) :
    ¬ ∀ Q, D Q → D (translate k (Q.image reflect)) := by
  intro preserve
  have forced (Q : Finset Vertex) (h4 : Q.card = 4)
      (hreflect : ∀ j : Fin 17, translate k ((translate j Q).image reflect) =
        translate (k - j) Q) :
      ∃ j : Fin 17, D (translate j Q) ∧ k - j = j := by
    obtain ⟨j, hj, huniq⟩ := hD.orbits Q (subset_univ _) h4
    exact ⟨j, hj, huniq (k-j) (by simpa only [hreflect j] using preserve _ hj)⟩
  have leftAct : ∀ k j : Fin 17, translate k ((translate j leftQuad).image reflect)
      = translate (k - j) leftQuad := by decide +kernel
  have rightAct : ∀ k j : Fin 17, translate k ((translate j rightQuad).image reflect)
      = translate (k - j) rightQuad := by decide +kernel
  obtain ⟨i, hi, ei⟩ := forced leftQuad (by decide) (leftAct k)
  obtain ⟨j, hj, ej⟩ := forced rightQuad (by decide) (rightAct k)
  have uniqueCenter : ∀ a b s : Fin 17, s - a = a → s - b = b → a = b := by decide +kernel
  obtain rfl := uniqueCenter i j k ei ej
  have triple : ∀ i : Fin 17, (translate i sharedTriple).card = 3 := by decide +kernel
  have inside : ∀ i : Fin 17, translate i sharedTriple ⊆ translate i leftQuad ∧
      translate i sharedTriple ⊆ translate i rightQuad := by decide +kernel
  have distinct : ∀ i : Fin 17, translate i leftQuad ≠ translate i rightQuad := by decide +kernel
  have uniq := hD.triples _ (subset_univ _) (triple i)
  exact distinct i (uniq.unique ⟨hi, (inside i).1⟩ ⟨hj, (inside i).2⟩)

end Erdos835.TwentyPoint
