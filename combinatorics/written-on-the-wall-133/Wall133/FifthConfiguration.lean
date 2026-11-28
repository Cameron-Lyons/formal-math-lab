module

public import Wall133.ShortGirthFifthCertificate
public import Wall133.FifthPathConfiguration

@[expose] public section

namespace Wall133
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A five-edge induced path beginning at a vertex with five independent
neighbors forces an eight-vertex induced path if every vertex has three
independent neighbors. -/
theorem eight_of_five_chain (P : Chain G 5) (h4 : NoFourCycle G)
    (high : 5≤G.indepNeighborsCard (P.vertex 0)) (hmin : ∀ v,3≤G.indepNeighborsCard v) :
    8 ≤ G.path := by
  obtain ⟨f,facts⟩ := FifthCertificate.exists_configuration P h4 high hmin
  exact FifthCertificate.eight_of_certificate f h4 facts

end Wall133
