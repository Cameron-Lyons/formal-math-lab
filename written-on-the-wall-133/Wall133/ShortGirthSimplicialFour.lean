module

public import Wall133.ShortGirthCertificate
public import Wall133.ShortGirthFourConfiguration

@[expose] public section

namespace Wall133
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A four-edge geodesic starting at a high vertex of the independence core
forces an eight-vertex induced path when its far endpoint is simplicial. -/
theorem eight_of_simplicial_end (P : Chain G 4) (h4 : NoFourCycle G) (hc : G.Connected)
    (geo : ∀ i ≤ 4,G.dist (P.vertex 0) (P.vertex i)=i) (S : Set V)
    (atRoot : IndependentCoreStar G S (P.vertex 0) 4)
    (core : ∀ w∈S, Nonempty (IndependentCoreStar G S w 3))
    (simplicial : ∀ z,G.Adj z (P.vertex 4) → z≠P.vertex 3 → G.Adj z (P.vertex 3)) :
    8 ≤ G.path := by
  obtain ⟨f,e3,e4,hf⟩ := exists_fourth_configuration P h4 hc geo S atRoot core
  apply FourthCertificate.eight_of_certificate f h4 _ hf
  simpa only [e3,e4] using simplicial

end Wall133
