import Simple.FiniteBase
import Simple.TestOfLaw

namespace E1486.Simple

/-- The 225 bits of a relation on the 15 vertices. -/
noncomputable def pack (G : Fin 15 → Fin 15 → Prop) : BitVec 225 := Test.pack G

theorem pack_get (G : Fin 15 → Fin 15 → Prop) (a b : Fin 15) :
    (pack G).getLsbD (15*a.val+b.val) = true ↔ G a b := Test.edge_pack G a b

end E1486.Simple
