module

public import Erdos617.LineObstruction

@[expose] public section

namespace Erdos617

open Finset SimpleGraph

variable {V L : Type*} [DecidableEq V] [DecidableEq L]
variable {r t : ℕ} {c : Sym2 V → Fin r} {k : Fin r} {S : Finset V}

omit [DecidableEq L] in
/-- Each vertex of a full clique needs a neighbor outside it in the obstruction. -/
theorem MinimalObstruction.full_clique_external_neighbor (h : MinimalObstruction c k t S)
    (C : Finset V) (hCS : C ⊆ S) (hC : (colorGraph c k).IsNClique r C) (x : V) (hx : x ∈ C) :
    ∃ y ∈ S \ C, (colorGraph c k).Adj y x := by
  classical
  by_contra! hnone
  let G := colorGraph c k
  have sub : S.filter (G.Adj x) ⊆ C.erase x := by
    intro y hy
    obtain ⟨hyS,ha⟩ := mem_filter.mp hy
    refine mem_erase.mpr ⟨ha.ne.symm,?_⟩
    by_contra hyC
    exact hnone y (mem_sdiff.mpr ⟨hyS,hyC⟩) ha.symm
  exact (h.degree_ge x (hCS hx)).not_gt ((card_le_card sub).trans_lt
    ((card_lt_card (erase_ssubset hx)).trans_eq hC.card_eq))

/-- No two edges represented by vertices of a full clique in a minimal
obstruction can be parallel. An external neighbor distinguishes them. -/
theorem MinimalObstruction.injOn_full_clique (h : MinimalObstruction c k t S)
    (hb : Balanced c) (p : V → Sym2 L) (rep : LineRepresentation (colorGraph c k) S p)
    (C : Finset V) (hCS : C ⊆ S) (hC : (colorGraph c k).IsNClique r C) :
    Set.InjOn p (C : Set V) := by
  intro x hx z hz eq
  obtain ⟨y,hy,hxy⟩ := h.full_clique_external_neighbor C hCS hC x hx
  obtain ⟨hyS,hyC⟩ := mem_sdiff.mp hy
  have ne {u : V} (hu : u ∈ C) : y ≠ u := fun e => hyC (e ▸ hu)
  have hcommon := (rep.adj y hyS x (hCS hx) (ne hx)).mp hxy
  rw [eq] at hcommon
  exact exterior_clique_neighbor_unique c hb k C hC y hyC hx hz hxy
    ((rep.adj y hyS z (hCS hz) (ne hz)).mpr hcommon)

end Erdos617
