module

public import Wall133.Chung
public import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Independence

@[expose] public section

namespace Wall133

open SimpleGraph

variable {V : Type*}

/-- In a graph without a four-cycle, two distinct vertices have at most one common neighbor. -/
def NoFourCycle (G : SimpleGraph V) : Prop :=
  ∀ ⦃x y a b⦄, x ≠ y → G.Adj x a → G.Adj y a → G.Adj x b → G.Adj y b → a = b

theorem noFourCycle_iff (G : SimpleGraph V) :
    NoFourCycle G ↔ ¬ ∃ a b c d : V,
      a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a := by
  constructor
  · rintro h ⟨a,b,c,d,_,hac,_,_,hbd,_,hab,hbc,hcd,hda⟩
    exact hbd (h hac hab hbc.symm hda.symm hcd)
  · intro h x y a b hxy hxa hya hxb hyb
    by_contra hab
    exact h ⟨x, a, y, b, hxa.ne, hxy, hxb.ne, hya.ne.symm, hab, hyb.ne,
      hxa, hya.symm, hyb, hxb.symm⟩

variable [Fintype V]

/-- The independence number of a neighborhood is at most its cardinality. -/
theorem indepNeighborsCard_le_degree {G : SimpleGraph V} [DecidableRel G.Adj] (v : V) :
    G.indepNeighborsCard v ≤ G.degree v := by
  classical
  let H := G.induce (G.neighborSet v)
  obtain ⟨s, hs⟩ := exists_isNIndepSet_indepNum (G := H)
  calc
    G.indepNeighborsCard v = s.card := hs.card_eq.symm
    _ ≤ Fintype.card (G.neighborSet v) := Finset.card_le_univ _
    _ = _ := G.card_neighborSet_eq_degree v

/-- A lower bound on the average neighborhood independence number gives the same
lower bound on the average degree. -/
theorem sum_degree_ge_of_le_l [Nonempty V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {k : ℕ} (hk : (k : ℝ) ≤ l G) : k * Fintype.card V ≤ ∑ v, G.degree v := by
  have hsum : (∑ v : V, G.indepNeighbors v) ≤ ∑ v : V, (G.degree v : ℝ) := by
    apply Finset.sum_le_sum
    intro v _
    change (G.indepNeighborsCard v : ℝ) ≤ (G.degree v : ℝ)
    exact_mod_cast indepNeighborsCard_le_degree (G := G) v
  have hp : 0 < (Fintype.card V : ℝ) := by exact_mod_cast Fintype.card_pos
  have hk' := (le_div_iff₀ hp).mp hk
  exact_mod_cast hk'.trans hsum

variable [DecidableEq V]

omit [DecidableEq V] in
/-- From any vertex there is a geodesic at least as long as the radius. -/
theorem exists_geodesic_ge_radius (G : SimpleGraph V) (hc : G.Connected) (v : V) :
    ∃ w : V, ∃ p : G.Walk v w, p.length = G.dist v w ∧ G.radius.toNat ≤ p.length := by
  obtain ⟨w, hw⟩ := G.exists_edist_eq_eccent_of_finite v
  obtain ⟨p, _, hp⟩ := hc.exists_path_of_dist v w
  refine ⟨w, p, hp, hp ▸ ?_⟩
  exact ENat.toNat_le_toNat (hw ▸ G.radius_le_eccent) (edist_ne_top_iff_reachable.mpr (hc v w))

theorem radius_add_one_le_path (G : SimpleGraph V) (hc : G.Connected) :
    G.radius.toNat + 1 ≤ G.path := by
  obtain ⟨w,p,hp,hr⟩ := exists_geodesic_ge_radius G hc (Classical.choice hc.nonempty)
  have h := G.length_le_path_of_isInducedPath p.support (isInducedPath_support_of_length_eq_dist p hp)
  rw [Walk.length_support] at h
  omega

end Wall133
