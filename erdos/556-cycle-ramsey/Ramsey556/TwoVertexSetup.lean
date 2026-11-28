import Ramsey556.TwoVertexFrame

namespace Ramsey556

/-- One red-independent set of size 16 yields two supporting octets for
all seventeen exterior vertices using the two-color classification. -/
theorem supportedOctets_of_independent (classify : TwoColorOctets16) {c : Coloring 33}
    (free : ¬ HasMonoC9 c) (v : Fin 16 → Fin 33) (inj : ∀ ⦃i j⦄, v i = v j → i = j)
    (absent : ∀ i j, i ≠ j → c.edge (v i) (v j) ≠ 0) : Nonempty (SupportedOctets c) := by
  obtain ⟨k,A,hk,old,between⟩ := octets_on_subset classify c v (@inj) absent free
  obtain ⟨w,wi,disj⟩ := outside_vertices (b := 17) (by decide) v
  have away (s i j) : A.vertex s i ≠ w j := by
    obtain ⟨u,hu⟩ := old s i
    rw [hu]
    exact disj _ _
  have colors : ∀ k : Fin 3, k ≠ 0 → otherNonzero k ≠ 0 ∧ k ≠ otherNonzero k := by decide
  have side (j : Fin 17) := all_but_one_spokes_of_octet_pair c (w j) A.vertex k (otherNonzero k)
    hk ((colors k hk).1) ((colors k hk).2) (@A.inj) (fun s i => away s i j) A.inside between free
  refine ⟨{ anchor := A.vertex, outer := w, tag := fun j => (side j).choose, anchorInj := @A.inj,
            outerInj := @wi, disjoint := away, supports := fun j => (side j).choose_spec,
            independent := ?_ }⟩
  intro s t i j ne
  obtain ⟨p,hp⟩ := old s i
  obtain ⟨q,hq⟩ := old t j
  rw [hp,hq]
  apply absent
  intro eq
  have e := A.inj (hp.trans ((congrArg v eq).trans hq.symm))
  exact ne (Prod.ext e.1 e.2)

/-- Two deletions leave 31 vertices. Either side of size at least 16
in a bipartition supplies an independent 16-set in that color. -/
theorem independent16_of_bipartite_on_31 (c : Coloring 33) (v : Fin 31 → Fin 33)
    (inj : ∀ ⦃i j⦄, v i = v j → i = j) (r : Fin 3) (bip : IsBipartiteColor (c.induce v) r) :
    ∃ u : Fin 16 → Fin 33, (∀ ⦃i j⦄, u i = u j → i = j) ∧
      ∀ i j, i ≠ j → c.edge (u i) (u j) ≠ r := by
  obtain ⟨u, ui, absent⟩ := bip.independent_set (m := 15) (by decide)
  exact ⟨v ∘ u, Function.Injective.comp (@inj) ui, absent⟩

end Ramsey556
