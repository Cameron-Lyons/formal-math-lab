import Ramsey556.ClassifiedHalves

namespace Ramsey556

/-- Derive the one-deletion case from the two-color K₁₆ classification. -/
theorem hasMonoC9_of_one_bipartite_on_32 (classify : TwoColorOctets16)
    (c : Coloring 33) (v : Fin 32 → Fin 33) (hv : ∀ ⦃i j⦄, v i = v j → i = j)
    (r : Fin 3) (bip : IsBipartiteColor (c.induce v) r) : HasMonoC9 c := by
  let swap (r x : Fin 3) : Fin 3 := if x = r then 0 else if x = 0 then r else x
  have perm : ∀ r i j, swap r i = swap r j → i = j := by decide
  let d := c.recolor (swap r)
  have bip₀ : IsBipartiteColor (d.induce v) 0 := by
    obtain ⟨side, cut⟩ := bip
    refine ⟨side, fun i j ne he => cut i j ne (perm r _ r ?_)⟩
    change swap r ((c.induce v).edge i j) = 0 at he
    rwa [show swap r r = 0 by simp [swap]]
  apply hasMonoC9_of_copy c id (swap r) (fun {_ _} e => e) (fun {_ _} => perm r _ _)
  change HasMonoC9 d
  apply Classical.byContradiction
  intro free
  have free₀ := mt (HasMonoC9.of_induce (c := d) (@hv)) free
  obtain ⟨u, hU, noRed⟩ := balanced_halves_of_octets classify _ free₀ bip₀
  obtain ⟨z, hz⟩ := missingVertex v
  have models (h : Fin 2) := octets_on_subset classify d (fun j => v (u h j))
    (fun {_ _} e => (hU (hv e)).2) (noRed h) free
  let k (h : Fin 2) := (models h).choose
  let S (h : Fin 2) := (models h).choose_spec.choose
  have data (h) := (models h).choose_spec.choose_spec
  let index (h a : Fin 2) (i : Fin 8) := ((data h).2.1 a i).choose
  have label (h a i) : (S h).vertex a i = v (u h (index h a i)) :=
    ((data h).2.1 a i).choose_spec
  apply free
  apply hasMonoC9_of_classifiedHalves d z
  refine { color := k, nonzero := fun h => (data h).1, vertex := fun h => (S h).vertex,
           inside := fun h => (S h).inside, between := fun h => (data h).2.2,
           inj := ?_, away := ?_, noZero := ?_ }
  · intro h g a b i j e
    have eq := hv ((label h a i).symm.trans (e.trans (label g b j)))
    obtain ⟨rfl, _⟩ := hU eq
    exact ⟨rfl, (S h).inj e⟩
  · intro h a i
    rw [label]
    exact hz _
  · intro h a b i j ne
    rw [label, label]
    apply noRed
    intro eq
    have e : (S h).vertex a i = (S h).vertex b j := by rw [label, label, eq]
    obtain ⟨ha, hi⟩ := (S h).inj e
    exact ne (Prod.ext ha hi)

/-- Some color becomes bipartite on some induced 32-vertex subgraph. -/
def OneBipartiteAfterDeletion (c : Coloring 33) : Prop :=
  ∃ v : Fin 32 → Fin 33, (∀ ⦃i j⦄, v i = v j → i = j) ∧
    ∃ r : Fin 3, IsBipartiteColor (c.induce v) r

/-- Using the 16-vertex two-color classification, the remaining colorings have
all three color graphs nonbipartite after every single-vertex deletion. -/
theorem k33_iff_all_three_survive (classify : TwoColorOctets16) :
    K33Claim ↔ ∀ c : Coloring 33, (¬ OneBipartiteAfterDeletion c) → HasMonoC9 c := by
  refine ⟨fun h c _ => h c, ?_⟩
  intro h c
  by_cases hit : OneBipartiteAfterDeletion c
  · obtain ⟨v, hv, r, hr⟩ := hit
    exact hasMonoC9_of_one_bipartite_on_32 classify c v hv r hr
  · exact h c hit

end Ramsey556
