import Ramsey556.EdgeBound
import Ramsey556.Dense16Deletion

namespace Ramsey556.Cert16

/-- A catalog records all simple, dense color graphs up to relabeling. The
finite certificates establish these three properties, while the ambient
coloring argument uses this interface to transfer back to unordered edges. -/
structure CatalogProof (catalog : Nat → List Nat) : Prop where
  start : 0 ∈ catalog 1
  step : ∀ {n g m : Nat}, 1 ≤ n → n < 16 → g ∈ catalog n → m < 2^n →
    threshold (n+1) ≤ edgeCount n g + popcount n m → Safe n g m →
    ∃ h ∈ catalog (n+1), ExtendsTo n g m h
  final : ∀ {g}, g ∈ catalog 16 → ∃ side : Fin 16 → Bool,
    ∀ i j, edge g i.val j.val = true → side i ≠ side j

private theorem range_as_fin (n : Nat) : (List.finRange n).map Fin.val = List.range n := by
  apply List.ext_getElem <;> simp

private theorem mask_exists {n : Nat} (p : Fin n → Bool) :
    ∃ m, m < 2 ^ n ∧ ∀ i : Fin n, Nat.testBit m i.val = p i := by
  let bits := BitVec.ofBoolListLE (List.ofFn p)
  refine ⟨bits.toNat, by simpa [bits] using bits.isLt, ?_⟩
  intro i
  change bits.getLsbD i.val = _
  rw [show bits.getLsbD i.val = (List.ofFn p).getD i.val false by exact BitVec.getLsbD_ofBoolListLE]
  simp [List.getD, i.isLt]

/-- A relabeling of a simple color graph with its diagonal removed. The vertex
map points from the catalog representation into the original coloring. -/
structure Model {n : Nat} (g : Nat) (c : Coloring n) (k : Fin 3) where
  vertex : Fin n → Fin n
  inj : ∀ ⦃i j⦄, vertex i = vertex j → i = j
  agree : ∀ i j, edge g i.val j.val =
    decide (vertex i ≠ vertex j ∧ c.edge (vertex i) (vertex j) = k)

private theorem append_inj {n : Nat} (f : Fin n → Fin (n+1)) (z : Fin (n+1))
    (inj : ∀ ⦃i j⦄, f i = f j → i = j) (away : ∀ i, f i ≠ z) :
    ∀ ⦃i j : Fin (n+1)⦄, Fin.lastCases (motive := fun _ => Fin (n+1)) z f i = Fin.lastCases (motive := fun _ => Fin (n+1)) z f j → i = j := by
  intro i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp only [Fin.lastCases_last, Fin.lastCases_castSucc, Fin.castSucc_inj]
  · exact id
  · exact fun e => (away _ e.symm).elim
  · exact fun e => (away _ e).elim
  · exact fun e => inj e

private theorem safe_new_edges {n g m : Nat} (c : Coloring (n+1)) (k : Fin 3)
    (f : Fin n → Fin (n+1)) (z : Fin (n+1))
    (inj : ∀ ⦃i j⦄, f i = f j → i = j) (away : ∀ i, f i ≠ z)
    (old : ∀ i j, edge g i.val j.val = decide (f i ≠ f j ∧ c.edge (f i) (f j) = k))
    (bits : ∀ i : Fin n, m.testBit i.val = decide (c.edge z (f i) = k))
    (free : ¬ HasC9In c k) : Safe n g m := by
  intro p hi edges hfirst hlast
  apply free
  apply closeC9InThrough c k (fun i => f (p i)) z
      (fun {_ _} e => hi (inj e)) (fun i => away _) _ ?_ ?_
  · intro i h
    let j : Fin 7 := ⟨i.val, by omega⟩
    have e := edges j
    rw [old] at e
    exact (of_decide_eq_true e).2
  · simpa only [bits, decide_eq_true_eq] using hfirst
  · simpa only [bits, decide_eq_true_eq] using hlast

private theorem model_of_extension {n g m h : Nat} {c : Coloring (n+1)} {k : Fin 3}
    (f : Fin n → Fin (n+1)) (z : Fin (n+1))
    (inj : ∀ ⦃i j⦄, f i = f j → i = j) (away : ∀ i, f i ≠ z)
    (old : ∀ i j, edge g i.val j.val = decide (f i ≠ f j ∧ c.edge (f i) (f j) = k))
    (bits : ∀ i : Fin n, m.testBit i.val = decide (c.edge z (f i) = k))
    (next : ExtendsTo n g m h) : Nonempty (Model h c k) := by
  let v : Fin (n+1) → Fin (n+1) := Fin.lastCases z f
  have vi := @append_inj n f z inj away
  have edges (i j : Fin (n+1)) :
      extendEdge n g m i.val j.val = decide (v i ≠ v j ∧ c.edge (v i) (v j) = k) := by
    by_cases eq : i = j
    · subst j; simp [extendEdge]
    · have neq : i.val ≠ j.val := fun he => eq (Fin.ext he)
      have vne : v i ≠ v j := fun he => eq (vi he)
      induction i using Fin.lastCases <;> induction j using Fin.lastCases
      · exact (eq rfl).elim
      · rename_i j
        simp [extendEdge, show n ≠ j.val by omega, v, bits, (away j).symm]
      · rename_i i
        have ineq : i.val ≠ n := by omega
        simp [extendEdge, ineq, v, bits, away, c.symm z]
      · rename_i i j
        have ineq : i.val ≠ n := by omega
        have jneq : j.val ≠ n := by omega
        have ij : i.val ≠ j.val := neq
        simp [extendEdge, ij, ineq, jneq, v, old]
  obtain ⟨perm, hi, he⟩ := next
  obtain ⟨inv, right, _⟩ := inverse_exists perm hi
  refine ⟨⟨fun i => v (inv i), ?_, ?_⟩⟩
  · intro i j eq
    have e := congrArg perm (vi eq)
    simpa only [right] using e
  · intro i j
    simpa only [right] using (he (inv i) (inv j)).trans (edges (inv i) (inv j))

/-- The popcount of the new adjacency word counts neighbors of the omitted
vertex. This also accounts for a relabeling of the old vertices. -/
private theorem count_new_edges {n m : Nat} (c : Coloring (n+1)) (k : Fin 3)
    (f : Fin n → Fin (n+1)) (z : Fin (n+1))
    (inj : ∀ ⦃i j⦄, f i = f j → i = j) (away : ∀ i, f i ≠ z)
    (bits : ∀ i : Fin n, m.testBit i.val = decide (c.edge z (f i) = k)) :
    popcount n m = (List.finRange (n+1)).countP (fun a => decide (z ≠ a ∧ c.edge z a = k)) := by
  let p (a : Fin (n+1)) := decide (z ≠ a ∧ c.edge z a = k)
  let v : Fin (n+1) → Fin (n+1) := Fin.lastCases z f
  have eq := (list_permutation v (append_inj f z inj away)).countP_eq p
  change popcount n m = (List.finRange (n+1)).countP p
  rw [← eq]
  unfold popcount
  rw [← List.countP_eq_length_filter, ← range_as_fin n]
  simp only [List.countP_map, List.finRange_succ_last, List.countP_append, List.countP_cons,
    List.countP_nil, Function.comp_def, v, Fin.lastCases_castSucc, Fin.lastCases_last]
  have miss : p z = false := by simp [p]
  rw [miss]
  simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
  apply List.countP_congr
  intro a _
  simp [p, bits, (away a).symm]

/-- The lower edge thresholds are closed under minimum-degree deletion.
Use the ratio inequality to avoid rounding in the combinatorial induction. -/
private theorem deletion_threshold {n e d : Nat} (hn : 1 ≤ n) (hn' : n < 16)
    (many : threshold (n+1) ≤ e) (avg : (n+1)*d ≤ 2*e) :
    threshold n ≤ e-d := by
  have small : n=1 ∨ n=2 ∨ n=3 ∨ n=4 ∨ n=5 ∨ n=6 ∨ n=7 ∨
      n=8 ∨ n=9 ∨ n=10 ∨ n=11 ∨ n=12 ∨ n=13 ∨ n=14 ∨ n=15 := by omega
  rcases small with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst n <;> simp [threshold] at * <;> omega

/-- Inductively identify the simple graph of one color with a checked catalog
member. A minimum-degree deletion always leaves a graph in the preceding
density range; a seven-edge conflict rules out its proposed extension. -/
theorem model_exists {catalog : Nat → List Nat} (cert : CatalogProof catalog) (n : Nat) :
    ∀ (c : Coloring n) (k : Fin 3), 1 ≤ n → n ≤ 16 →
      threshold n ≤ colorEdgeCount c k → (¬ HasC9In c k) →
      ∃ g ∈ catalog n, Nonempty (Model g c k) := by
  induction n with
  | zero => intro c k hn; omega
  | succ n ih =>
    intro c k hn top many free
    by_cases hzero : n = 0
    · subst n
      refine ⟨0, cert.start, ⟨⟨id, fun {_ _} h => h, ?_⟩⟩⟩
      intro i j
      have eq : i = j := Fin.ext (by omega)
      subst j
      simp [edge]
    obtain ⟨z, remove, inject, missed, _, deleted, average, _⟩ := delete_min_degree c k
    let d := c.induce remove
    have cap : threshold n ≤ colorEdgeCount d k := by
      have next := deletion_threshold (by omega : 1 ≤ n) (by omega : n < 16) many average
      rw [deleted, Nat.add_sub_cancel] at next
      exact next
    have free' : ¬ HasC9In d k := by
      rintro ⟨v, hi, he⟩
      exact free ⟨fun i => remove (v i), fun {_ _} h => hi (inject h), he⟩
    obtain ⟨g, hg, ⟨S⟩⟩ := ih d k (by omega) (by omega) cap free'
    let old (i : Fin n) := remove (S.vertex i)
    have hi : ∀ ⦃i j⦄, old i = old j → i = j := fun {_ _} h => S.inj (inject h)
    have away (i) : old i ≠ z := missed _
    have oldEdges (i j : Fin n) : edge g i.val j.val = decide (old i ≠ old j ∧ c.edge (old i) (old j) = k) := by
      have iff : old i = old j ↔ S.vertex i = S.vertex j := ⟨fun e => inject e, congrArg remove⟩
      simpa only [ne_eq, iff, old, d, Coloring.induce] using S.agree i j
    obtain ⟨m, hm, bits⟩ := mask_exists (fun i : Fin n => decide (c.edge z (old i) = k))
    have size : edgeCount n g = colorEdgeCount d k := by
      rw [← colorEdgeCount_relabel d k S.vertex (@S.inj)]
      apply cert16_count_eq
      intro i j
      have iff : S.vertex i = S.vertex j ↔ i = j := ⟨fun e => S.inj e, congrArg S.vertex⟩
      rw [S.agree]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq, Coloring.induce, ne_eq, iff]
      exact decide_eq_true_iff.symm
    have pop : popcount n m = colorDegree c k z := count_new_edges c k old z hi away bits
    obtain ⟨H, hH, next⟩ := cert.step (by omega : 1≤n) (by omega) hg hm
      (by rw [size, pop]; exact deleted ▸ many) (safe_new_edges c k old z hi away oldEdges bits free)
    exact ⟨H, hH, model_of_extension old z hi away oldEdges bits next⟩

/-- A complete checked catalog with bipartite representatives at order 16
proves the single-color edge bound, including all vertex relabelings and all
values on the diagonal of the given coloring. -/
theorem denseC9Free16Bipartite_of_catalog {catalog : Nat → List Nat} (cert : CatalogProof catalog)
    : DenseC9Free16Bipartite := by
  intro c k many free
  have large : threshold 16 ≤ colorEdgeCount c k := by
    change 60 ≤ colorEdgeCount c k
    rw [colorEdgeCount16_eq]
    exact many
  obtain ⟨g, hg, ⟨S⟩⟩ := model_exists cert 16 c k (by decide) (by decide) large free
  obtain ⟨side, bip⟩ := cert.final hg
  obtain ⟨inv, right, _⟩ := inverse_exists S.vertex (@S.inj)
  refine ⟨fun v => side (inv v), ?_⟩
  intro u v ne he
  apply bip
  rw [S.agree, right, right]
  simp [ne, he]

end Ramsey556.Cert16
