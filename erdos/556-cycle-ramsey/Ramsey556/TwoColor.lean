import Ramsey556.OctetPair
import Ramsey556.Bipartite

namespace Ramsey556

/-- The other nonzero color when `k` is 1 or 2. -/
def otherNonzero (k : Fin 3) : Fin 3 := if k = 1 then 2 else 1

/-- An ordered pair of disjoint eight-vertex cliques in color `k`. -/
structure OctetCliques {n : Nat} (c : Coloring n) (k : Fin 3) where
  vertex : Fin 2 → Fin 8 → Fin n
  inj : ∀ ⦃a b i j⦄, vertex a i = vertex b j → a = b ∧ i = j
  inside : ∀ a i j, i ≠ j → c.edge (vertex a i) (vertex a j) = k

/-- The K₁₆ instance of the two-color critical-coloring classification.
See Nikiforov–Schelp, *Cycles and Stability*, §4.1, and Sanhueza-Matamala,
*Stability and Ramsey numbers for cycles and wheels*, Lemma 11 (journal version).
This proposition is an explicit input to the reduction below. -/
def TwoColorOctets16 : Prop :=
  ∀ c : Coloring 16, (∀ i j, i ≠ j → c.edge i j ≠ 0) → ¬ HasMonoC9 c →
    ∃ k : Fin 3, k ≠ 0 ∧ Nonempty (OctetCliques c k)

/-- On a two-colored K₁₆ avoiding C₉, every edge between the cliques, with
at most one exception, has the other color. -/
theorem OctetCliques.between {n : Nat} {c : Coloring n} {k : Fin 3}
    (S : OctetCliques c k) (hk : k ≠ 0) (free : ¬ HasMonoC9 c)
    (only : ∀ i j, c.edge (S.vertex 0 i) (S.vertex 1 j) ≠ 0) :
    ∃ u v : Fin 8, ∀ i j, (i,j) ≠ (u,v) →
      c.edge (S.vertex 0 i) (S.vertex 1 j) = otherNonzero k := by
  have unique {a b a' b' : Fin 8}
      (e : c.edge (S.vertex 0 a) (S.vertex 1 b) = k)
      (e' : c.edge (S.vertex 0 a') (S.vertex 1 b') = k) : (a,b) = (a',b') := by
    have disj (i j : Fin 8) : S.vertex 0 i ≠ S.vertex 1 j :=
      fun e => (by decide : (0 : Fin 2) ≠ 1) (S.inj e).1
    have inj (s : Fin 2) : ∀ ⦃i j⦄, S.vertex s i = S.vertex s j → i = j :=
      fun {_ _} e => (S.inj e).2
    apply Prod.ext
    · exact clique_cross_unique c k _ _ (inj 0) (inj 1) disj (S.inside 0) (S.inside 1) free e e'
    · apply clique_cross_unique c k _ _ (inj 1) (inj 0) (fun i j => (disj j i).symm)
        (S.inside 1) (S.inside 0) free
      · exact (c.symm _ _).trans e
      · exact (c.symm _ _).trans e'
  have pick : ∀ k x : Fin 3, k ≠ 0 → x ≠ 0 → x ≠ k → x = otherNonzero k := by decide
  by_cases ex : ∃ a b, c.edge (S.vertex 0 a) (S.vertex 1 b) = k
  · obtain ⟨a, b, e⟩ := ex
    exact ⟨a, b, fun i j h => pick _ _ hk (only i j) (fun f => h (unique f e))⟩
  · exact ⟨0, 0, fun i j _ => pick _ _ hk (only i j) (fun f => ex ⟨i,j,f⟩)⟩

/-- Transport the classification from its 16 labeled vertices to any chosen
two-colored set of 16 vertices of a larger coloring. -/
theorem octets_on_subset {n : Nat} (classify : TwoColorOctets16) (c : Coloring n)
    (v : Fin 16 → Fin n) (inj : ∀ ⦃i j⦄, v i = v j → i = j)
    (absent : ∀ i j, i ≠ j → c.edge (v i) (v j) ≠ 0) (free : ¬ HasMonoC9 c) :
    ∃ (k : Fin 3) (S : OctetCliques c k), k ≠ 0 ∧
      (∀ b i, ∃ j, S.vertex b i = v j) ∧
      ∃ u w : Fin 8, ∀ i j, (i,j) ≠ (u,w) →
        c.edge (S.vertex 0 i) (S.vertex 1 j) = otherNonzero k := by
  have hf := mt (HasMonoC9.of_induce (@inj)) free
  obtain ⟨k, hk, ⟨T⟩⟩ := classify _ absent hf
  let S : OctetCliques c k := {
    vertex := fun b i => v (T.vertex b i)
    inj := fun {_ _ _ _} e => T.inj (inj e)
    inside := T.inside
  }
  have diff (i j : Fin 8) : T.vertex 0 i ≠ T.vertex 1 j :=
    fun e => (by decide : (0 : Fin 2) ≠ 1) (T.inj e).1
  exact ⟨k, S, hk, fun b i => ⟨T.vertex b i, rfl⟩,
    T.between hk hf (fun i j => absent _ _ (diff i j))⟩

/-- The 16-vertex classification implies the usual two-color Ramsey bound
at 17. A seventeenth vertex would have to send seven edges of the absent color. -/
theorem twoColor17_of_octets (classify : TwoColorOctets16) (c : Coloring 17)
    (absent : ∀ i j, i ≠ j → c.edge i j ≠ 0) : HasMonoC9 c := by
  apply Classical.byContradiction
  intro free
  obtain ⟨k, S, hk, old, between⟩ := octets_on_subset classify c Fin.castSucc
    (fun {_ _} h => Fin.castSucc_inj.mp h)
    (fun _ _ h => absent _ _ (fun e => h (Fin.castSucc_inj.mp e))) free
  have away (b i) : S.vertex b i ≠ Fin.last 16 := by
    obtain ⟨j, hj⟩ := old b i
    rw [hj]
    exact Fin.ne_of_lt (Fin.castSucc_lt_last j)
  have colors : ∀ k : Fin 3, k ≠ 0 → otherNonzero k ≠ 0 ∧ k ≠ otherNonzero k := by decide
  obtain ⟨b, f, _, spokes⟩ := seven_spokes_of_octet_pair c (Fin.last 16) S.vertex k
    (otherNonzero k) hk ((colors k hk).1) ((colors k hk).2) (@S.inj) away S.inside between free
  exact absent _ _ (away b (f 0)).symm (spokes 0)

/-- A bipartite color in a C₉-free K₃₂ must split its vertices 16–16.
The labels returned here keep the absence of that color explicit in each half. -/
theorem balanced_halves_of_octets (classify : TwoColorOctets16) (c : Coloring 32)
    (free : ¬ HasMonoC9 c) (bip : IsBipartiteColor c 0) :
    ∃ u : Fin 2 → Fin 16 → Fin 32,
      (∀ ⦃a b i j⦄, u a i = u b j → a = b ∧ i = j) ∧
      ∀ a i j, i ≠ j → c.edge (u a i) (u a j) ≠ 0 := by
  obtain ⟨side, cut⟩ := bip
  let cell (b : Bool) := (List.finRange 32).filter (fun x => side x == b)
  have nodup (b : Bool) : (cell b).Nodup := (List.nodup_finRange 32).filter _
  have bound (b : Bool) : (cell b).length ≤ 16 := by
    apply Nat.le_of_not_gt
    intro enough
    let v (i : Fin 17) := (cell b)[i.val]'(by omega)
    have inj : ∀ ⦃i j⦄, v i = v j → i = j := fun {_ _} e =>
      Fin.ext ((nodup b).eq_of_getElem_eq _ _ e)
    have tag (i : Fin 17) : side (v i) = b := by
      have mem : v i ∈ cell b := List.getElem_mem ..
      simpa [cell] using mem
    apply free
    apply HasMonoC9.of_induce (@inj)
    apply twoColor17_of_octets classify (c.induce v)
    intro i j ne eq
    exact cut _ _ (fun e => ne (inj e)) eq ((tag i).trans (tag j).symm)
  have total : 32 = (cell true).length + (cell false).length := by
    simpa [cell, List.countP_eq_length_filter] using
      List.length_eq_countP_add_countP side (l := List.finRange 32)
  have size (b : Bool) : (cell b).length = 16 := by
    have := bound true
    have := bound false
    cases b <;> omega
  let bit (a : Fin 2) := decide (a = 1)
  let u (a : Fin 2) (i : Fin 16) := (cell (bit a))[i.val]'(by rw [size]; exact i.isLt)
  have tag (a i) : side (u a i) = bit a := by
    have mem : u a i ∈ cell (bit a) := List.getElem_mem ..
    simpa [cell] using mem
  have inj (a : Fin 2) : ∀ ⦃i j⦄, u a i = u a j → i = j :=
    fun {_ _} e => Fin.ext ((nodup (bit a)).eq_of_getElem_eq _ _ e)
  refine ⟨u, ?_, ?_⟩
  · intro a b i j e
    have bitInj : ∀ a b, bit a = bit b → a = b := by decide
    have eq := bitInj a b ((tag a i).symm.trans ((congrArg side e).trans (tag b j)))
    subst b
    exact ⟨rfl, inj a e⟩
  · intro a i j ne e
    exact cut _ _ (fun h => ne (inj a h)) e ((tag a i).trans (tag a j).symm)

end Ramsey556
