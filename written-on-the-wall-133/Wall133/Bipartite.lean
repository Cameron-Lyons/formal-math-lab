import Wall133.Basic
import Mathlib.Combinatorics.SimpleGraph.Bipartite

namespace Wall133
open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- An induced path with indices counted from its active endpoint. -/
structure Chain (G : SimpleGraph V) (n : ℕ) where
  vertex : ℕ → V
  inj : ∀ {i j}, i ≤ n → j ≤ n → vertex i = vertex j → i = j
  edges : ∀ {i j}, i ≤ n → j ≤ n →
    (G.Adj (vertex i) (vertex j) ↔ i + 1 = j ∨ j + 1 = i)

private def Chain.start (v : V) : Chain G 0 where
  vertex := fun _ => v
  inj := by omega
  edges := by
    intro i j hi hj
    have : i = 0 := by omega
    have : j = 0 := by omega
    subst i; subst j
    simp

def Chain.prepend {n : ℕ} (P : Chain G n) (z : V)
    (hz : G.Adj z (P.vertex 0))
    (hfresh : ∀ i ≤ n, z ≠ P.vertex i)
    (hclean : ∀ i ≤ n, i ≠ 0 → ¬ G.Adj z (P.vertex i)) : Chain G (n+1) where
  vertex := fun i => match i with
    | 0 => z
    | i+1 => P.vertex i
  inj := by
    intro i j hi hj
    cases i <;> cases j
    · simp
    · intro h; exact (hfresh _ (by omega) h).elim
    · intro h; exact (hfresh _ (by omega) h.symm).elim
    · intro h; exact congrArg Nat.succ (P.inj (by omega) (by omega) h)
  edges := by
    intro i j hi hj
    cases i with
    | zero =>
      cases j with
      | zero => simp
      | succ j =>
        change G.Adj z (P.vertex j) ↔ 0+1 = j+1 ∨ j+1+1 = 0
        by_cases h : j = 0
        · subst j; simp [hz]
        · simp [hclean j (by omega) h, h]
    | succ i =>
      cases j with
      | zero =>
        change G.Adj (P.vertex i) z ↔ i+1+1 = 0 ∨ 0+1 = i+1
        rw [G.adj_comm]
        by_cases h : i = 0
        · subst i; simp [hz]
        · simp [hclean i (by omega) h, h]
      | succ j =>
        change G.Adj (P.vertex i) (P.vertex j) ↔ i+1+1 = j+1 ∨ j+1+1 = i+1
        simpa only [Nat.succ.injEq] using P.edges (i := i) (j := j) (by omega) (by omega)

theorem Chain.color_val {n : ℕ} (P : Chain G n) (c : G.Coloring (Fin 2))
    (i : ℕ) (hi : i ≤ n) :
      (c (P.vertex i)).val = ((c (P.vertex 0)).val + i) % 2 := by
    induction i with
    | zero => have := (c (P.vertex 0)).isLt; omega
    | succ k ih =>
      have hprev := ih (by omega)
      have hadj := (P.edges (i := k) (j := k+1) (by omega) hi).2 (Or.inl rfl)
      have hdiff := (Fin.val_ne_of_ne (c.valid hadj))
      have := (c (P.vertex k)).isLt
      have := (c (P.vertex (k+1))).isLt
      omega
theorem Chain.even_of_common {n : ℕ} (P : Chain G n) (c : G.Coloring (Fin 2))
    {j : ℕ} (hj : j ≤ n) {z : V} (hz : G.Adj (P.vertex 0) z)
    (h : G.Adj (P.vertex j) z) : j % 2 = 0 := by
  have ha := Fin.val_ne_of_ne (c.valid hz)
  have hb := Fin.val_ne_of_ne (c.valid h)
  have h₀ := (c (P.vertex 0)).isLt
  have hj' := (c (P.vertex j)).isLt
  have hz' := (c z).isLt
  have := P.color_val c j hj
  omega

theorem Chain.extend [Fintype V] [DecidableRel G.Adj] {n : ℕ}
    (P : Chain G n) (c : G.Coloring (Fin 2)) (h4 : NoFourCycle G)
    (hd : 2 ≤ G.degree (P.vertex 0)) (hn : n/2 < G.degree (P.vertex 0)) :
    ∃ Q : Chain G (n+1), Q.vertex (n+1) = P.vertex n := by
  classical
  let neighbors := G.neighborFinset (P.vertex 0)
  have hcard : neighbors.card = G.degree (P.vertex 0) := rfl
  have chooseNext : ∃ z ∈ neighbors,
      (∀ i ≤ n, z ≠ P.vertex i) ∧
      (∀ i ≤ n, i ≠ 0 → ¬ G.Adj z (P.vertex i)) := by
    by_cases hsmall : n < 2
    · have hex : ∃ z ∈ neighbors, z ≠ P.vertex 1 := by
        by_contra! h
        have hsub : neighbors ⊆ {P.vertex 1} :=
          fun z hz => Finset.mem_singleton.mpr (h z hz)
        have := Finset.card_le_card hsub
        simp at this
        omega
      obtain ⟨z, hz, hdiff⟩ := hex
      have ha : G.Adj (P.vertex 0) z := (G.mem_neighborFinset _ _).mp hz
      refine ⟨z, hz, ?_, ?_⟩
      · intro i hi; rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
        · exact ha.ne.symm
        · exact hdiff
      · intro i hi hnz hz'
        have := P.even_of_common c hi ha hz'.symm
        omega
    · by_contra h
      have blocker (z : ↥neighbors) : ∃ j, j ≤ n ∧ j ≠ 0 ∧ j % 2 = 0 ∧
          G.Adj (P.vertex j) z := by
        have hz : G.Adj (P.vertex 0) z := (G.mem_neighborFinset _ _).mp z.property
        by_cases hc : ∃ j ≤ n, j ≠ 0 ∧ G.Adj (P.vertex j) z
        · obtain ⟨j, hj, hp, ha⟩ := hc
          exact ⟨j, hj, hp, P.even_of_common c hj hz ha, ha⟩
        · have hclean : ∀ j ≤ n, j ≠ 0 → ¬G.Adj z (P.vertex j) :=
            fun j hj hp ha => hc ⟨j, hj, hp, ha.symm⟩
          have hrep : ∃ i ≤ n, (z : V) = P.vertex i := by
            by_contra! hfresh
            exact h ⟨z, z.property, hfresh, hclean⟩
          obtain ⟨i, hi, heq⟩ := hrep
          rw [heq] at hz ⊢
          have := (P.edges (by omega) hi).1 hz
          have : i = 1 := by omega
          subst i
          exact ⟨2, by omega, by decide, by decide, (P.edges (by omega) hi).2 (by decide)⟩
      choose idx hidx using blocker
      let f (z : ↥neighbors) : Fin (n/2) := ⟨(idx z)/2-1, by
        have := (hidx z).1
        have := (hidx z).2.1
        have := (hidx z).2.2.1
        omega⟩
      have hfinj : Function.Injective f := by
        intro a b hab
        have heq := congrArg Fin.val hab
        change (idx a)/2-1 = (idx b)/2-1 at heq
        have ha := hidx a
        have hb := hidx b
        have hi : idx a = idx b := by omega
        apply Subtype.ext
        apply h4 (x := P.vertex 0) (y := P.vertex (idx a))
        · intro he; have := P.inj (Nat.zero_le _) ha.1 he; omega
        · exact (G.mem_neighborFinset _ _).mp a.property
        · exact ha.2.2.2
        · exact (G.mem_neighborFinset _ _).mp b.property
        · rw [hi]; exact hb.2.2.2
      have hbound := Fintype.card_le_of_injective f hfinj
      simp only [Fintype.card_coe, Fintype.card_fin] at hbound
      omega
  obtain ⟨z, hz, hfresh, hclean⟩ := chooseNext
  exact ⟨P.prepend z ((G.mem_neighborFinset _ _).mp hz).symm hfresh hclean, rfl⟩

def Chain.reverse {n : ℕ} (P : Chain G n) : Chain G n where
  vertex i := P.vertex (n-i)
  inj := by
    intro i j hi hj h
    have := P.inj (Nat.sub_le n i) (Nat.sub_le n j) h
    omega
  edges := by
    intro i j hi hj
    rw [P.edges (Nat.sub_le n i) (Nat.sub_le n j)]
    omega

theorem exists_chain_ending_at [Fintype V] [DecidableRel G.Adj] (v : V)
    (c : G.Coloring (Fin 2)) (h4 : NoFourCycle G) {d : ℕ}
    (hd : 2 ≤ d) (hmin : ∀ x, d ≤ G.degree x) (n : ℕ) (hn : n ≤ 2*d) :
    ∃ P : Chain G n, P.vertex n = v := by
  induction n with
  | zero => exact ⟨Chain.start v, rfl⟩
  | succ n ih =>
    obtain ⟨P, hP⟩ := ih (by omega)
    have hdeg := hmin (P.vertex 0)
    obtain ⟨Q, hQ⟩ := P.extend c h4 (by omega) (by omega)
    exact ⟨Q, hQ.trans hP⟩

theorem Chain.length_le [Fintype V] [DecidableEq V] {n : ℕ}
    (P : Chain G n) : n+1 ≤ path G := by
  let f (i : Fin (n+1)) := P.vertex i.val
  let vertices := List.ofFn f
  have hlen : vertices.length = n+1 := List.length_ofFn
  rw [← hlen]
  apply G.length_le_path_of_isInducedPath
  refine ⟨List.nodup_ofFn_ofInjective (fun i j h => Fin.ext (P.inj (by omega) (by omega) h)), ?_⟩
  intro i j
  change G.Adj ((List.ofFn f)[i.val]) ((List.ofFn f)[j.val]) ↔ _
  simp only [List.getElem_ofFn]
  exact P.edges (by have := i.isLt; omega) (by have := j.isLt; omega)

/-- A bipartite graph with no four-cycle and minimum degree at least `d ≥ 2`
contains an induced path on `2 * d + 1` vertices. -/
theorem two_mul_minDegree_add_one_le_path [Fintype V] [DecidableEq V]
    [Nonempty V] [DecidableRel G.Adj] (hb : G.IsBipartite) (h4 : NoFourCycle G)
    {d : ℕ} (hd : 2 ≤ d) (hmin : ∀ x, d ≤ G.degree x) : 2*d+1 ≤ path G := by
  obtain ⟨c⟩ := hb
  obtain ⟨P, _⟩ := exists_chain_ending_at (Classical.arbitrary V) c h4 hd hmin (2*d) le_rfl
  exact P.length_le

/-- Keeping one high-degree vertex at the other end of the path allows
one extra extension after reversing it. -/
theorem two_mul_minDegree_add_two_le_path [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (hb : G.IsBipartite) (h4 : NoFourCycle G)
    {d : ℕ} (hd : 2 ≤ d) (hmin : ∀ x, d ≤ G.degree x) (v : V) (hv : d < G.degree v) :
    2*d+2 ≤ path G := by
  obtain ⟨c⟩ := hb
  obtain ⟨P, hP⟩ := exists_chain_ending_at v c h4 hd hmin (2*d) le_rfl
  have hstart : P.reverse.vertex 0 = v := by simpa [Chain.reverse] using hP
  obtain ⟨Q, _⟩ := P.reverse.extend c h4 (by rw [hstart]; omega) (by rw [hstart]; omega)
  exact Q.length_le

/-- If one bipartition class has strictly higher minimum degree, both ends
of an even-length path starting in that class allow an extra extension. -/
theorem two_mul_minDegree_add_three_le_path [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (c : G.Coloring (Fin 2)) (h4 : NoFourCycle G)
    {d : ℕ} (hd : 2 ≤ d) (hmin : ∀ x, d ≤ G.degree x) (v : V)
    (hhigh : ∀ x, c x = c v → d < G.degree x) :
    2*d+3 ≤ path G := by
  obtain ⟨P, hP⟩ := exists_chain_ending_at v c h4 hd hmin (2*d) le_rfl
  have hc : c (P.vertex 0) = c v := by
    have hval := P.color_val c (2*d) le_rfl
    rw [hP] at hval
    apply Fin.ext
    have := (c (P.vertex 0)).isLt
    omega
  have hfirst := hhigh _ hc
  obtain ⟨Q, hQ⟩ := P.extend c h4 (by omega) (by omega)
  have hstart : Q.reverse.vertex 0 = v := by simpa [Chain.reverse, hP] using hQ
  have hlast := hhigh v rfl
  obtain ⟨R, _⟩ := Q.reverse.extend c h4 (by rw [hstart]; omega) (by rw [hstart]; omega)
  exact R.length_le

/-- Combining the endpoint argument with Chung's radius bound gives a
radius-plus-minimum-degree bound, with no restriction on the radius. -/
theorem radius_add_minDegree_le_path_of_bipartite [Fintype V] [DecidableEq V]
    [Nonempty V] [DecidableRel G.Adj] (hc : G.Connected)
    (hb : G.IsBipartite) (h4 : NoFourCycle G) {d : ℕ} (hmin : ∀ x, d ≤ G.degree x) :
    G.radius.toNat + d ≤ path G := by
  by_cases hd : 2 ≤ d
  · have hp := two_mul_minDegree_add_one_le_path hb h4 hd hmin
    have hr := chung_bound_nat G hc
    omega
  · have hp := radius_add_one_le_path G hc
    omega

/-- The unrounded neighborhood average is bounded above by any upper bound on
the vertex degrees. -/
theorem averageIndepNeighbors_le_of_degree_le [Fintype V] [Nonempty V]
    [DecidableRel G.Adj] {d : ℕ} (hmax : ∀ x, G.degree x ≤ d) : l G ≤ d := by
  classical
  have hsum : (∑ v : V, G.indepNeighbors v) ≤ ∑ _v : V, (d : ℝ) := by
    apply Finset.sum_le_sum
    intro v _
    change (G.indepNeighborsCard v : ℝ) ≤ (d : ℝ)
    exact_mod_cast (indepNeighborsCard_le_degree (G := G) v).trans (hmax v)
  unfold l averageIndepNeighbors
  apply (div_le_iff₀ (by exact_mod_cast Fintype.card_pos : 0 < (Fintype.card V : ℝ))).2
  simpa [mul_comm] using hsum

/-- WOWII 133 on all connected regular bipartite graphs without a four-cycle,
even with the unrounded average appearing in the upstream Lean statement. -/
theorem radius_add_l_le_path_of_regular_bipartite [Fintype V] [DecidableEq V]
    [Nonempty V] [DecidableRel G.Adj] (hc : G.Connected)
    (hb : G.IsBipartite) (h4 : NoFourCycle G) {d : ℕ} (hreg : G.IsRegularOfDegree d) :
    (G.radius.toNat : ℝ) + l G ≤ path G := by
  have hpath := radius_add_minDegree_le_path_of_bipartite hc hb h4
    (fun x => (hreg.degree_eq x).ge)
  have hav := averageIndepNeighbors_le_of_degree_le (fun x => (hreg.degree_eq x).le)
  calc
    _ ≤ (G.radius.toNat : ℝ) + d := by gcongr
    _ ≤ path G := by exact_mod_cast hpath

end Wall133
