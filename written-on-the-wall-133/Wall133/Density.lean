import Wall133.Basic
import Mathlib.Combinatorics.SimpleGraph.Bipartite

namespace Wall133
open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

def degreeOn (s : Finset V) (v : V) : ℕ := (s.filter (G.Adj v)).card

omit [DecidableEq V] in
theorem degreeOn_univ (v : V) : degreeOn G Finset.univ v = G.degree v := by
  rw [degreeOn, ← G.card_neighborFinset_eq_degree]
  congr 1
  ext w
  simp

omit [Fintype V] [DecidableEq V] in
theorem degreeOn_induce (s : Finset V) (v : s) :
    degreeOn G s v = (G.induce (s : Set V)).degree v := by
  rw [degreeOn, ← SimpleGraph.card_neighborSet_eq_degree, ← Fintype.card_coe]
  apply Fintype.card_congr
  exact
    { toFun := fun w => ⟨⟨w.val, (Finset.mem_filter.mp w.property).1⟩,
          (Finset.mem_filter.mp w.property).2⟩
      invFun := fun w => ⟨w.val.val, Finset.mem_filter.mpr ⟨w.val.property, w.property⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

def totalOn (s : Finset V) := ∑ v ∈ s, degreeOn G s v

omit [Fintype V] in
theorem totalOn_insert {s : Finset V} {u : V} (hu : u ∉ s) :
    totalOn G (insert u s) = totalOn G s + 2 * degreeOn G s u := by
  classical
  have deg (v : V) : degreeOn G (insert u s) v =
      degreeOn G s v + if G.Adj v u then 1 else 0 := by
    by_cases h : G.Adj v u
    · simp [degreeOn, Finset.filter_insert, h, hu]
    · simp [degreeOn, Finset.filter_insert, h]
  have count : (∑ v ∈ s, if G.Adj v u then 1 else 0) = degreeOn G s u := by
    simp [degreeOn, G.adj_comm u, Finset.sum_boole]
  simp only [totalOn, Finset.sum_insert hu, deg, Finset.sum_add_distrib, count,
    show ¬ G.Adj u u from G.irrefl, if_false, Nat.add_zero]
  omega

/-- Removing one vertex subtracts twice its degree from the degree sum. -/
theorem sum_degree_erase_vertex (w : V) :
    (∑ v, G.degree v) =
      (∑ u : (Finset.univ.erase w), (G.induce (Finset.univ.erase w : Finset V)).degree u) +
      2*G.degree w := by
  classical
  let S := Finset.univ.erase w
  have his : insert w S = Finset.univ := Finset.insert_erase (Finset.mem_univ w)
  have ht := totalOn_insert G (s := S) (u := w) (Finset.notMem_erase _ _)
  rw [his] at ht
  have hw : degreeOn G S w = G.degree w := by
    rw [← degreeOn_univ G, ← his]
    simp [degreeOn, Finset.filter_insert]
  have he : totalOn G S = ∑ u : S, (G.induce (S : Set V)).degree u := by
    rw [totalOn, ← Finset.sum_attach]
    exact Finset.sum_congr rfl (fun u _ => degreeOn_induce G S u)
  rw [he,hw] at ht
  simpa only [totalOn, degreeOn_univ] using ht

omit [Fintype V] in
private theorem core_from_set (f : V → ℕ) (s : Finset V) (hs : s.Nonempty)
    (h : 2 * (∑ x ∈ s, f x) ≤ totalOn G s)
    (hstrict : (∀ x, 0 < f x) ∨ 2 * (∑ x ∈ s, f x) < totalOn G s) :
    ∃ S : Finset V, S.Nonempty ∧ (∀ v : S, f v < degreeOn G S v) ∧
      2 * (∑ v ∈ S, f v) ≤ totalOn G S := by
  classical
  by_cases hall : ∀ v : s, f v < degreeOn G s v
  · exact ⟨s, hs, hall, h⟩
  push Not at hall
  obtain ⟨x, hx⟩ := hall
  obtain ⟨x, hxs⟩ := x
  change degreeOn G s x ≤ f x at hx
  let t := s.erase x
  have ht : (x : V) ∉ t := Finset.notMem_erase _ _
  have hre : insert (x : V) t = s := Finset.insert_erase hxs
  have htotal := totalOn_insert G ht
  rw [hre] at htotal
  have hsum : (∑ u ∈ s, f u) = f x + ∑ u ∈ t, f u := by
    rw [← hre, Finset.sum_insert ht]
  have hdx : degreeOn G s x = degreeOn G t x := by
    rw [← hre]
    simp [degreeOn, Finset.filter_insert]
  have htstrict : (∀ z, 0 < f z) ∨ 2 * (∑ u ∈ t, f u) < totalOn G t := by
    rcases hstrict with hpos | h'
    · exact Or.inl hpos
    · exact Or.inr (by omega)
  have hne : t.Nonempty := by
    by_contra! hempty
    have hem : t = ∅ := hempty
    rw [hem] at htotal hsum hdx htstrict
    have hzero : totalOn G s = 0 := by simpa [totalOn, degreeOn] using htotal
    have hsumzero : (∑ u ∈ s, f u) = f x := by simpa using hsum
    rcases hstrict with hall | hlt
    · have := hall x; omega
    · omega
  exact core_from_set f t hne (by omega) htstrict
termination_by s.card
decreasing_by exact Finset.card_erase_lt_of_mem hxs

/-- Peeling vertices of internal degree at most their assigned allowance leaves a
nonempty induced subgraph satisfying every lower bound and retaining the weighted density. -/
theorem exists_weighted_degree_core [Nonempty V] (f : V → ℕ) (hpos : ∀ x, 0 < f x)
    (h : 2 * (∑ x, f x) ≤ ∑ x, G.degree x) :
    ∃ S : Finset V, S.Nonempty ∧ (∀ v : S, f v < (G.induce (S : Set V)).degree v) ∧
      2 * (∑ v ∈ S, f v) ≤ ∑ v : S, (G.induce (S : Set V)).degree v := by
  classical
  have hh : 2 * (∑ x, f x) ≤ totalOn G Finset.univ := by
    simpa [totalOn, degreeOn_univ] using h
  obtain ⟨s, hs, hdeg, htotal⟩ := core_from_set G f Finset.univ Finset.univ_nonempty hh (Or.inl hpos)
  refine ⟨s, hs, fun v => (degreeOn_induce G s v) ▸ hdeg v, ?_⟩
  calc
    _ ≤ totalOn G s := htotal
    _ = ∑ v : s, degreeOn G s v := (Finset.sum_attach _ _).symm
    _ = _ := Finset.sum_congr rfl (fun v _ => degreeOn_induce G s v)

/-- A finite graph of average degree at least `k ≥ 1` has a nonempty induced
subgraph of minimum degree strictly greater than `⌊k/2⌋`. -/
theorem exists_degree_core [Nonempty V] {k : ℕ} (hk : 0 < k)
    (h : k * Fintype.card V ≤ ∑ v, G.degree v) :
    ∃ S : Finset V, S.Nonempty ∧
      ∀ v : S, k/2+1 ≤ (G.induce (S : Set V)).degree v := by
  classical
  have hprod := Nat.mul_le_mul_right (Fintype.card V) (show 2*(k/2) ≤ k by omega)
  let f := fun _ : V => k/2
  have hs : 2 * (∑ v, f v) ≤ totalOn G Finset.univ := by
    simp only [f, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, totalOn, degreeOn_univ]
    calc
      _ = (2*(k/2)) * Fintype.card V := by ac_rfl
      _ ≤ _ := hprod.trans h
  have hstrict : (∀ x, 0 < f x) ∨ 2 * (∑ v, f v) < totalOn G Finset.univ := by
    by_cases h2 : 2 ≤ k
    · exact Or.inl (fun _ => by dsimp [f]; omega)
    · have h1 : k = 1 := by omega
      subst k
      have hc := Fintype.card_pos (α := V)
      right
      simpa [f, totalOn, degreeOn_univ] using (show 0 < ∑ v, G.degree v by simpa using lt_of_lt_of_le hc (by simpa using h))
  obtain ⟨s, hs, hd, _⟩ := core_from_set G f Finset.univ Finset.univ_nonempty hs hstrict
  exact ⟨s, hs, fun v => (degreeOn_induce G s v) ▸ hd v⟩

/-- At an odd average-degree threshold, the smaller color class can pay one extra
unit in the peeling argument. -/
theorem exists_odd_degree_core_with_density [Nonempty V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (c : G.Coloring (Fin 2)) {m : ℕ} (hm : 0 < m)
    (h : (2*m+1) * Fintype.card V ≤ ∑ v, G.degree v) :
    ∃ (a : Fin 2) (S : Finset V), S.Nonempty ∧ (∀ v : S,
      m+1+(if c v = a then 1 else 0) ≤ (G.induce (S : Set V)).degree v) ∧
      2*(∑ v : S, (m + if c v.val = a then 1 else 0)) ≤ ∑ v : S, (G.induce (S : Set V)).degree v := by
  classical
  let side := fun (a : Fin 2) => (Finset.univ : Finset V).filter (fun v => c v = a)
  have hpartition : (side 0).card + (side 1).card = Fintype.card V := by
    have he : side 1 = Finset.univ.filter (fun v => c v ≠ 0) := by
      ext v
      simp only [side, Finset.mem_filter, Finset.mem_univ, true_and]
      generalize c v = i
      fin_cases i <;> decide
    rw [he]
    exact Finset.card_filter_add_card_filter_not (fun v => c v = 0)
  obtain ⟨a, ha⟩ : ∃ a : Fin 2, 2*(side a).card ≤ Fintype.card V := by
    by_cases h0 : 2*(side 0).card ≤ Fintype.card V
    · exact ⟨0, h0⟩
    · exact ⟨1, by omega⟩
  let f := fun v : V => m + if c v = a then 1 else 0
  have hf : (∑ x, f x) = Fintype.card V * m + (side a).card := by
    simp [f, side, Finset.sum_add_distrib, Finset.sum_boole]
  have hbudget : 2*(∑ v, f v) ≤ ∑ v, G.degree v := by
    rw [hf]
    apply le_trans _ h
    rw [Nat.mul_add, Nat.add_mul, Nat.one_mul]
    have he : 2 * (Fintype.card V * m) = 2 * m * Fintype.card V := by ac_rfl
    omega
  obtain ⟨s, hs, hd, hsum⟩ := exists_weighted_degree_core G f (fun _ => by dsimp [f]; omega) hbudget
  refine ⟨a, s, hs, fun v => ?_, ?_⟩
  swap
  · have he := Finset.sum_attach s f
    rw [← he] at hsum
    exact hsum
  have hm := hd v
  unfold f at hm
  omega

/-- The odd-density core has a stronger minimum degree on one color class. -/
theorem exists_odd_degree_core [Nonempty V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (c : G.Coloring (Fin 2)) {m : ℕ} (hm : 0 < m)
    (h : (2*m+1) * Fintype.card V ≤ ∑ v, G.degree v) :
    ∃ (a : Fin 2) (S : Finset V), S.Nonempty ∧ ∀ v : S,
      m+1+(if c v = a then 1 else 0) ≤ (G.induce (S : Set V)).degree v := by
  obtain ⟨a,S,hS,hmin,-⟩ := exists_odd_degree_core_with_density c hm h
  exact ⟨a,S,hS,hmin⟩

end Wall133
