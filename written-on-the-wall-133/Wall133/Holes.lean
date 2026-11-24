import Wall133.TriangleCycles

namespace Wall133

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- Positive orientation of edges in the cycle on indices `0, …, n−1`. -/
def CycleStep (n i j : ℕ) : Prop := i + 1 = j ∨ (i + 1 = n ∧ j = 0)

/-- Cyclically ordered distinct vertices, with a graph edge at every step. -/
structure Ring (G : SimpleGraph V) (n : ℕ) where
  vertex : ℕ → V
  inj : ∀ {i j}, i < n → j < n → vertex i = vertex j → i = j
  step : ∀ {i j}, i < n → j < n → CycleStep n i j → G.Adj (vertex i) (vertex j)

/-- The ring has precisely the edges of a cycle. -/
def Ring.Induced {n : ℕ} (C : Ring G n) : Prop :=
  ∀ i j, i < n → j < n → G.Adj (C.vertex i) (C.vertex j) → CycleStep n i j ∨ CycleStep n j i

private def Ring.ofWalk {v} (p : G.Walk v v) (hp : p.IsCycle) : Ring G p.length where
  vertex := p.getVert
  inj := fun hi hj he => hp.getVert_injOn' (by omega : _ ≤ p.length-1)
    (by omega : _ ≤ p.length-1) he
  step := by
    intro i j hi hj hs
    rcases hs with he | ⟨he, rfl⟩
    · subst j
      exact p.adj_getVert_succ hi
    · simpa [he] using p.adj_getVert_succ hi

private def wrapped (n i a : ℕ) : ℕ := if i+a < n then i+a else i+a-n

/-- A chord closes either arc between its endpoints to form a smaller ring. -/
private def Ring.arc {n} (C : Ring G n) (i d : ℕ) (hi : i < n) (hd : d < n)
    (hclose : G.Adj (C.vertex (wrapped n i d)) (C.vertex i)) : Ring G (d+1) where
  vertex a := C.vertex (wrapped n i a)
  inj := by
    intro a b ha hb eq
    have bounded (j) (hj : j ≤ d) : wrapped n i j < n := by unfold wrapped; split <;> omega
    have he := C.inj (bounded a (by omega)) (bounded b (by omega)) eq
    unfold wrapped at he
    split at he <;> split at he <;> omega
  step := by
    intro a b ha hb hs
    rcases hs with he | ⟨he, rfl⟩
    · subst b
      apply C.step <;> unfold wrapped
      · split <;> omega
      · split <;> omega
      · unfold CycleStep
        split <;> split <;> omega
    · have had : a = d := by omega
      simpa [had, wrapped, hi] using hclose

/-- Among rings of length at least four, a shortest one has no chord if it has
at least five vertices. A chord cuts off a proper arc with at least three edges. -/
private theorem Ring.induced_of_min {n} (C : Ring G n) (hn : 5 ≤ n)
    (hmin : ∀ k, 4 ≤ k → Nonempty (Ring G k) → n ≤ k) : C.Induced := by
  have ordered {i j} (hi : i < n) (hj : j < n) (hij : i < j)
      (h : G.Adj (C.vertex i) (C.vertex j)) : CycleStep n i j ∨ CycleStep n j i := by
    by_contra! hno
    obtain ⟨h₁, h₂⟩ := hno
    unfold CycleStep at h₁ h₂
    by_cases hgap : 3 ≤ j-i
    · let d := j-i
      have hwrap : wrapped n i d = j := by unfold wrapped d; split <;> omega
      have R := C.arc i d hi (by dsimp [d]; omega) (by simpa [hwrap] using h.symm)
      have := hmin (d+1) (by unfold d; omega) ⟨R⟩
      unfold d at this
      omega
    · let d := n-(j-i)
      have hwrap : wrapped n j d = i := by unfold wrapped d; split <;> omega
      have R := C.arc j d hj (by unfold d; omega) (by simpa [hwrap] using h)
      have := hmin (d+1) (by unfold d; omega) ⟨R⟩
      unfold d at this
      omega
  intro i j hi hj ha
  rcases lt_trichotomy i j with hij | rfl | hji
  · exact ordered hi hj hij ha
  · exact (ha.ne rfl).elim
  · exact (ordered hj hi hji ha.symm).symm

/-- Any four-cycle-free connected graph with average neighborhood independence
at least two contains an induced cycle of length at least five. -/
theorem exists_induced_ring_of_two_le_l [Fintype V] [DecidableEq V] [Nonempty V]
    (hc : G.Connected) (h4 : NoFourCycle G) (hav : 2 ≤ l G) :
    ∃ n, 5 ≤ n ∧ ∃ C : Ring G n, C.Induced := by
  classical
  have hlong : ∃ n, 4 ≤ n ∧ Nonempty (Ring G n) := by
    by_contra! h
    apply hav.not_gt (l_lt_two_of_cycles_triangles hc h4 ?_)
    intro u p hp
    by_contra! hl
    exact (h _ hl).false (Ring.ofWalk p hp)
  let n := Nat.find hlong
  obtain ⟨hn, ⟨C⟩⟩ := Nat.find_spec hlong
  change 4 ≤ n at hn
  change Ring G n at C
  have hn5 : 5 ≤ n := by
    by_contra! h
    have he : n = 4 := by omega
    have hne (i j : ℕ) (hi : i < n) (hj : j < n) (hne : i ≠ j) : C.vertex i ≠ C.vertex j :=
      fun h => hne (C.inj hi hj h)
    have hadj {i j} (hi : i < n) (hj : j < n) (hij : CycleStep n i j) := C.step hi hj hij
    have h01 := hadj (i := 0) (j := 1) (by omega) (by omega) (Or.inl rfl)
    have h12 := hadj (i := 1) (j := 2) (by omega) (by omega) (Or.inl rfl)
    have h23 := hadj (i := 2) (j := 3) (by omega) (by omega) (Or.inl rfl)
    have h30 := hadj (i := 3) (j := 0) (by omega) (by omega) (.inr ⟨by omega, rfl⟩)
    exact hne 1 3 (by omega) (by omega) (by decide) (h4 (hne 0 2 (by omega) (by omega) (by decide))
      h01 h12.symm h30.symm h23)
  exact ⟨n,hn5,C,C.induced_of_min hn5 (fun k hk hC => Nat.find_min' hlong ⟨hk,hC⟩)⟩

/-- All but one vertex of an induced cycle, taken in order, give an induced path. -/
theorem Ring.path_bound [Fintype V] [DecidableEq V] {k n : ℕ} (C : Ring G n)
    (hC : C.Induced) (hk : k < n) : k ≤ path G := by
  let f (i : Fin k) := C.vertex i.val
  let vs := List.ofFn f
  have hlen : vs.length = k := List.length_ofFn
  rw [← hlen]
  apply G.length_le_path_of_isInducedPath
  refine ⟨List.nodup_ofFn_ofInjective (fun i j h => Fin.ext (C.inj (i.isLt.trans hk) (j.isLt.trans hk) h)), ?_⟩
  intro i j
  have hi : i.val < k := hlen ▸ i.isLt
  have hj : j.val < k := hlen ▸ j.isLt
  change G.Adj ((List.ofFn f)[i.val]) ((List.ofFn f)[j.val]) ↔ _
  simp only [List.getElem_ofFn]
  constructor
  · intro ha
    have := hC _ _ (hi.trans hk) (hj.trans hk) ha
    unfold CycleStep at this
    omega
  · rintro (he | he)
    · exact C.step (hi.trans hk) (hj.trans hk) (.inl he)
    · exact (C.step (hj.trans hk) (hi.trans hk) (.inl he)).symm

end Wall133
