import Wall133.Holes
import Wall133.Bipartite

namespace Wall133

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

abbrev CyclicEdge {n : ℕ} (i j : Fin n) := CycleStep n i.val j.val ∨ CycleStep n j.val i.val

instance {n i j : ℕ} : Decidable (CycleStep n i j) := by unfold CycleStep; infer_instance

abbrev Ring.label {n : ℕ} (C : Ring G n) (i : Fin n) := C.vertex i.val

theorem Ring.label_inj {n} (C : Ring G n) : Function.Injective C.label :=
  fun i j h => Fin.ext (C.inj i.isLt j.isLt h)

theorem Ring.edge_iff {n} (C : Ring G n) (hC : C.Induced) (i j : Fin n) :
    G.Adj (C.label i) (C.label j) ↔ CyclicEdge i j := by
  refine ⟨hC _ _ i.isLt j.isLt, ?_⟩
  rintro (h | h)
  · exact C.step i.isLt j.isLt h
  · exact (C.step j.isLt i.isLt h).symm

/-- Possible adjacencies of an outside vertex to a cycle in a four-cycle-free graph. -/
def Legal {n} (S : Finset (Fin n)) := ∀ i j k : Fin n, i ∈ S → j ∈ S →
  CyclicEdge i k → CyclicEdge j k → i = j

instance {n} {S : Finset (Fin n)} : Decidable (Legal S) := by unfold Legal; infer_instance

theorem legal_of_outside {n} (C : Ring G n) (hC : C.Induced) (h4 : NoFourCycle G)
    {w : V} (hw : w ∉ Set.range C.label) [DecidableRel G.Adj] :
    Legal (Finset.univ.filter (fun i => G.Adj w (C.label i))) := by
  intro i j k hi hj hik hjk
  apply C.label_inj
  apply h4 (show w ≠ C.label k from fun h => hw ⟨k, h.symm⟩)
    (Finset.mem_filter.mp hi).2 ((C.edge_iff hC i k).2 hik).symm
    (Finset.mem_filter.mp hj).2 ((C.edge_iff hC j k).2 hjk).symm

def forwardArc {n k} [NeZero n] (start : Fin n) (forward : Bool) (j : Fin k) : Fin n :=
  if forward then start + Fin.ofNat n j.val else start - Fin.ofNat n j.val

def CleanArc {n k} (S : Finset (Fin n)) (q : Fin k → Fin n) :=
  Function.Injective q ∧
  (∀ i j, CyclicEdge (q i) (q j) ↔ i.val+1 = j.val ∨ j.val+1 = i.val) ∧
  (∀ i, q i ∈ S ↔ i.val = 0)

instance {n k} {S : Finset (Fin n)} {q : Fin k → Fin n} : Decidable (CleanArc S q) := by
  unfold CleanArc Function.Injective; infer_instance

/-- On a five-cycle, a nonempty legal set touches just the first vertex of
some four-vertex arc. -/
lemma five_arc_table : ∀ S : Finset (Fin 5), S.Nonempty → Legal S →
    ∃ (a : Fin 5) (b : Bool), CleanArc S (forwardArc (k := 4) a b) := by decide

theorem path_bound_of_indices [Fintype V] [DecidableEq V] {k : ℕ} (f : Fin k → V)
    (hinj : Function.Injective f) (hedge : ∀ i j, G.Adj (f i) (f j) ↔ i.val+1 = j.val ∨ j.val+1 = i.val) :
    k ≤ path G := by
  have hlen : (List.ofFn f).length = k := List.length_ofFn
  rw [← hlen]
  apply G.length_le_path_of_isInducedPath
  refine ⟨List.nodup_ofFn_ofInjective hinj, ?_⟩
  intro i j
  change G.Adj ((List.ofFn f)[i.val]) ((List.ofFn f)[j.val]) ↔ _
  simp only [List.getElem_ofFn]
  apply hedge

lemma CleanArc.extend [Fintype V] [DecidableEq V] {n k} (C : Ring G n) (hC : C.Induced)
    {S : Finset (Fin n)} {q : Fin k → Fin n} (hq : CleanArc S q) {w : V}
    (hw : w ∉ Set.range C.label) (hs : ∀ i, i ∈ S ↔ G.Adj w (C.label i)) : k+1 ≤ path G := by
  let f (j : Fin (k+1)) : V := Fin.cases w (fun i => C.label (q i)) j
  apply path_bound_of_indices f
  · intro i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · simp
    · exact fun h => False.elim (hw ⟨q j, h.symm⟩)
    · exact fun h => False.elim (hw ⟨q i, h⟩)
    · exact fun h => congrArg Fin.succ (hq.1 (C.label_inj h))
  · intro i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · simp [f]
    · simpa [f] using (hs _).symm.trans (hq.2.2 j)
    · rw [G.adj_comm]
      simpa [f] using (hs _).symm.trans (hq.2.2 i)
    · simpa [f] using (C.edge_iff hC (q i) (q j)).trans (hq.2.1 i j)

theorem exits {S : Set V} {v w : V} (p : G.Walk v w) (hv : v ∈ S) (hw : w ∉ S) :
    ∃ x ∈ S, ∃ y ∉ S, G.Adj x y := by
  induction p with
  | nil => exact (hw hv).elim
  | @cons u a z hua p ih =>
    by_cases ha : a ∈ S
    · exact ih ha hw
    · exact ⟨u, hv, a, ha, hua⟩

lemma Ring.average_le_two_of_surjective [Fintype V] [Nonempty V] [DecidableRel G.Adj] {n : ℕ} (C : Ring G n)
    (hC : C.Induced) (h : Function.Surjective C.label)
    (bound : ∀ i : Fin n, Fintype.card {j : Fin n // CyclicEdge i j} ≤ 2) : l G ≤ 2 := by
  classical
  let e := Equiv.ofBijective C.label ⟨C.label_inj,h⟩
  apply averageIndepNeighbors_le_of_degree_le (d := 2)
  intro v
  obtain ⟨i, rfl⟩ := h v
  rw [← G.card_neighborSet_eq_degree]
  apply le_trans _ (bound i)
  let f (w : G.neighborSet (C.label i)) : {j : Fin n // CyclicEdge i j} :=
    ⟨e.symm w.1, (C.edge_iff hC i _).1 (by simpa [← show ∀ j, e j = C.label j from fun _ => rfl] using w.2)⟩
  exact Fintype.card_le_of_injective f (fun x y h => Subtype.ext (e.symm.injective (congrArg Subtype.val h)))

/-- In a connected four-cycle-free graph an average strictly above two forces
an induced path on five vertices. -/
theorem five_le_path_of_two_lt_l [Fintype V] [DecidableEq V] [Nonempty V]
    (hc : G.Connected) (h4 : NoFourCycle G) (hav : 2 < l G) : 5 ≤ path G := by
  classical
  obtain ⟨n, hn, C, hC⟩ := exists_induced_ring_of_two_le_l hc h4 hav.le
  by_cases h : 5 < n
  · exact C.path_bound hC h
  obtain rfl : n = 5 := by omega
  have hsur : ¬Function.Surjective C.label := fun h => hav.not_ge (C.average_le_two_of_surjective hC h (by decide))
  obtain ⟨w, hw⟩ : ∃ w, w ∉ Set.range C.label := by simpa [Function.Surjective, Set.mem_range] using hsur
  obtain ⟨p⟩ := hc (C.label 0) w
  obtain ⟨x, ⟨i, rfl⟩, y, hy, hiy⟩ := exits (S := Set.range C.label) p ⟨0,rfl⟩ hw
  let S := Finset.univ.filter (fun i => G.Adj y (C.label i))
  have hs (j) : j ∈ S ↔ G.Adj y (C.label j) := by simp [S]
  obtain ⟨a,b,hab⟩ := five_arc_table S ⟨i,(hs i).2 hiy.symm⟩ (legal_of_outside C hC h4 hy)
  exact CleanArc.extend C hC hab hy hs

end Wall133
