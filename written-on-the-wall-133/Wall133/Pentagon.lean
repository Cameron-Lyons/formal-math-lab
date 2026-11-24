import Wall133.FiveCycle

namespace Wall133
open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

private abbrev Six := Option (Option (Fin 4))

/-- The four arc vertices and two vertices outside the cycle. -/
private def pattern (X Y : Finset (Fin 4)) (b : Bool) : Six → Six → Prop
  | none, none | some none, some none => False
  | none, some none | some none, none => b = true
  | none, some (some i) | some (some i), none => i ∈ X
  | some none, some (some i) | some (some i), some none => i ∈ Y
  | some (some i), some (some j) => i.val + 1 = j.val ∨ j.val + 1 = i.val

private instance (X Y : Finset (Fin 4)) (b : Bool) (i j : Six) : Decidable (pattern X Y b i j) := by
  cases i with
  | none => cases j with | none => dsimp [pattern]; infer_instance | some j => cases j <;> dsimp [pattern] <;> infer_instance
  | some i => cases i <;> cases j with
    | none => dsimp [pattern]; infer_instance
    | some j => cases j <;> dsimp [pattern] <;> infer_instance

private def endpoints : Fin 6 → Six := ![none, some (some 0), some (some 1), some (some 2), some (some 3), some none]
private def serial : Fin 6 → Six := ![some none, none, some (some 0), some (some 1), some (some 2), some (some 3)]

private def arcLabel (C : Ring G 5) (q : Fin 4 → Fin 5) (a b : V) : Six → V
  | none => a
  | some none => b
  | some (some i) => C.label (q i)

private theorem arc_inj (C : Ring G 5) {q : Fin 4 → Fin 5} (hq : Function.Injective q)
    {a b : V} (ha : a ∉ Set.range C.label) (hb : b ∉ Set.range C.label) (hab : a ≠ b) :
    Function.Injective (arcLabel C q a b) := by
  have ha' (i) : a ≠ C.label (q i) := fun he => ha ⟨q i, he.symm⟩
  have hb' (i) : b ≠ C.label (q i) := fun he => hb ⟨q i, he.symm⟩
  intro i j h
  rcases i with _ | (_ | i) <;> rcases j with _ | (_ | j) <;>
    simp_all [arcLabel, Ne.symm, C.label_inj.eq_iff, hq.eq_iff]

private theorem arc_edges (C : Ring G 5) (hC : C.Induced) {q : Fin 4 → Fin 5}
    (hedge : ∀ i j, CyclicEdge (q i) (q j) ↔ i.val+1=j.val ∨ j.val+1=i.val)
    {a b : V} {X Y : Finset (Fin 4)} {cross : Bool}
    (ha : ∀ i, G.Adj a (C.label (q i)) ↔ i ∈ X)
    (hb : ∀ i, G.Adj b (C.label (q i)) ↔ i ∈ Y)
    (hab : G.Adj a b ↔ cross = true) (i j : Six) :
    G.Adj (arcLabel C q a b i) (arcLabel C q a b j) ↔ pattern X Y cross i j := by
  rcases i with _ | (_ | i) <;> rcases j with _ | (_ | j) <;>
    first | exact ha _ | exact hb _ | exact hab | exact (C.edge_iff hC _ _).trans (hedge _ _) |
      exact (G.adj_comm ..).trans (ha _) | exact (G.adj_comm ..).trans (hb _) |
      exact (G.adj_comm ..).trans hab | simp [arcLabel,pattern]

private def DistinctFin (q : Fin 6 → Six) : Prop := Function.Injective q
private instance (q : Fin 6 → Six) : Decidable (DistinctFin q) := by unfold DistinctFin Function.Injective; infer_instance

private theorem realize_path [Fintype V] [DecidableEq V]
    {X Y : Finset (Fin 4)} {cross : Bool} {q : Fin 6 → Six} {f : Six → V}
    (hf : Function.Injective f) (he : ∀ i j, G.Adj (f i) (f j) ↔ pattern X Y cross i j)
    (hq : DistinctFin q) (heq : ∀ i j, pattern X Y cross (q i) (q j) ↔ i.val+1=j.val ∨ j.val+1=i.val) :
    6 ≤ path G := path_bound_of_indices (f ∘ q) (hf.comp hq) (fun i j => (he _ _).trans (heq i j))

private theorem realize_six {f : Six → V} (hf : Function.Injective f)
    (he : ∀ i j, G.Adj (f i) (f j) ↔ pattern {0} {3} true i j) : ∃ D : Ring G 6, D.Induced := by
  have hinj : DistinctFin endpoints := by decide
  have htable : ∀ i j : Fin 6, pattern {0} {3} true (endpoints i) (endpoints j) ↔ CyclicEdge i j := by decide
  let C : Ring G 6 := {
    vertex := fun i => f (endpoints (Fin.ofNat 6 i))
    inj := by
      intro i j hi hj hh
      have := congrArg Fin.val (hinj (hf hh))
      simpa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] using this
    step := by
      intro i j hi hj hij
      apply (he _ _).2 ((htable _ _).2 (Or.inl ?_))
      simpa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] using hij }
  refine ⟨C, ?_⟩
  intro i j hi hj ha
  have h := (htable _ _).1 ((he _ _).1 ha)
  simpa [CyclicEdge, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] using h

private def attach [DecidableRel G.Adj] (C : Ring G 5) (v : V) :=
  Finset.univ.filter fun i => G.Adj v (C.label i)

private theorem attach_iff [DecidableRel G.Adj] (C : Ring G 5) (v : V) (i : Fin 5) :
    i ∈ attach C v ↔ G.Adj v (C.label i) := by simp [attach]

/-- Unless an induced six-vertex path already exists, the five-cycle dominates. -/
private theorem dominates [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (C : Ring G 5) (hC : C.Induced) (hc : G.Connected) (h4 : NoFourCycle G)
    (hshort : ¬ 6 ≤ path G) (v : V) : v ∈ Set.range C.label ∨ (attach C v).Nonempty := by
  classical
  let S : Set V := {w | w ∈ Set.range C.label ∨ (attach C w).Nonempty}
  by_contra hv
  obtain ⟨p⟩ := hc (C.label 0) v
  obtain ⟨a, ha, b, hb, hab⟩ := exits (S := S) p (Or.inl ⟨0,rfl⟩) hv
  have hb' : b ∉ Set.range C.label := fun h => hb (Or.inl h)
  have hmiss (i : Fin 5) : ¬G.Adj b (C.label i) := fun h => hb (Or.inr ⟨i,(attach_iff ..).2 h⟩)
  have ha' : a ∉ Set.range C.label := by rintro ⟨i,rfl⟩; exact hmiss i hab.symm
  obtain ⟨u, d, hq⟩ := five_arc_table (attach C a) (ha.resolve_left ha') (legal_of_outside C hC h4 ha')
  let q := forwardArc (k := 4) u d
  have hinj := arc_inj C (q := q) hq.1 ha' hb' hab.ne
  have he := arc_edges C hC (q := q) hq.2.1 (a := a) (b := b) (X := {0}) (Y := ∅) (cross := true)
    (fun i => by
      rw [Finset.mem_singleton]
      exact ((attach_iff C a (q i)).symm.trans (hq.2.2 i)).trans
        ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩)
    (fun i => by simp [hmiss]) (by simp [hab])
  exact hshort (realize_path (q := serial) hinj he (by decide) (by decide))

private def farType (i : Fin 5) (t : Fin 3) : Finset (Fin 5) :=
  if t = 0 then {i+2} else if t = 1 then {i+3} else {i+2, i+3}

private theorem far_type_table : ∀ (i : Fin 5) (S : Finset (Fin 5)), S.Nonempty →
    (∀ j ∈ S, i ≠ j ∧ ¬CyclicEdge i j) → ∃ t, S = farType i t := by decide

private def Matches (S T : Finset (Fin 5)) (a : Fin 5) (d : Bool) : Prop :=
  CleanArc S (forwardArc (k := 4) a d) ∧
    ∀ i : Fin 4, forwardArc a d i ∈ T ↔ i.val = 3

private instance (S T : Finset (Fin 5)) (a : Fin 5) (d : Bool) : Decidable (Matches S T a d) := by
  unfold Matches; infer_instance

/-- On a five-cycle, selecting a far attachment at each possible center gives
two distinct outside vertices which meet a common four-vertex arc at opposite ends. -/
private theorem opposite_arcs (t : Fin 5 → Fin 3) :
    ∃ i j a d, Matches (farType i (t i)) (farType j (t j)) a d := by
  revert t
  set_option maxRecDepth 30000 in
    decide

/-- A five-cycle in a connected graph without four-cycles either has a vertex
of eccentricity at most two, or yields an induced path or cycle on six vertices. -/
theorem ring_five_trichotomy [Fintype V] [DecidableEq V] [Nonempty V]
    (hc : G.Connected) (h4 : NoFourCycle G) (C : Ring G 5) (hC : C.Induced) :
    6 ≤ path G ∨ G.radius.toNat ≤ 2 ∨ ∃ D : Ring G 6, D.Induced := by
  classical
  by_cases hshort : 6 ≤ path G
  · exact Or.inl hshort
  by_cases hrad : G.radius.toNat ≤ 2
  · exact Or.inr (Or.inl hrad)
  right; right
  have hdist (i j : Fin 5) : G.dist (C.label i) (C.label j) ≤ 2 := by
    have ht : ∀ i j : Fin 5, i=j ∨ CyclicEdge i j ∨ ∃ k, CyclicEdge i k ∧ CyclicEdge k j := by decide
    rcases ht i j with rfl | h | ⟨k,h₁,h₂⟩
    · simp
    · rw [dist_eq_one_iff_adj.mpr ((C.edge_iff hC ..).2 h)]; decide
    · have h := hc.dist_triangle (u := C.label i) (v := C.label k) (w := C.label j)
      rwa [dist_eq_one_iff_adj.mpr ((C.edge_iff hC ..).2 h₁),
        dist_eq_one_iff_adj.mpr ((C.edge_iff hC ..).2 h₂)] at h
  have far (i : Fin 5) : ∃ x, x ∉ Set.range C.label ∧ ∃ t, attach C x = farType i t := by
    obtain ⟨x,hx⟩ := G.exists_edist_eq_eccent_of_finite (C.label i)
    have hrx : G.radius.toNat ≤ G.dist (C.label i) x := ENat.toNat_le_toNat (hx ▸ G.radius_le_eccent)
      (edist_ne_top_iff_reachable.mpr (hc _ _))
    have hx' : x ∉ Set.range C.label := by rintro ⟨j,rfl⟩; have := hdist i j; omega
    refine ⟨x,hx', far_type_table i _ ((dominates C hC hc h4 hshort x).resolve_left hx') ?_⟩
    intro j hj
    have h1 := dist_eq_one_iff_adj.mpr ((attach_iff C x j).1 hj).symm
    constructor
    · rintro rfl; omega
    · intro hij
      have h2 := dist_eq_one_iff_adj.mpr ((C.edge_iff hC i j).2 hij)
      have h := hc.dist_triangle (u := C.label i) (v := C.label j) (w := x)
      omega
  choose x hx t ht using far
  obtain ⟨i,j,a,d,hq,hend⟩ := opposite_arcs t
  let q := forwardArc (k := 4) a d
  have hstart (u : Fin 4) : G.Adj (x i) (C.label (q u)) ↔ u.val = 0 := by
    rw [← attach_iff, ht i]; exact hq.2.2 u
  have hfinish (u : Fin 4) : G.Adj (x j) (C.label (q u)) ↔ u.val = 3 := by
    rw [← attach_iff, ht j]; exact hend u
  have hne : x i ≠ x j := by
    intro he
    have h := (hstart 0).2 rfl
    rw [he] at h
    exact (by decide : ¬ (0:Fin 4).val=3) ((hfinish 0).1 h)
  have hinj := arc_inj C (q := q) hq.1 (hx i) (hx j) hne
  have he (b : Bool) (hb : G.Adj (x i) (x j) ↔ b = true) :=
    arc_edges C hC (q := q) hq.2.1 (X := {0}) (Y := {3}) (cross := b)
      (fun u => by
        rw [Finset.mem_singleton]
        exact (hstart u).trans ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩)
      (fun u => by
        rw [Finset.mem_singleton]
        exact (hfinish u).trans ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩) hb
  by_cases hcross : G.Adj (x i) (x j)
  · exact realize_six hinj (he true (by simp [hcross]))
  · exact (hshort (realize_path (q := endpoints) hinj (he false (by simp [hcross])) (by decide) (by decide))).elim

end Wall133
