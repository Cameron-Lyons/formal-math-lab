import Ramsey556.Certified16
import Ramsey556.CycleStructure

namespace Ramsey556

private theorem at_most_64 (c : Coloring 16) (k : Fin 3) (free : ¬ HasC9In c k) :
    colorEdgeCount c k ≤ 64 := by
  by_cases dense : 60 ≤ colorEdgeCount c k
  · obtain ⟨g,member,⟨M⟩⟩ := Cert16.model_exists Cert16.completeCatalog 16 c k
      (by decide) (by decide) dense free
    have size : colorEdgeCount c k = Cert16.edgeCount 16 g := by
      rw [← colorEdgeCount_relabel c k M.vertex (@M.inj)]
      apply Eq.symm
      apply cert16_count_eq
      intro i j
      have inj : M.vertex i = M.vertex j ↔ i = j := ⟨fun e => M.inj e,congrArg _⟩
      rw [M.agree]
      apply Bool.eq_iff_iff.mpr
      simp [Coloring.induce, inj]
      exact decide_eq_true_iff.symm
    rw [size]
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp member
    have small : i < 30 := List.mem_range.mp hi
    exact (by decide +kernel : ∀ j : Fin 30, Cert16.edgeCount 16 ((Cert16.table 16).get j.val) ≤ 64) ⟨i,small⟩
  · omega

/-- An induced subgraph of the specified minimum order and minimum color degree seven. -/
def HasSevenCoreOfOrder {n : Nat} (c : Coloring n) (k : Fin 3) (order : Nat) : Prop :=
  ∃ (m : Nat) (v : Fin m → Fin n), order ≤ m ∧ (∀ ⦃i j⦄, v i = v j → i = j) ∧
    ∀ u, 7 ≤ colorDegree (c.induce v) k u

private theorem cap_step {n cap next : Nat}
    (bound : ∀ (c : Coloring n) (k), (¬ HasC9In c k) → colorEdgeCount c k ≤ cap)
    (arith : ∀ e d : Nat, e ≤ cap + d → (n+1)*d ≤ 2*e → e ≤ next)
    (c : Coloring (n+1)) (k : Fin 3) (free : ¬ HasC9In c k) : colorEdgeCount c k ≤ next := by
  obtain ⟨z,v,vi,_,_,loss,avg,_⟩ := delete_min_degree c k
  have clean := mt (HasC9In.of_induce (@vi)) free
  apply arith _ _ _ avg
  rw [loss]
  exact Nat.add_le_add_right (bound _ _ clean) _

private theorem at_most_90 (c : Coloring 19) (k : Fin 3) (free : ¬ HasC9In c k) :
    colorEdgeCount c k ≤ 90 := by
  have b17 := cap_step (next := 72) at_most_64 (by intro e d; omega)
  have b18 := cap_step (next := 81) b17 (by intro e d; omega)
  exact cap_step b18 (by intro e d; omega) c k free

private theorem peel (base cap : Nat)
    (bound : ∀ (c : Coloring base) (k), (¬ HasC9In c k) → colorEdgeCount c k ≤ cap)
    (m : Nat) (lower : base ≤ m) (c : Coloring m) (k : Fin 3)
    (many : cap + 6*m < colorEdgeCount c k + 6*base) (free : ¬ HasC9In c k) :
    HasSevenCoreOfOrder c k (base+1) := by
  induction m with
  | zero =>
    have eq : base = 0 := by omega
    subst base
    have := bound c k free
    omega
  | succ m ih =>
    by_cases atEnd : base = m+1
    · subst base
      have := bound c k free
      omega
    obtain ⟨z,w,wi,_,_,loss,_,minimum⟩ := delete_min_degree c k
    by_cases high : 7 ≤ colorDegree c k z
    · exact ⟨m+1,id,by omega,fun {_ _} e => e,fun i => Nat.le_trans high (minimum i)⟩
    have clean := mt (HasC9In.of_induce (@wi)) free
    obtain ⟨t,v,size,vi,deg⟩ := ih (by omega) (c.induce w) (by omega) clean
    exact ⟨t,fun i => w (v i),size,fun {_ _} e => vi (wi e),deg⟩

/-- Peeling vertices of degree at most six down to 16 vertices would leave
more than the maximum of 64 edges. In particular this applies to any color
of maximum size in a three-colored K₃₃, which has at least 176 edges. -/
theorem largeSevenCore_of_167_edges {c : Coloring 33} {k : Fin 3}
    (many : 167 ≤ colorEdgeCount c k) (free : ¬ HasC9In c k) : HasSevenCoreOfOrder c k 17 :=
  peel 16 64 at_most_64 33 (by decide) c k (by omega) free

/-- The edge tally in the saturation argument agrees with the minimum-degree deletion count. -/
theorem colorEdgeCount33_eq_tally (c : Coloring 33) (k : Fin 3) :
    colorEdgeCount c k = CycleStructure.tally c k := by
  let xs := pairList (List.finRange 33)
  have distinct : ∀ e ∈ xs, e.1 ≠ e.2 := by decide +revert +kernel
  rw [colorEdgeCount, count_pairList]
  change xs.countP _ = _
  rw [show CycleStructure.tally c k = xs.countP (fun e => c.edge e.1 e.2 == k) by rfl]
  apply List.countP_congr
  rintro ⟨a,b⟩ h
  simp [colorAdjacent, distinct (a,b) h]

/-- Removing fourteen vertices of degree six or less from a 175-edge graph
would leave at least 91 edges on nineteen vertices. -/
theorem twentyVertexSevenCore {c : Coloring 33} {k : Fin 3}
    (many : 175 ≤ CycleStructure.tally c k) (free : ¬ HasC9In c k) : HasSevenCoreOfOrder c k 20 := by
  rw [← colorEdgeCount33_eq_tally] at many
  exact peel 19 90 at_most_90 33 (by decide) c k (by omega) free

theorem some_twentyVertexSevenCore {c : Coloring 33} (free : ¬ HasMonoC9 c) :
    ∃ k, 176 ≤ CycleStructure.tally c k ∧ HasSevenCoreOfOrder c k 20 := by
  have total := CycleStructure.tally_total c
  have heavy : ∃ k, 176 ≤ CycleStructure.tally c k := by
    by_cases first : 176 ≤ CycleStructure.tally c 0
    · exact ⟨0,first⟩
    by_cases second : 176 ≤ CycleStructure.tally c 1
    · exact ⟨1,second⟩
    exact ⟨2,by omega⟩
  obtain ⟨k,big⟩ := heavy
  exact ⟨k,big,twentyVertexSevenCore (by omega) (fun h => free ⟨k,h⟩)⟩

end Ramsey556
