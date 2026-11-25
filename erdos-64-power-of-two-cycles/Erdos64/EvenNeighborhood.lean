import Erdos64.Identification

/-! Doubling cycles through the vertices adjacent to a selected independent set. -/
namespace Erdos64.EvenNeighborhood

universe u
variable {V : Type u} {G : Graph V} {X : V → Prop}

/-- The graph on the selected vertices in which an edge records a common neighbor. -/
def halfSquare (G : Graph V) (X : V → Prop) : Graph {v // X v} where
  adj x y := x ≠ y ∧ ∃ b, G.adj x.val b ∧ G.adj y.val b
  symm := by rintro x y ⟨h,b,hx,hy⟩; exact ⟨h.symm,b,hy,hx⟩
  loopless := by intro x h; exact h.1 rfl

/-- Every vertex meeting the selected set has exactly two neighbors there. -/
def Paired (G : Graph V) (X : V → Prop) : Prop :=
  ∀ (x : {v // X v}) b, G.adj x.val b →
    ∃ y : {v // X v}, y ≠ x ∧ G.adj y.val b ∧
      ∀ w : {v // X v}, G.adj w.val b → w = x ∨ w = y

/-- The half-square preserves the entire degree, including one or two lost
incidences at a marked branch vertex in the bipartite descent. -/
theorem neighborBijection (h : Paired G X) (noFour : ¬ HasCycle G 4) (x : {v // X v}) :
    ∃ f : {b // G.adj x.val b} → {y // (halfSquare G X).adj x y},
      (∀ b c, f b = f c → b = c) ∧ ∀ y, ∃ b, f b = y := by
  classical
  let partner (b : {b // G.adj x.val b}) := Classical.choose (h x b.val b.property)
  have spec (b : {b // G.adj x.val b}) := Classical.choose_spec (h x b.val b.property)
  let f (b : {b // G.adj x.val b}) : {y // (halfSquare G X).adj x y} :=
    ⟨partner b,(spec b).1.symm,b.val,b.property,(spec b).2.1⟩
  refine ⟨f,?_,?_⟩
  · intro b c eq
    have partners : partner b = partner c := congrArg Subtype.val eq
    apply Classical.byContradiction
    intro diff
    have adjacent : G.adj (partner b).val c.val := by
      rw [partners]; exact (spec c).2.1
    exact noFour (Identification.fourOfCommon
      (fun a => (spec b).1 (Subtype.ext a.symm)) (fun a => diff (Subtype.ext a))
      b.property c.property (spec b).2.1 adjacent)
  · rintro ⟨y,ne,b,xb,yb⟩
    let z : {b // G.adj x.val b} := ⟨b,xb⟩
    exact ⟨z, Subtype.ext (((spec z).2.2 y yb).resolve_left ne.symm).symm⟩

theorem minDegree (h : Paired G X) (degree : MinDegreeThree G)
    (noFour : ¬ HasCycle G 4) : MinDegreeThree (halfSquare G X) := by
  intro x
  obtain ⟨a,b,c,ha,hb,hc,ab,ac,bc⟩ := degree x.val
  obtain ⟨f,inject,_⟩ := neighborBijection h noFour x
  have lift {u v : V} (hu : G.adj x.val u) (hv : G.adj x.val v) (diff : u ≠ v) :
      (f ⟨u,hu⟩).val ≠ (f ⟨v,hv⟩).val := fun eq =>
    diff (congrArg Subtype.val (inject _ _ (Subtype.ext eq)))
  exact ⟨_,_,_,(f ⟨a,ha⟩).property,(f ⟨b,hb⟩).property,(f ⟨c,hc⟩).property,
    lift ha hb ab, lift ha hc ac, lift hb hc bc⟩

private theorem nextValue {k : Nat} (i : Fin k) :
    (cycleNext i).val = if i.val+1 < k then i.val+1 else 0 := by
  change (i.val + 1) % k = _
  split
  next h => exact Nat.mod_eq_of_lt h
  next h => have eq : i.val+1 = k := by omega
            simp [eq]

private theorem nextTwice {k : Nat} (hk : 3 ≤ k) (i : Fin k) : cycleNext (cycleNext i) ≠ i := by
  intro e
  have eq := congrArg Fin.val e
  simp only [nextValue] at eq
  split at eq <;> split at * <;> omega

/-- Two disjoint injective vertex sequences joined by alternating edges form a cycle. -/
theorem interleaveCycle {k : Nat} (f g : Fin k → V)
    (fi : ∀ i j, f i = f j → i = j) (gi : ∀ i j, g i = g j → i = j)
    (sep : ∀ i j, f i ≠ g j) (start : ∀ i, G.adj (f i) (g i))
    (finish : ∀ i, G.adj (g i) (f (cycleNext i))) : HasCycle G (2*k) := by
  let half (i : Fin (2*k)) : Fin k := ⟨i.val/2, by omega⟩
  let label (i : Fin (2*k)) := if i.val % 2 = 0 then f (half i) else g (half i)
  have same {i j : Fin (2*k)} (h : half i = half j) (parity : i.val % 2 = j.val % 2) :
      i = j := by
    have index := congrArg Fin.val h
    dsimp [half] at index
    exact Fin.ext (by omega)
  refine ⟨label,?_,?_⟩
  · intro i j eq
    simp only [label] at eq
    split at eq <;> split at eq
    · exact same (fi _ _ eq) (by omega)
    · exact False.elim (sep _ _ eq)
    · exact False.elim (sep _ _ eq.symm)
    · exact same (gi _ _ eq) (by omega)
  · intro i
    by_cases even : i.val % 2 = 0
    · have next : (cycleNext i).val = i.val + 1 := Nat.mod_eq_of_lt (by omega)
      have odd : (cycleNext i).val % 2 ≠ 0 := by omega
      have index : half (cycleNext i) = half i := Fin.ext (by dsimp [half]; omega)
      simpa [label,even,odd,index] using start (half i)
    · have next := nextValue i
      have parity : (cycleNext i).val % 2 = 0 := by split at next <;> omega
      have index : half (cycleNext i) = cycleNext (half i) := by
        apply Fin.ext
        simp only [half,nextValue]
        split <;> split <;> omega
      simpa [label,even,parity,index] using finish (half i)

/-- A simple cycle on selected branch vertices lifts to a simple cycle of twice
its length. The pairing condition keeps different subdividing vertices distinct. -/
theorem liftCycle (indep : ∀ {v w}, X v → X w → ¬ G.adj v w) (paired : Paired G X)
    {k : Nat} (hk : 3 ≤ k) (cyc : HasCycle (halfSquare G X) k) : HasCycle G (2*k) := by
  classical
  obtain ⟨f,inj,edges⟩ := cyc
  let mid (i : Fin k) := Classical.choose (edges i).2
  have steps (i : Fin k) := Classical.choose_spec (edges i).2
  apply interleaveCycle (fun i => (f i).val) mid
  · intro i j eq; exact inj _ _ (Subtype.ext eq)
  · intro i j eq
    obtain ⟨y,_,_,two⟩ := paired (f i) (mid i) (steps i).1
    have endEq : f (cycleNext i) = y :=
      (two _ (steps i).2).resolve_left (edges i).1.symm
    have first : G.adj (f j).val (mid i) := eq ▸ (steps j).1
    have last : G.adj (f (cycleNext j)).val (mid i) := eq ▸ (steps j).2
    rcases two _ first with a|a
    · exact (inj _ _ a).symm
    · have ji := inj _ _ (a.trans endEq.symm)
      have ij := inj _ _ ((two _ last).resolve_right (fun b => (edges j).1 (a.trans b.symm)))
      exact False.elim (nextTwice hk i (ji ▸ ij))
  · intro i j eq
    exact indep (f j).property (f i).property (eq ▸ (steps j).1)
  · exact fun i => (steps i).1
  · exact fun i => G.symm (steps i).2

theorem dyadicDescent (degree : MinDegreeThree G) (no : ¬ HasDyadicCycle G)
    (indep : ∀ {v w}, X v → X w → ¬ G.adj v w) (paired : Paired G X) :
    MinDegreeThree (halfSquare G X) ∧ ¬ HasDyadicCycle (halfSquare G X) := by
  refine ⟨minDegree paired degree (fun h => no ⟨2,by decide,h⟩),?_⟩
  rintro ⟨k,hk,cyc⟩
  have lower : 3 ≤ 2^k := by
    have := Nat.pow_le_pow_right (by decide : 0 < 2) hk
    omega
  exact no ⟨k+1,by omega,by simpa [Nat.pow_succ,Nat.mul_comm] using liftCycle indep paired lower cyc⟩

/-- In a minimum-order counterexample a nonempty independent set cannot meet
every outside neighborhood in zero or two vertices. No degree ceiling is used. -/
theorem noPairedOfMinimum (minimal : MinimumOrderCounterexample G)
    (nonempty : ∃ v, X v) (indep : ∀ {v w}, X v → X w → ¬ G.adj v w) :
    ¬ Paired G X := by
  classical
  intro paired
  obtain ⟨x,hx⟩ := nonempty
  obtain ⟨b,_,_,xb,_⟩ := minimal.degree x
  have outside : ¬ X b := fun hb => indep hx hb xb
  let keep := minimal.vertices.filter (fun v => decide (X v))
  let labels := keep.attachWith X (by intro v h; exact of_decide_eq_true (List.mem_filter.mp h).2)
  have covers (w : {v // X v}) : w ∈ labels :=
    (List.mem_attachWith _ _).2 (List.mem_filter.mpr ⟨minimal.covers w.val, decide_eq_true w.property⟩)
  have lt : labels.length < minimal.vertices.length := by
    simpa [labels,keep] using
      (show ∃ v ∈ minimal.vertices, ¬ X v from ⟨b,minimal.covers b,outside⟩)
  obtain ⟨degree,no⟩ := dyadicDescent minimal.degree minimal.avoids indep paired
  exact no (minimal.smaller (halfSquare G X) labels ⟨⟨x,hx⟩⟩ covers lt degree)

end Erdos64.EvenNeighborhood
