import Ramsey556.Basic

namespace Ramsey556

/-- Close a simple path on eight vertices through a ninth vertex. -/
theorem closeC9InThrough {n : Nat} (c : Coloring n) (k : Fin 3) (p : Fin 8 → Fin n) (z : Fin n)
    (hi : ∀ ⦃i j⦄, p i = p j → i = j) (havoid : ∀ i, p i ≠ z)
    (hp : ∀ i : Fin 8, ∀ h : i.val + 1 < 8, c.edge (p i) (p ⟨i.val + 1, h⟩) = k)
    (h0 : c.edge z (p 0) = k) (h7 : c.edge z (p 7) = k) : HasC9In c k := by
  let v (i : Fin 9) : Fin n := if h : i.val < 8 then p ⟨i.val, h⟩ else z
  refine ⟨v, ?_, ?_⟩
  · intro i j hij
    simp only [v] at hij
    split at hij <;> split at hij
    · exact Fin.ext (congrArg (fun x : Fin 8 => x.val) (hi hij))
    · exact (havoid _ hij).elim
    · exact (havoid _ hij.symm).elim
    · exact Fin.ext (by omega)
  · intro i
    by_cases h : i.val < 7
    · have hj : (i + 1).val = i.val + 1 := by
        change (i.val + 1) % 9 = i.val + 1
        omega
      simpa [v, hj, show i.val < 8 by omega, show i.val + 1 < 8 by omega] using
        hp ⟨i.val, by omega⟩ (by simp; omega)
    · by_cases h7' : i = 7
      · subst i
        change c.edge (p 7) z = k
        rwa [c.symm]
      · have hi8 : i = 8 := Fin.ext (by change i.val = 8; omega)
        subst i
        exact h0

/-- The cycle through the extra vertex is monochromatic. -/
theorem closeC9Through {n : Nat} (c : Coloring n) (k : Fin 3) (p : Fin 8 → Fin n) (z : Fin n)
    (hi : ∀ ⦃i j⦄, p i = p j → i = j) (havoid : ∀ i, p i ≠ z)
    (hp : ∀ i : Fin 8, ∀ h : i.val + 1 < 8, c.edge (p i) (p ⟨i.val + 1, h⟩) = k)
    (h0 : c.edge z (p 0) = k) (h7 : c.edge z (p 7) = k) : HasMonoC9 c :=
  ⟨k, closeC9InThrough c k p z hi havoid hp h0 h7⟩

/-- A path on eight old vertices closes through the new vertex if its endpoints
    meet the new vertex in the path's color. -/
theorem closeC9ThroughLast {n : Nat} (c : Coloring (n + 1)) (k : Fin 3) (p : Fin 8 → Fin n)
    (hi : ∀ ⦃i j⦄, p i = p j → i = j)
    (hp : ∀ i : Fin 8, ∀ h : i.val + 1 < 8,
      c.edge (p i).castSucc (p ⟨i.val + 1, h⟩).castSucc = k)
    (h0 : c.edge (Fin.last n) (p 0).castSucc = k)
    (h7 : c.edge (Fin.last n) (p 7).castSucc = k) : HasMonoC9 c := by
  apply closeC9Through c k (fun i => (p i).castSucc) (Fin.last n)
      (fun {_ _} h => hi (Fin.castSucc_inj.mp h)) _ hp h0 h7
  intro i h
  have heq := congrArg Fin.val h
  simp only [Fin.val_castSucc, Fin.val_last] at heq
  omega

/-- Delete the vertex with highest index. -/
def dropLast {n : Nat} (c : Coloring (n+1)) : Coloring n where
  edge u v := c.edge u.castSucc v.castSucc
  symm _ _ := c.symm _ _

/-- Two vertices conflict for color `k` if a simple path of seven edges
of that color connects them. Coloring both new incident edges `k` then closes a C₉. -/
def Conflict {n : Nat} (c : Coloring n) (k : Fin 3) (a b : Fin n) : Prop :=
  ∃ p : Fin 8 → Fin n,
    (∀ ⦃i j⦄, p i = p j → i = j) ∧ p 0 = a ∧ p 7 = b ∧
      ∀ (i : Fin 8) (h : i.val + 1 < 8), c.edge (p i) (p ⟨i.val + 1, h⟩) = k

/-- An assignment of colors to the edges incident with a new vertex is
compatible when each of its three color classes avoids its conflicts. -/
def Compatible {n : Nat} (c : Coloring n) (f : Fin n → Fin 3) : Prop :=
  ∀ k a b, Conflict c k a b → f a = k → f b ≠ k

private theorem liftCycle {n : Nat} {c : Coloring (n+1)} :
    HasMonoC9 (dropLast c) → HasMonoC9 c := by
  rintro ⟨k, v, hv, edges⟩
  exact ⟨k, fun i => (v i).castSucc, fun {_ _} h => hv (Fin.castSucc_inj.mp h), edges⟩

/-- A full characterization of the one-vertex extensions with no monochromatic C₉. -/
theorem free_iff_compatible {n : Nat} (c : Coloring (n+1)) :
    ¬ HasMonoC9 c ↔ ¬ HasMonoC9 (dropLast c) ∧
      Compatible (dropLast c) (fun a => c.edge (Fin.last n) a.castSucc) := by
  constructor
  · intro h
    refine ⟨fun hbase => h (liftCycle hbase), ?_⟩
    rintro k a b ⟨p, hp, rfl, rfl, hpath⟩ ha hb
    exact h (closeC9ThroughLast c k p hp hpath ha hb)
  · rintro ⟨hbase, hcompatible⟩ ⟨k, v, hv, hedges⟩
    by_cases used : ∃ t, v t = Fin.last n
    · obtain ⟨t, ht⟩ := used
      -- Read the next eight vertices after t in their cyclic order.
      let pos (i : Fin 8) : Fin 9 := t + i.succ
      have off : ∀ t : Fin 9, ∀ i : Fin 8, t + i.succ ≠ t := by decide
      have old (i : Fin 8) : (v (pos i)).val < n := by
        apply Fin.val_lt_last
        intro h
        exact off t i (hv (h.trans ht.symm))
      let p (i : Fin 8) := (v (pos i)).castLT (old i)
      have castP (i : Fin 8) : (p i).castSucc = v (pos i) := Fin.castSucc_castLT _ _
      have step : ∀ (t : Fin 9) (i : Fin 8) (h : i.val + 1 < 8),
          (t + i.succ) + 1 = t + (⟨i.val + 1, h⟩ : Fin 8).succ := by decide
      have cancel : ∀ (t : Fin 9) (i j : Fin 8), t + i.succ = t + j.succ → i = j := by decide
      have path : Conflict (dropLast c) k (p 0) (p 7) := by
        refine ⟨p, ?_, rfl, rfl, ?_⟩
        · intro i j h
          exact cancel t i j (hv (by simpa only [castP] using congrArg Fin.castSucc h))
        · intro i h
          change c.edge (p i).castSucc (p ⟨i.val + 1, h⟩).castSucc = k
          simpa only [castP, pos, step t i h] using hedges (pos i)
      have firstEdge : c.edge (Fin.last n) (p 0).castSucc = k := by
        rw [castP, ← ht]
        exact hedges t
      have endPos : ∀ t : Fin 9, (t + (7 : Fin 8).succ) + 1 = t := by decide
      apply hcompatible k _ _ path firstEdge
      change c.edge (Fin.last n) (p 7).castSucc = k
      rw [c.symm, castP, ← ht]
      simpa only [pos, endPos] using hedges (pos 7)
    · have old (i : Fin 9) : (v i).val < n :=
        Fin.val_lt_last (fun h => used ⟨i, h⟩)
      apply hbase
      refine ⟨k, fun i => (v i).castLT (old i), ?_, ?_⟩
      · intro i j h
        exact hv (Fin.ext (congrArg (fun a : Fin n => a.val) h))
      · simpa [dropLast] using hedges

/-- Add a vertex with incident edge colors given by `f`. -/
def addLast {n : Nat} (c : Coloring n) (f : Fin n → Fin 3) : Coloring (n+1) where
  edge := Fin.lastCases (Fin.lastCases 0 f) (fun i => Fin.lastCases (f i) (c.edge i))
  symm u v := by
    induction u using Fin.lastCases <;> induction v using Fin.lastCases <;> simp [c.symm]

/-- The open problem reduces exactly to the incompatibility of the three
endpoint conflict relations for each monochromatic-C₉-free coloring of K₃₂. -/
theorem k33_iff_no_compatible_assignment :
    K33Claim ↔ ∀ (c : Coloring 32), (¬ HasMonoC9 c) →
      ∀ f : Fin 32 → Fin 3, ¬ Compatible c f := by
  constructor
  · intro claim c h f hf
    have base : dropLast (addLast c f) = c := by
      cases c with
      | mk edge symm =>
        unfold dropLast addLast
        congr 1
        funext u v
        simp only [Fin.lastCases_castSucc]
    have tip : (fun a : Fin 32 => (addLast c f).edge (Fin.last 32) a.castSucc) = f := by
      funext a
      simp only [addLast, Fin.lastCases_last, Fin.lastCases_castSucc]
    have noCycle := (free_iff_compatible (addLast c f)).2 (by rw [base, tip]; exact ⟨h, hf⟩)
    exact noCycle (claim _)
  · intro impossible c
    apply Classical.byContradiction
    intro h
    obtain ⟨hbase, hf⟩ := (free_iff_compatible c).1 h
    exact impossible (dropLast c) hbase _ hf

end Ramsey556
