import Ramsey556.Cert16.Basic
import Ramsey556.Basic

namespace Ramsey556.Split17

/-- Index of a spoke between a vertex below 13 and one of the last four. -/
def spoke (i j : Fin 17) : Nat := 13*(j.val-13)+i.val

private def lowEnd (f : Fin 52) : Fin 17 := ⟨f.val%13, by omega⟩
private def highEnd (f : Fin 52) : Fin 17 := ⟨13+f.val/13, by omega⟩

private def addBit (state : Bool → Nat) (v : Fin 52) (b : Bool) (k : Bool) : Nat :=
  if k=b then state k ||| (1 <<< v.val) else state k

private def vertex (w : Nat) (i : Fin 9) : Fin 17 :=
  ⟨(((w >>> (5*i.val)) % 32) % 17), Nat.mod_lt _ (by decide)⟩

private def marked (g : Nat) (state : Bool → Nat) (k : Bool) (i j : Fin 17) : Bool :=
  if i.val < 13 then
    if j.val < 13 then Cert16.edge g i.val j.val == k else (state k).testBit (spoke i j)
  else if j.val < 13 then (state k).testBit (spoke j i) else false

inductive Trace where
  | cycle (k : Bool) (vertices : Nat)
  | branch (v : Fin 52) (zero one : Trace)

def check (g : Nat) (state : Bool → Nat) : Trace → Bool
  | .cycle k w =>
    decide ((∀ i j, vertex w i = vertex w j → i = j) ∧ ∀ i, marked g state k (vertex w i) (vertex w (i+1)) = true)
  | .branch v z o => check g (addBit state v false) z && check g (addBit state v true) o

private def Agree {n} (c : Coloring n) (v : Fin 17 → Fin n) (color : Bool → Fin 3)
    (state : Bool → Nat) : Prop :=
  ∀ k i j, i.val < 13 → 13 ≤ j.val → (state k).testBit (spoke i j) = true → c.edge (v i) (v j) = color k

private theorem agree_add {n} {c : Coloring n} {v : Fin 17 → Fin n} {color : Bool → Fin 3}
    {state : Bool → Nat} (old : Agree c v color state) (f : Fin 52) (b : Bool)
    (selected : c.edge (v (lowEnd f)) (v (highEnd f)) = color b) : Agree c v color (addBit state f b) := by
  intro k i j lo hi hit
  by_cases eq : k=b
  · subst k
    simp only [addBit,↓reduceIte,Nat.testBit_or,Bool.or_eq_true] at hit
    rcases hit with existing | single
    · exact old _ _ _ lo hi existing
    have same : f.val = spoke i j := by
      apply Classical.byContradiction
      intro ne
      rw [Nat.one_shiftLeft,Nat.testBit_two_pow_of_ne ne] at single
      contradiction
    have a : lowEnd f = i := Fin.ext (by dsimp [lowEnd]; unfold spoke at same; omega)
    have d : highEnd f = j := Fin.ext (by dsimp [highEnd]; unfold spoke at same; omega)
    simpa only [a,d] using selected
  · exact old _ _ _ lo hi (by simpa only [addBit,ite_eq_right eq] using hit)

/-- Each checked leaf gives nine distinct vertices and checks its edges
against the fixed clique and the spokes decided along that branch. -/
theorem trace_sound {n} (c : Coloring n) (v : Fin 17 → Fin n) (color : Bool → Fin 3)
    (inj : ∀ ⦃i j⦄, v i = v j → i=j) (g : Nat)
    (base : ∀ i j : Fin 17, i.val < 13 → j.val < 13 → i ≠ j →
      c.edge (v i) (v j) = color (Cert16.edge g i.val j.val))
    (spokes : ∀ i j : Fin 17, i.val < 13 → 13 ≤ j.val →
      c.edge (v i) (v j) = color false ∨ c.edge (v i) (v j) = color true)
    (t : Trace) (valid : check g (fun _ => 0) t = true) : HasMonoC9 c := by
  have go (state : Bool → Nat) (t : Trace) (h : check g state t = true) (agree : Agree c v color state) :
      HasMonoC9 c := by
    induction t generalizing state with
    | cycle k w =>
      obtain ⟨simple,arcs⟩ := of_decide_eq_true h
      refine ⟨color k,fun i => v (vertex w i),fun {i j} e => simple _ _ (inj e),fun a => ?_⟩
      let i := vertex w a
      let j := vertex w (a+1)
      have ne : i ≠ j := fun e => (show ∀ t : Fin 9, t ≠ t+1 by decide) a (simple _ _ e)
      have hr : marked g state k i j = true := arcs a
      change c.edge (v i) (v j) = color k
      by_cases hi : i.val<13
      · by_cases hj : j.val<13
        · have edge : Cert16.edge g i.val j.val=k := by simpa [marked,hi,hj] using hr
          exact (base i j hi hj ne).trans (congrArg color edge)
        · exact agree _ _ _ hi (by omega) (by simpa [marked,hi,hj] using hr)
      · by_cases hj : j.val<13
        · exact (c.symm _ _).trans (agree _ _ _ hj (by omega) (by simpa [marked,hi,hj] using hr))
        · simp [marked,hi,hj] at hr
    | branch f z o iz io =>
      obtain ⟨hz,ho⟩ := Bool.and_eq_true_iff.mp h
      rcases spokes (lowEnd f) (highEnd f) (by dsimp [lowEnd]; omega) (by simp [highEnd]) with h | h
      · exact iz _ hz (agree_add agree f false h)
      · exact io _ ho (agree_add agree f true h)
  exact go _ t valid (by intro k i j h1 h2 bit; simp at bit)

end Ramsey556.Split17
