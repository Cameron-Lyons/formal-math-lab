import Std

/-! Soundness of branching on the complete neighborhood of one fresh vertex
in a finite induced subgraph. The host graph can have any vertex type. -/
namespace Erdos64

structure Graph (V : Type u) where
  adj : V → V → Prop
  symm : ∀ {x y}, adj x y → adj y x
  loopless : ∀ x, ¬ adj x x

abbrev Adj := Nat → Nat → Bool

def MinDegreeThree {V : Type u} (G : Graph V) : Prop :=
  ∀ x, ∃ y z w, G.adj x y ∧ G.adj x z ∧ G.adj x w ∧ y ≠ z ∧ y ≠ w ∧ z ≠ w

/-- The entries at indices greater than or equal to n are irrelevant. -/
structure Copy {V : Type u} (G : Graph V) (n : Nat) (E : Adj) where
  lab : Nat → V
  inj : ∀ {i j : Nat}, i < n → j < n → lab i = lab j → i = j
  edge : ∀ {i j : Nat}, i < n → j < n → (G.adj (lab i) (lab j) ↔ E i j = true)

def extendAdj (n : Nat) (E : Adj) (m : Nat) : Adj := fun i j =>
  if i = n then if j = n then false else m.testBit j
  else if j = n then m.testBit i else E i j

private theorem freshAvoiding {V : Type u} {G : Graph V} (d : MinDegreeThree G)
    (x y z : V) : ∃ w, G.adj x w ∧ w ≠ y ∧ w ≠ z := by
  obtain ⟨a,b,c,ha,hb,hc,hab,hac,hbc⟩ := d x
  by_cases h : a = y ∨ a = z
  · by_cases k : b = y ∨ b = z
    · exact ⟨c,hc,by grind,by grind⟩
    · exact ⟨b,hb,by grind,by grind⟩
  · exact ⟨a,ha,by grind,by grind⟩

private theorem packBits (b : Nat → Bool) (n : Nat) :
    ∃ m < 2^n, ∀ i < n, m.testBit i = b i := by
  induction n with
  | zero => exact ⟨0,by decide,by omega⟩
  | succ n ih =>
    obtain ⟨m,hm,he⟩ := ih
    cases h : b n with
    | false =>
      refine ⟨m,by rw [Nat.pow_succ]; omega, ?_⟩
      intro i hi
      by_cases e : i = n
      · subst i; simpa [h] using Nat.testBit_lt_two_pow hm
      · exact he i (by omega)
    | true =>
      refine ⟨2^n + m,by rw [Nat.pow_succ]; omega, ?_⟩
      intro i hi
      by_cases e : i = n
      · subst i; simp [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hm, h]
      · rw [Nat.testBit_two_pow_add_gt (by omega : i < n), he i (by omega)]

/-- If at most two labels neighbor the anchor in the induced copy, a third
neighbor exists in the host. Its adjacency to *all* old labels gives one of
the masks considered by the search. -/
theorem extendCopyFixing {V : Type u} {G : Graph V} {n : Nat} {E : Adj}
    (c : Copy G n E) (d : MinDegreeThree G) {a p q : Nat} (ha : a < n)
    (cover : ∀ i : Fin n, E a i.val = true → i.val = p ∨ i.val = q) :
    ∃ m, m < 2^n ∧ m.testBit a = true ∧
      ∃ c' : Copy G (n+1) (extendAdj n E m), ∀ i < n, c'.lab i = c.lab i := by
  classical
  obtain ⟨v,hav,hvp,hvq⟩ := freshAvoiding d (c.lab a) (c.lab p) (c.lab q)
  have fresh : ∀ i < n, c.lab i ≠ v := by
    intro i hi eq
    have h := cover ⟨i,hi⟩ ((c.edge ha hi).mp (eq ▸ hav))
    rcases h with h | h
    · exact hvp (h ▸ eq.symm)
    · exact hvq (h ▸ eq.symm)
  obtain ⟨m, hm, bits⟩ := packBits (fun i => decide (G.adj (c.lab i) v)) n
  let f (i : Nat) := if i = n then v else c.lab i
  refine ⟨m, hm, by simpa [bits a ha] using hav, ⟨f, ?_, ?_⟩, ?_⟩
  · intro i j hi hj h
    by_cases e : i = n <;> by_cases g : j = n
    · omega
    · simp [f,e,g] at h
      exact False.elim (fresh j (by omega) h.symm)
    · simp [f,e,g] at h
      exact False.elim (fresh i (by omega) h)
    · exact c.inj (by omega) (by omega) (by simpa [f,e,g] using h)
  · intro i j hi hj
    by_cases e : i = n <;> by_cases g : j = n
    · simp [f,extendAdj,e,g,G.loopless]
    · simp only [f,extendAdj,e,g,ite_true,ite_false, bits j (by omega),decide_eq_true_eq]
      exact ⟨G.symm,G.symm⟩
    · simp [f,extendAdj,e,g,bits i (by omega)]
    · simpa [f,extendAdj,e,g] using c.edge (i := i) (j := j) (by omega) (by omega)

  · intro i hi
    simp [f,Nat.ne_of_lt hi]

theorem extendCopy {V : Type u} {G : Graph V} {n : Nat} {E : Adj}
    (c : Copy G n E) (d : MinDegreeThree G) {a p q : Nat} (ha : a < n)
    (cover : ∀ i : Fin n, E a i.val = true → i.val = p ∨ i.val = q) :
    ∃ m, m < 2^n ∧ m.testBit a = true ∧ Nonempty (Copy G (n+1) (extendAdj n E m)) := by
  obtain ⟨m,hm,ha',u,_⟩ := extendCopyFixing c d ha cover
  exact ⟨m,hm,ha',⟨u⟩⟩

def pathAdj (k : Nat) : Adj := fun i j =>
  decide (i < k ∧ j < k ∧ (i+1 = j ∨ j+1 = i))

/-- An induced copy of the disjoint union of a path on k vertices and an isolate. -/
def HasPathIso {V : Type u} (G : Graph V) (k : Nat) : Prop :=
  Nonempty (Copy G (k+1) (pathAdj k))

def cycleNext {k : Nat} (i : Fin k) : Fin k :=
  ⟨(i.val + 1) % k, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩

def HasCycle {V : Type u} (G : Graph V) (k : Nat) : Prop :=
  ∃ f : Fin k → V, (∀ i j, f i = f j → i = j) ∧
    ∀ i, G.adj (f i) (f (cycleNext i))

theorem cycleOfIndices {V : Type u} {G : Graph V} {n : Nat} {E : Adj}
    (c : Copy G n E) {k : Nat} (f : Fin k → Fin n)
    (distinct : ∀ i j, f i = f j → i = j)
    (edges : ∀ i, E (f i).val (f (cycleNext i)).val = true) : HasCycle G k := by
  refine ⟨fun i => c.lab (f i).val, ?_, ?_⟩
  · intro i j eq
    exact distinct i j (Fin.ext (c.inj (f i).isLt (f j).isLt eq))
  · intro i
    exact (c.edge (f i).isLt (f (cycleNext i)).isLt).mpr (edges i)

/-- Closing the two ends of an old simple path with the fresh vertex
constructs a simple cycle. Here k is the number of old path edges. -/
theorem cycleThroughFresh {V : Type u} {G : Graph V} {n m : Nat} {E : Adj}
    (c : Copy G (n+1) (extendAdj n E m)) {k : Nat} (f : Nat → Nat)
    (range : ∀ i ≤ k, f i < n)
    (distinct : ∀ i ≤ k, ∀ j ≤ k, f i = f j → i = j)
    (steps : ∀ i < k, E (f i) (f (i+1)) = true)
    (first : m.testBit (f 0) = true) (last : m.testBit (f k) = true) :
    HasCycle G (k+2) := by
  let g (i : Fin (k+2)) : Fin (n+1) :=
    if h : i.val ≤ k then ⟨f i.val, Nat.lt_succ_of_lt (range _ h)⟩ else ⟨n, by omega⟩
  apply cycleOfIndices c g
  · intro i j eq
    apply Fin.ext
    have eq' := congrArg Fin.val eq
    by_cases hi : i.val ≤ k <;> by_cases hj : j.val ≤ k
    · exact distinct _ hi _ hj (by simpa [g,hi,hj] using eq')
    · simp [g,hi,hj] at eq'
      have := range i.val hi
      omega
    · simp [g,hi,hj] at eq'
      have := range j.val hj
      omega
    · have := i.isLt; have := j.isLt; omega
  · intro i
    have hlim := i.isLt
    by_cases hi : i.val < k
    · have hnext : (cycleNext i).val = i.val+1 :=
        Nat.mod_eq_of_lt (by omega)
      have hlo : i.val ≤ k := by omega
      have hne : f i.val ≠ n := Nat.ne_of_lt (range _ hlo)
      have hne' : f (i.val+1) ≠ n := Nat.ne_of_lt (range _ (by omega))
      have hstep : i.val+1 ≤ k := by omega
      simpa [g,hlo,hnext,hstep,extendAdj,hne,hne'] using steps i.val hi
    · by_cases he : i.val = k
      · have hnext : (cycleNext i).val = i.val+1 := Nat.mod_eq_of_lt (by omega)
        have hlo : i.val ≤ k := by omega
        have hhi : ¬ (cycleNext i).val ≤ k := by omega
        have hne : f k ≠ n := Nat.ne_of_lt (range _ (Nat.le_refl _))
        simpa [g,hlo,hhi,he,extendAdj,hne] using last
      · have he' : i.val+1 = k+2 := by omega
        have hnext : (cycleNext i).val = 0 := by simp [cycleNext,he']
        have hlo : ¬ i.val ≤ k := by omega
        have hhi : (cycleNext i).val ≤ k := by omega
        have hne : f 0 ≠ n := Nat.ne_of_lt (range _ (Nat.zero_le _))
        simpa [g,hlo,hhi,hnext,extendAdj,hne] using first

/-- Row j records the neighbors of j among labels less than j. -/
def adjAt (rows : Array Nat) : Adj := fun i j =>
  if i < j then (rows.getD j 0).testBit i
  else if j < i then (rows.getD i 0).testBit j else false

theorem adjAt_push {rows : Array Nat} {m i j : Nat}
    (hi : i < rows.size+1) (hj : j < rows.size+1) :
    adjAt (rows.push m) i j = extendAdj rows.size (adjAt rows) m i j := by
  by_cases ei : i = rows.size <;> by_cases ej : j = rows.size
  · simp [adjAt,extendAdj,ei,ej]
  · have hj' : j < rows.size := by omega
    simp [adjAt,extendAdj,ei,ej,hj',Nat.not_lt_of_ge (Nat.le_of_lt hj')]
  · have hi' : i < rows.size := by omega
    simp [adjAt,extendAdj,ei,ej,hi']
  · simp [adjAt,extendAdj,ei,ej,Array.getElem?_push]

theorem Copy.congr {V : Type u} {G : Graph V} {n : Nat} {E F : Adj}
    (c : Copy G n E) (h : ∀ i < n, ∀ j < n, E i j = F i j) : Nonempty (Copy G n F) :=
  ⟨⟨c.lab, c.inj, fun hi hj => (c.edge hi hj).trans (by rw [h _ hi _ hj])⟩⟩

theorem pushCopy {V : Type u} {G : Graph V} {rows : Array Nat} {m : Nat}
    (c : Copy G (rows.size+1) (extendAdj rows.size (adjAt rows) m)) :
    Nonempty (Copy G (rows.push m).size (adjAt (rows.push m))) := by
  rw [Array.size_push]
  exact c.congr (fun _ hi _ hj => (adjAt_push hi hj).symm)

def HasInducedPath {V : Type u} (G : Graph V) (k : Nat) : Prop :=
  Nonempty (Copy G k (pathAdj k))

theorem pushCopyFixing {V : Type u} {G : Graph V} {rows : Array Nat} {m : Nat}
    (c : Copy G (rows.size+1) (extendAdj rows.size (adjAt rows) m)) :
    ∃ c' : Copy G (rows.push m).size (adjAt (rows.push m)), ∀ i, c'.lab i = c.lab i := by
  rw [Array.size_push]
  refine ⟨⟨c.lab,c.inj,?_⟩,fun _ => rfl⟩
  intro i j hi hj
  simpa only [adjAt_push hi hj] using c.edge hi hj

def DominatesFirst (k : Nat) {V : Type u} {G : Graph V} {n : Nat} {E : Adj}
    (c : Copy G n E) : Prop :=
  ∀ x, (∃ i : Fin k, x = c.lab i.val) ∨ ∃ i : Fin k, G.adj x (c.lab i.val)

def HasDominatingInducedPath {V : Type u} (G : Graph V) (k : Nat) : Prop :=
  ∃ c : Copy G k (pathAdj k), DominatesFirst k c

theorem seedDominates {V : Type u} {G : Graph V} {k : Nat}
    (c : Copy G k (pathAdj k)) (forbid : ¬ HasPathIso G k) :
    DominatesFirst k c := by
  classical
  intro x
  apply Classical.byContradiction
  intro h
  have fresh (i : Nat) (hi : i < k) : x ≠ c.lab i :=
    fun eq => h (Or.inl ⟨⟨i,hi⟩,eq⟩)
  have missing (i : Nat) (hi : i < k) : ¬ G.adj x (c.lab i) :=
    fun edge => h (Or.inr ⟨⟨i,hi⟩,edge⟩)
  apply forbid
  let f (i : Nat) := if i < k then c.lab i else x
  refine ⟨⟨f, ?_, ?_⟩⟩
  · intro i j hi hj eq
    by_cases ei : i < k <;> by_cases ej : j < k
    · exact c.inj ei ej (by simpa [f,ei,ej] using eq)
    · exact False.elim (fresh i ei (by simpa [f,ei,ej] using eq.symm))
    · exact False.elim (fresh j ej (by simpa [f,ei,ej] using eq))
    · omega
  · intro i j hi hj
    by_cases ei : i < k <;> by_cases ej : j < k
    · simpa [f,ei,ej] using c.edge ei ej
    · have nonedge : ¬ G.adj (c.lab i) x := fun e => missing i ei (G.symm e)
      simp [f,ei,ej,pathAdj,nonedge]
    · simp [f,ei,ej,pathAdj,missing j ej]
    · simp [f,ei,ej,pathAdj,G.loopless]

theorem dominatingOfNoPathIso {V : Type u} {G : Graph V} {k : Nat}
    (path : HasInducedPath G k) (forbid : ¬ HasPathIso G k) : HasDominatingInducedPath G k := by
  obtain ⟨c⟩ := path
  exact ⟨c, seedDominates c forbid⟩

theorem DominatesFirst.transfer {V : Type u} {G : Graph V} {k n n' : Nat} {E F : Adj}
    {c : Copy G n E} {c' : Copy G n' F} (dom : DominatesFirst k c)
    (fixes : ∀ i < k, c'.lab i = c.lab i) : DominatesFirst k c' := by
  intro x
  rcases dom x with ⟨i,eq⟩ | ⟨i,e⟩
  · exact Or.inl ⟨i, by simpa only [fixes _ i.isLt] using eq⟩
  · exact Or.inr ⟨i, by simpa only [fixes _ i.isLt] using e⟩

theorem maskMeetsDominatingSeed {V : Type u} {G : Graph V} {k n m : Nat} {E : Adj}
    (c : Copy G (n+1) (extendAdj n E m)) (hlen : k ≤ n) (dom : DominatesFirst k c) :
    ∃ i : Fin k, m.testBit i.val = true := by
  rcases dom (c.lab n) with ⟨i,h⟩ | ⟨i,e⟩
  · have := c.inj (by omega) (by have := i.isLt; omega) h
    have := i.isLt
    omega
  · have hi := i.isLt
    have h := (c.edge (by omega) (by omega)).mp e
    exact ⟨i, by simpa [extendAdj,show i.val ≠ n by omega] using h⟩

end Erdos64
