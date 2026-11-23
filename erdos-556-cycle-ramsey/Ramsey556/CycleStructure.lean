import Ramsey556.Basic

namespace Ramsey556

/-- An eight-edge path with different vertices and specified endpoints. -/
def HasPath8In {n} (c : Coloring n) (k : Fin 3) (x y : Fin n) : Prop :=
  ∃ p : Fin 9 → Fin n, (∀ ⦃i j⦄, p i = p j → i = j) ∧ p 0 = x ∧ p 8 = y ∧
    ∀ i : Fin 8, c.edge (p i.castSucc) (p i.succ) = k

/-- For every edge, each color earlier than its own joins its endpoints by
a simple path of length eight. Red is 0, blue is 1, and green is 2. -/
def PathSaturated {n} (c : Coloring n) : Prop :=
  ∀ x y, x ≠ y → ∀ k, k < c.edge x y → HasPath8In c k x y

/-- Two vertices belong to the same connected component of one color. -/
inductive ColorJoined {n} (c : Coloring n) (k : Fin 3) : Fin n → Fin n → Prop where
  | refl (x) : ColorJoined c k x x
  | edge {x y} : c.edge x y = k → ColorJoined c k x y
  | trans {x y z} : ColorJoined c k x y → ColorJoined c k y z → ColorJoined c k x z

theorem ColorJoined.symm {n c k} {x y : Fin n} (h : ColorJoined c k x y) : ColorJoined c k y x := by
  induction h with
  | refl x => exact .refl x
  | edge e => exact .edge ((c.symm _ _).trans e)
  | trans _ _ a b => exact .trans b a

theorem HasPath8In.joined {n c k} {x y : Fin n} (h : HasPath8In c k x y) : ColorJoined c k x y := by
  obtain ⟨p,_,rfl,rfl,edges⟩ := h
  have go (i : Nat) (hi : i < 9) : ColorJoined c k (p 0) (p ⟨i,hi⟩) := by
    induction i with
    | zero => exact .refl _
    | succ j ih => exact .trans (ih (by omega)) (.edge (edges ⟨j,by omega⟩))
  exact go 8 (by decide)

/-- The edge joining the endpoints of a simple eight-edge path closes C₉. -/
theorem HasPath8In.close {n} {c : Coloring n} {k : Fin 3} {x y : Fin n}
    (h : HasPath8In c k x y) (e : c.edge x y = k) : HasMonoC9 c := by
  obtain ⟨p,pi,rfl,rfl,he⟩ := h
  refine ⟨k,p,@pi,fun i => ?_⟩
  by_cases last : i = 8
  · subst i
    exact (c.symm _ _).trans e
  · let j : Fin 8 := ⟨i.val,by omega⟩
    have a : j.castSucc = i := Fin.ext rfl
    have b : j.succ = i+1 :=
      (show ∀ q : Fin 8, q.succ = q.castSucc+1 by decide) j |>.trans (congrArg (· + 1) a)
    rw [← a, ← (show j.succ = j.castSucc + 1 by rw [a,b])]
    exact he j

/-- In the saturated form, the color of every edge is the first color in
which its endpoints have no eight-edge simple path. -/
theorem PathSaturated.edge_iff {n} {c : Coloring n} (sat : PathSaturated c) (free : ¬ HasMonoC9 c)
    {x y : Fin n} (ne : x ≠ y) (k : Fin 3) :
    c.edge x y = k ↔ (∀ q, q < k → HasPath8In c q x y) ∧ ¬ HasPath8In c k x y := by
  constructor
  · rintro rfl
    exact ⟨sat x y ne, fun h => free (h.close rfl)⟩
  · rintro ⟨earlier,absent⟩
    by_cases before : c.edge x y < k
    · exact (free ((earlier _ before).close rfl)).elim
    by_cases after : k < c.edge x y
    · exact (absent (sat _ _ ne k after)).elim
    exact Fin.ext (by omega)

namespace CycleStructure

def samePair {n} (x y a b : Fin n) : Prop := (a=x ∧ b=y) ∨ (a=y ∧ b=x)
instance {n} (x y a b : Fin n) : Decidable (samePair x y a b) :=
  inferInstanceAs (Decidable ((_ ∧ _) ∨ (_ ∧ _)))

def paint {n} (c : Coloring n) (x y : Fin n) (k : Fin 3) : Coloring n where
  edge a b := if samePair x y a b then k else c.edge a b
  symm a b := by
    have flip : samePair x y a b ↔ samePair x y b a := by
      unfold samePair
      exact ⟨fun h => h.elim (fun e => Or.inr e.symm) (fun e => Or.inl e.symm),
        fun h => h.elim (fun e => Or.inr e.symm) (fun e => Or.inl e.symm)⟩
    simp only [flip, c.symm a b]

private def edges (n : Nat) : List (Fin n × Fin n) :=
  (List.finRange n).flatMap fun a => ((List.finRange n).filter (a < ·)).map fun b => (a,b)

private def weight {n} (c : Coloring n) (es : List (Fin n × Fin n)) : Nat :=
  (es.map (fun (a,b) => (c.edge a b).val)).sum

private theorem weight_paint {n} (c : Coloring n) (x y : Fin n) (k : Fin 3) (lt : k < c.edge x y)
    (es : List (Fin n × Fin n)) :
    weight (paint c x y k) es ≤ weight c es ∧
    ((∃ e ∈ es, samePair x y e.1 e.2) → weight (paint c x y k) es < weight c es) := by
  induction es with
  | nil => simp [weight]
  | cons e es ih =>
    obtain ⟨a,b⟩ := e
    simp only [weight, List.map_cons, List.sum_cons] at *
    by_cases hit : samePair x y a b
    · have earlier : k.val < (c.edge a b).val := by
        rcases hit with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact lt
        · change k < c.edge a b
          rwa [c.symm] at lt
      have value : (paint c x y k).edge a b = k := by simp [paint,hit]
      rw [value]
      omega
    · have value : (paint c x y k).edge a b = c.edge a b := by simp [paint,hit]
      rw [value]
      refine ⟨Nat.add_le_add_left ih.1 _, ?_⟩
      rintro ⟨u,hu,good⟩
      rw [List.mem_cons] at hu
      rcases hu with rfl | hu
      · exact (hit good).elim
      · exact Nat.add_lt_add_left (ih.2 ⟨u,hu,good⟩) _

private theorem weight_strict {n} (c : Coloring n) (x y : Fin n) (hne : x ≠ y)
    {k : Fin 3} (lt : k < c.edge x y) :
    weight (paint c x y k) (edges n) < weight c (edges n) := by
  apply (weight_paint c x y k lt _).2
  have mem (a b : Fin n) (hab : a < b) : (a,b) ∈ edges n := by
    apply List.mem_flatMap.mpr
    refine ⟨a, List.mem_finRange _, List.mem_map.mpr ⟨b, ?_, rfl⟩⟩
    simp [hab]
  by_cases h : x < y
  · exact ⟨(x,y), mem _ _ h, Or.inl ⟨rfl,rfl⟩⟩
  · exact ⟨(y,x), mem _ _ (by omega), Or.inr ⟨rfl,rfl⟩⟩

private def reverseIndex (i : Fin 9) : Fin 9 := ⟨8-i.val, by omega⟩

private theorem path_symm {n} {c : Coloring n} {k : Fin 3} {x y : Fin n}
    (h : HasPath8In c k x y) : HasPath8In c k y x := by
  obtain ⟨p,inj,h0,h8,he⟩ := h
  refine ⟨fun i => p (reverseIndex i), fun {i j} e => ?_, h8,h0, ?_⟩
  · exact (show ∀ i j, reverseIndex i = reverseIndex j → i = j by decide) i j (inj e)
  · intro i
    let j : Fin 8 := ⟨7-i.val, by omega⟩
    have hs : reverseIndex i.castSucc = j.succ := Fin.ext (by dsimp [reverseIndex,j]; omega)
    have ht : reverseIndex i.succ = j.castSucc := Fin.ext (by dsimp [reverseIndex,j]; omega)
    change c.edge (p (reverseIndex i.castSucc)) (p (reverseIndex i.succ)) = k
    rw [hs,ht,c.symm]
    exact he j

private def rot (j i : Fin 9) := j+1+i

/-- When changing one edge creates a nine-cycle, deleting that edge from
the cycle leaves an eight-edge path in the original coloring. -/
theorem path_of_paint {n} {c : Coloring n} (free : ¬ HasMonoC9 c) {x y : Fin n} {k : Fin 3}
    (new : HasMonoC9 (paint c x y k)) : HasPath8In c k x y := by
  obtain ⟨s,p,inj,he⟩ := new
  have use : ∃ j, samePair x y (p j) (p (j+1)) := by
    apply Classical.byContradiction
    intro miss
    apply free
    refine ⟨s,p,@inj, fun i => ?_⟩
    have h : ¬ samePair x y (p i) (p (i+1)) := fun e => miss ⟨i,e⟩
    simpa [paint,h] using he i
  obtain ⟨j,js⟩ := use
  have sk : k=s := by simpa [paint,js] using he j
  subst s
  have injRot : ∀ j a b, rot j a = rot j b → a=b := by decide
  have last : ∀ j, rot j 8 = j := by decide
  have first : ∀ j, rot j 0 = j+1 := by decide
  have step : ∀ j (i : Fin 8), rot j i.succ = rot j i.castSucc + 1 := by decide
  have uniqueEdge : ∀ j (i : Fin 8), rot j i.castSucc ≠ j ∧
      ¬ (rot j i.castSucc = j+1 ∧ rot j i.succ = j) := by decide
  have path : HasPath8In c k (p (j+1)) (p j) := by
    refine ⟨fun i => p (rot j i), fun {a b} e => injRot j _ _ (inj e),
      congrArg p (first j), congrArg p (last j), fun i => ?_⟩
    have miss : ¬ samePair x y (p (rot j i.castSucc)) (p (rot j i.succ)) := by
      rcases js with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> intro hit
      · rcases hit with ⟨a,b⟩ | ⟨a,b⟩
        · exact (uniqueEdge j i).1 (inj (a.trans h1.symm))
        · exact (uniqueEdge j i).2 ⟨inj (a.trans h2.symm), inj (b.trans h1.symm)⟩
      · rcases hit with ⟨a,b⟩ | ⟨a,b⟩
        · exact (uniqueEdge j i).2 ⟨inj (a.trans h2.symm), inj (b.trans h1.symm)⟩
        · exact (uniqueEdge j i).1 (inj (a.trans h1.symm))
    have edge := he (rot j i.castSucc)
    rw [← step j i] at edge
    simpa [paint,miss] using edge
  rcases js with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact path_symm path
  · exact path

private theorem minimum_weight {n} (allowed : Coloring n → Prop) (c : Coloring n)
    (valid : allowed c) (free : ¬ HasMonoC9 c) :
    ∃ d : Coloring n, allowed d ∧ (¬ HasMonoC9 d) ∧ ∀ e : Coloring n, allowed e → (¬ HasMonoC9 e) →
      weight d (edges n) ≤ weight e (edges n) := by
  generalize eq : weight c (edges n) = w
  induction w using Nat.strongRecOn generalizing c with
  | ind w ih =>
    classical
    by_cases least : ∀ e : Coloring n, allowed e → (¬ HasMonoC9 e) → w ≤ weight e (edges n)
    · exact ⟨c,valid,free,eq ▸ least⟩
    simp only [Classical.not_forall] at least
    obtain ⟨e,he,ef,lower⟩ := least
    exact ih _ (by omega : weight e (edges n) < w) e he ef rfl

private theorem saturated_of_minimum {n} {allowed : Coloring n → Prop} {d : Coloring n}
    (free : ¬ HasMonoC9 d)
    (least : ∀ e : Coloring n, allowed e → (¬ HasMonoC9 e) → weight d (edges n) ≤ weight e (edges n))
    (x y : Fin n) (ne : x ≠ y) (k : Fin 3) (lt : k < d.edge x y) (hp : allowed (paint d x y k)) :
    HasPath8In d k x y := by
  apply path_of_paint free
  apply Classical.byContradiction
  intro other
  exact Nat.not_lt_of_ge (least _ hp other) (weight_strict d x y ne lt)

/-- Minimize the sum of the edge colors among counterexamples satisfying
a specified constraint. Any repaint to an earlier color which preserves the
constraint must complete a nine-cycle. -/
theorem saturated_within {n} (allowed : Coloring n → Prop) (c : Coloring n)
    (valid : allowed c) (free : ¬ HasMonoC9 c) :
    ∃ d : Coloring n, allowed d ∧ (¬ HasMonoC9 d) ∧ ∀ x y, x ≠ y → ∀ k, k < d.edge x y →
      allowed (paint d x y k) → HasPath8In d k x y := by
  obtain ⟨d,dv,df,h⟩ := minimum_weight allowed c valid free
  exact ⟨d,dv,df,saturated_of_minimum df h⟩

/-- Any counterexample can be replaced by one in which each non-red edge
is closed by an eight-edge red path, and each green edge also by a blue one. -/
theorem saturated_counterexample {n} (c : Coloring n) (free : ¬ HasMonoC9 c) :
    ∃ d : Coloring n, (¬ HasMonoC9 d) ∧ PathSaturated d := by
  obtain ⟨d,_,df,sat⟩ := saturated_within (fun _ => True) c trivial free
  exact ⟨d,df,fun x y ne k lt => sat x y ne k lt trivial⟩

private def count {n} (c : Coloring n) (k : Fin 3) (es : List (Fin n × Fin n)) :=
  es.countP (fun e => c.edge e.1 e.2 == k)

/-- Number of undirected edges of color k, counting each pair once. -/
def tally {n} (c : Coloring n) (k : Fin 3) := count c k (edges n)

private def swap (i j k : Fin 3) := if k=i then j else if k=j then i else k

private theorem swap_weight {n} (c : Coloring n) (i j : Fin 3) (adj : i.val+1=j.val)
    (es : List (Fin n × Fin n)) :
    weight (c.recolor (swap i j)) es + count c j es = weight c es + count c i es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    obtain ⟨a,b⟩ := e
    simp only [weight,List.map_cons,List.sum_cons,count,List.countP_cons] at *
    have he : (c.recolor (swap i j)).edge a b = swap i j (c.edge a b) := rfl
    rw [he]
    by_cases h : c.edge a b = i
    · simp [h,swap,show i≠j by omega]; omega
    · by_cases hj : c.edge a b = j
      · simp [hj,swap,show j≠i by omega]; omega
      · simp [swap,h,hj]; omega

private theorem free_swap {n} {c : Coloring n} (free : ¬ HasMonoC9 c) (i j : Fin 3) :
    ¬ HasMonoC9 (c.recolor (swap i j)) := by
  have inj : ∀ i j u v : Fin 3, swap i j u = swap i j v → u = v := by decide
  exact fun h => free (hasMonoC9_of_copy c id _ (fun {_ _} e => e) (fun {_ _} e => inj i j _ _ e) h)

theorem tally_total (c : Coloring 33) : tally c 0 + tally c 1 + tally c 2 = 528 := by
  have add (es : List (Fin 33 × Fin 33)) : count c 0 es + count c 1 es + count c 2 es = es.length := by
    induction es with
    | nil => rfl
    | cons e es ih =>
      obtain ⟨a,b⟩ := e
      have cases : c.edge a b=0 ∨ c.edge a b=1 ∨ c.edge a b=2 := by omega
      rcases cases with h|h|h <;> simp [count,h] at * <;> omega
  exact (add _).trans (by decide +kernel : (edges 33).length=528)

/-- One can require the saturated colors to be ordered by their edge
counts. In particular the saturated red graph has at least 176 edges. -/
theorem ordered_saturated_counterexample (c : Coloring 33) (free : ¬ HasMonoC9 c) :
    ∃ d : Coloring 33, (¬ HasMonoC9 d) ∧ PathSaturated d ∧
      176 ≤ tally d 0 ∧ tally d 2 ≤ tally d 1 ∧ tally d 1 ≤ tally d 0 := by
  obtain ⟨d,_,df,least⟩ := minimum_weight (fun _ => True) c trivial free
  have order {i j : Fin 3} (adj : i.val+1=j.val) : tally d j ≤ tally d i := by
    have eq := swap_weight d i j adj (edges 33)
    have := least _ trivial (free_swap df i j)
    unfold tally
    omega
  have a := order (i := 0) (j := 1) rfl
  have b := order (i := 1) (j := 2) rfl
  have tot := tally_total d
  exact ⟨d,df,fun x y ne k lt => saturated_of_minimum df least x y ne k lt trivial,by omega,b,a⟩

end CycleStructure

end Ramsey556
