import Erdos64.ExtensionSoundness

/-! A finite graph of pathwidth at most three and minimum degree at least three
has a simple cycle of length four or eight. We use the vertex-separation
characterization of pathwidth. -/
namespace Erdos64

/-- A finite vertex order witnessing vertex separation at most three. At every
cut at most three earlier vertices have an edge to a later vertex. Values of
`vertex` outside the first `size` positions have no significance. -/
structure WidthThreeOrder {V : Type u} (G : Graph V) where
  size : Nat
  vertex : Nat → V
  inj : ∀ i < size, ∀ j < size, vertex i = vertex j → i = j
  covers : ∀ x, ∃ i < size, vertex i = x
  width : ∀ cut ≤ size, ∃ bag : List Nat, bag.length ≤ 3 ∧
    ∀ i < cut, ∀ j, cut ≤ j → j < size → G.adj (vertex i) (vertex j) → i ∈ bag

namespace Pathwidth

private abbrev Board := Array (List Nat)

/-- Store each edge in the row of its later endpoint. -/
private def edge (b : Board) (i j : Nat) : Bool :=
  if i < j then (b.getD j []).contains i
  else if j < i then (b.getD i []).contains j else false

private def threeNeighbors (b : Board) (i : Nat) : Bool :=
  decide (3 ≤ ((List.range b.size).filter (edge b i)).length)

/-- Try a simple cycle through the vertex most recently introduced. An
independent check below validates the full list before a branch is closed. -/
private def findCycle (b : Board) (start : Nat) : Nat → Nat → List Nat → Option (List Nat)
  | 0, tip, used => if edge b tip start then some used else none
  | r+1, tip, used => (List.range b.size).findSome? fun w =>
    if edge b tip w && !used.contains w then findCycle b start r w (w :: used)
    else none

private def validCycle (b : Board) (k : Nat) (v : Array Nat) : Bool :=
  decide ((∀ i : Fin k, v.getD i.val 0 < b.size) ∧
    (∀ i j : Fin k, v.getD i.val 0 = v.getD j.val 0 → i = j) ∧
    (∀ i : Fin k, edge b (v.getD i.val 0) (v.getD (cycleNext i).val 0) = true))

private def foundCycle (b : Board) (k : Nat) : Bool :=
  let start := b.size - 1
  match findCycle b start (k-1) start [start] with
  | none => false
  | some v => validCycle b k v.toArray

private theorem foundCycle_sound {V : Type u} {G : Graph V} {b : Board}
    (c : Copy G b.size (edge b)) {k : Nat} (h : foundCycle b k = true) :
    HasCycle G k := by
  simp only [foundCycle] at h
  split at h
  · contradiction
  next p _ =>
    obtain ⟨rg,inj,steps⟩ := of_decide_eq_true h
    apply cycleOfIndices c (fun i => ⟨p.toArray.getD i.val 0, rg i⟩)
    · intro i j e
      exact inj i j (congrArg Fin.val e)
    · exact steps

/-- Enumerate subsets of the current bag by including or excluding each entry. -/
private def allChoices (test : List Nat → Bool) : List Nat → Bool
  | [] => test []
  | x :: xs => allChoices test xs && allChoices (fun ys => test (x :: ys)) xs

private theorem allChoices_filter {test : List Nat → Bool} {xs : List Nat}
    (p : Nat → Bool) (h : allChoices test xs = true) : test (xs.filter p) = true := by
  induction xs generalizing test with
  | nil => exact h
  | cons x xs ih =>
    obtain ⟨skip,take⟩ := Bool.and_eq_true_iff.mp h
    cases hp : p x with
    | false => simpa [hp] using ih skip
    | true => simpa [hp] using ih take

/-- A successful return rules out a terminal graph and every possible next
vertex. With four vertices in the bag, every choice of a vertex that has
already acquired three neighbors is tried as the vertex to forget. -/
private def closes : Nat → Board → List Nat → Bool
  | 0, _, _ => false
  | fuel+1, b, bag =>
    (b.isEmpty || bag.any (fun i => !threeNeighbors b i)) &&
    allChoices (fun ns =>
      let next := b.push ns
      let larger := b.size :: bag
      foundCycle next 4 || foundCycle next 8 ||
        (if larger.length ≤ 3 then closes fuel next larger
         else larger.all fun v => !threeNeighbors next v || closes fuel next (larger.erase v)))
      bag

private theorem closed : closes 11 #[] [] = true := by native_decide

variable {V : Type u} {G : Graph V}

private def Matches (o : WidthThreeOrder G) (b : Board) : Prop :=
  ∀ i < b.size, ∀ j < b.size, G.adj (o.vertex i) (o.vertex j) ↔ edge b i j = true

private def Live (o : WidthThreeOrder G) (cut i : Nat) : Prop :=
  i < cut ∧ ∃ j, cut ≤ j ∧ j < o.size ∧ G.adj (o.vertex i) (o.vertex j)

private theorem appendMatches {o : WidthThreeOrder G} {b : Board} {ns : List Nat}
    (matchOld : Matches o b)
    (neighbors : ∀ i < b.size, i ∈ ns ↔ G.adj (o.vertex i) (o.vertex b.size)) :
    Matches o (b.push ns) := by
  intro i hi j hj
  simp only [Array.size_push] at hi hj
  by_cases ei : i = b.size <;> by_cases ej : j = b.size
  · subst i; subst j; simp [edge,G.loopless]
  · subst i
    have lt : j < b.size := by omega
    simpa [edge,lt,Nat.not_lt_of_ge (Nat.le_of_lt lt), Array.getElem?_push] using
      (show G.adj (o.vertex b.size) (o.vertex j) ↔ j ∈ ns from
        ⟨fun e => (neighbors j lt).2 (G.symm e), fun m => G.symm ((neighbors j lt).1 m)⟩)
  · subst j
    have lt : i < b.size := by omega
    simpa [edge,lt,Array.getElem?_push] using (neighbors i lt).symm
  · have ilt : i < b.size := by omega
    have jlt : j < b.size := by omega
    simpa [edge, Array.getElem?_push,ilt,jlt,ei,ej] using matchOld i ilt j jlt

/-- A vertex with no neighbor beyond the cut has acquired its three neighbors
inside the board. -/
private theorem degreeWhenClosed {o : WidthThreeOrder G} {b : Board}
    (agrees : Matches o b) (d : MinDegreeThree G) {i : Nat} (hi : i < b.size)
    (dead : ¬ Live o b.size i) : threeNeighbors b i = true := by
  obtain ⟨x,y,z,hx,hy,hz,hxy,hxz,hyz⟩ := d (o.vertex i)
  obtain ⟨a,ha,rfl⟩ := o.covers x
  obtain ⟨e,he,rfl⟩ := o.covers y
  obtain ⟨c,hc,rfl⟩ := o.covers z
  have inside (j : Nat) (hj : j < o.size) (h : G.adj (o.vertex i) (o.vertex j)) :
      j ∈ (List.range b.size).filter (edge b i) := by
    have lt : j < b.size := by
      apply Classical.byContradiction
      intro outside
      exact dead ⟨hi,j,by omega,hj,h⟩
    exact List.mem_filter.mpr ⟨List.mem_range.mpr lt,(agrees _ hi _ lt).1 h⟩
  have nd : [a,e,c].Nodup := by simp; grind
  apply decide_eq_true
  exact nd.length_le_of_subset (by
    intro j mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl | rfl | rfl
    · exact inside _ ha hx
    · exact inside _ he hy
    · exact inside _ hc hz)

private theorem sound (o : WidthThreeOrder G) (d : MinDegreeThree G) (pos : 0 < o.size)
    (absent : ¬ (HasCycle G 4 ∨ HasCycle G 8)) (fuel : Nat) (b : Board) (bag : List Nat)
    (le : b.size ≤ o.size) (agrees : Matches o b)
    (range : ∀ i ∈ bag, i < b.size) (nd : bag.Nodup)
    (live : ∀ i, Live o b.size i → i ∈ bag) (closedHere : closes fuel b bag = true) : False := by
  classical
  induction fuel generalizing b bag with
  | zero => contradiction
  | succ fuel ih =>
    obtain ⟨unfinished, children⟩ := Bool.and_eq_true_iff.mp closedHere
    have lt : b.size < o.size := by
      apply Classical.byContradiction
      intro ge
      have eq : b.size = o.size := by omega
      have ne : b.isEmpty = false := by simp [Array.isEmpty,eq]; omega
      rw [ne,Bool.false_or] at unfinished
      obtain ⟨i,mem,bad⟩ := List.any_eq_true.mp unfinished
      have good := degreeWhenClosed agrees d (range i mem) (by
        intro ⟨_,j,lo,hi,_⟩; omega)
      simp [good] at bad
    let pred := fun i => decide (G.adj (o.vertex i) (o.vertex b.size))
    let ns := bag.filter pred
    let next := b.push ns
    let larger := b.size :: bag
    have nextMatches : Matches o next := appendMatches agrees (by
      intro i hi
      have h : G.adj (o.vertex i) (o.vertex b.size) → i ∈ bag :=
        fun e => live i ⟨hi,b.size,Nat.le_refl _,lt,e⟩
      simpa [ns,pred] using h)
    have child := allChoices_filter pred children
    change (foundCycle next 4 || foundCycle next 8 ||
      (if larger.length ≤ 3 then closes fuel next larger
       else larger.all fun v => !threeNeighbors next v || closes fuel next (larger.erase v))) = true at child
    have nextSize : next.size = b.size + 1 := by simp [next]
    have nextLe : next.size ≤ o.size := by omega
    have copy : Copy G next.size (edge next) :=
      ⟨o.vertex,fun hi hj e => o.inj _ (by omega) _ (by omega) e,fun hi hj => nextMatches _ hi _ hj⟩
    have c4 : foundCycle next 4 = false := Bool.eq_false_iff.mpr fun h =>
      absent (Or.inl (foundCycle_sound copy h))
    have c8 : foundCycle next 8 = false := Bool.eq_false_iff.mpr fun h =>
      absent (Or.inr (foundCycle_sound copy h))
    rw [c4,c8] at child
    simp only [Bool.false_or] at child
    have newRange : ∀ i ∈ larger, i < next.size := by
      intro i h
      rcases List.mem_cons.mp h with e | h
      · omega
      · have := range _ h; omega
    have newNd : larger.Nodup := List.nodup_cons.mpr ⟨fun h => Nat.lt_irrefl _ (range _ h),nd⟩
    have newLive : ∀ i, Live o next.size i → i ∈ larger := by
      intro i ⟨hi,j,lo,hj,e⟩
      by_cases eq : i = b.size
      · exact List.mem_cons.mpr (Or.inl eq)
      · exact List.mem_cons.mpr (Or.inr (live i ⟨by omega,j,by omega,hj,e⟩))
    split at child
    · exact ih next larger nextLe nextMatches newRange newNd newLive child
    next big =>
      obtain ⟨cover,len,covered⟩ := o.width next.size nextLe
      have gap : ¬ larger ⊆ cover := fun sub => big (Nat.le_trans (newNd.length_le_of_subset sub) len)
      obtain ⟨v,mem,missing⟩ : ∃ v ∈ larger, v ∉ cover := by
        apply Classical.byContradiction
        intro no
        exact gap (fun x hx => Classical.byContradiction (fun hy => no ⟨x,hx,hy⟩))
      have dead : ¬ Live o next.size v := fun ⟨hi,j,lo,hj,e⟩ => missing (covered _ hi _ lo hj e)
      have good := degreeWhenClosed nextMatches d (newRange _ mem) dead
      have sub := List.all_eq_true.mp child v mem
      simp only [good,Bool.not_true,Bool.false_or] at sub
      exact ih next (larger.erase v) nextLe nextMatches
        (fun i h => newRange i (List.mem_of_mem_erase h)) (newNd.erase v)
        (fun i hi => (List.mem_erase_of_ne (show i ≠ v from fun e => dead (e ▸ hi))).mpr (newLive i hi)) sub

end Pathwidth

/-- Every nonempty finite simple graph of pathwidth at most three and minimum
degree at least three has a simple cycle of length four or eight. -/
theorem cycle_of_pathwidth_atMost_three {V : Type u} [Nonempty V] {G : Graph V}
    (order : WidthThreeOrder G) (d : MinDegreeThree G) : HasCycle G 4 ∨ HasCycle G 8 := by
  apply Classical.byContradiction
  intro absent
  obtain ⟨i,hi,_⟩ := order.covers (Classical.ofNonempty : V)
  exact Pathwidth.sound order d (by omega) absent 11 #[] [] (by simp)
    (by intro i hi; simp at hi) (by simp) (by simp) (by intro i h; have := h.1; simp at this)
    Pathwidth.closed

end Erdos64
