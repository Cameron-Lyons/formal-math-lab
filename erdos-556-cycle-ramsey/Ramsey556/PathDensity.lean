import Ramsey556.Dense16Deletion

namespace Ramsey556.PathDensity

/-- A simple path of length l-1 in the indicated vertex set. Indices outside
the path may take arbitrary values. -/
structure Path {α : Type} (r : α → α → Bool) (xs : List α) (l : Nat) where
  vertex : Nat → α
  mem : ∀ i, i<l → vertex i ∈ xs
  inj : ∀ i j, i<l → j<l → vertex i=vertex j → i=j
  edges : ∀ i, i+1<l → r (vertex i) (vertex (i+1)) = true

private def Path.onSubset {α r xs ys l} (p : @Path α r xs l) (h : ∀ a ∈ xs, a ∈ ys) : Path r ys l :=
  ⟨p.vertex,fun i hi => h _ (p.mem i hi),p.inj,p.edges⟩

private def Path.prepend {α r xs l} (p : @Path α r xs l) (z : α) (mem : z ∈ xs)
    (away : ∀ i, i<l → p.vertex i≠z) (edge : r z (p.vertex 0) = true) : Path r xs (l+1) where
  vertex i := if i=0 then z else p.vertex (i-1)
  mem i hi := by split; exact mem; exact p.mem _ (by omega)
  inj i j hi hj eq := by
    split at eq <;> split at eq
    · omega
    · exact (away _ (by omega) eq.symm).elim
    · exact (away _ (by omega) eq).elim
    · have := p.inj _ _ (by omega) (by omega) eq; omega
  edges i hi := by
    by_cases h : i=0
    · simpa [h] using edge
    · simpa [h,Nat.sub_add_cancel (by omega : 1≤i)] using p.edges (i-1) (by omega)

private def Path.reverse {α r xs l} (sym : ∀ i j, r i j = r j i) (p : @Path α r xs l) :
    Path r xs l where
  vertex i := p.vertex (l-1-i)
  mem _ hi := p.mem _ (by omega)
  inj _ _ hi hj e := by have := p.inj _ _ (by omega) (by omega) e; omega
  edges i hi := by
    rw [sym]
    have e := p.edges (l-1-(i+1)) (by omega)
    simpa [show l-1-(i+1)+1=l-1-i by omega] using e

private def perm (l cut j : Nat) := if j≤cut then j else l+cut-j
private def around (l cut start step : Nat) := perm l cut ((perm l cut start + step)%l)

/-- Traverse both subpaths obtained from the cut, reversing the second one. -/
private theorem order_start : ∀ l c z : Fin 8, c.val+1<l.val → z.val<l.val →
    around l c z 0=z.val := by decide +kernel

private theorem order_bound : ∀ l c z j : Fin 8, c.val+1<l.val → z.val<l.val → j.val<l.val →
    around l c z j<l.val := by decide +kernel

private theorem order_inj : ∀ l c z j k : Fin 8, c.val+1<l.val → z.val<l.val →
    j.val<l.val → k.val<l.val → around l c z j=around l c z k → j=k := by decide +kernel

private theorem order_edges : ∀ l c z j : Fin 8, c.val+1<l.val → z.val<l.val → j.val+1<l.val →
    let a := around l c z j
    let b := around l c z (j.val+1)
    a+1=b ∨ b+1=a ∨ (a=c.val ∧ b=l.val-1) ∨ (b=c.val ∧ a=l.val-1) ∨
      (a=0 ∧ b=c.val+1) ∨ (b=0 ∧ a=c.val+1) := by decide +kernel

private theorem cycle_path {α r xs l} (sym : ∀ i j, r i j=r j i) (p : @Path α r xs l) (small : l≤7)
    {cut start} (hc : cut+1<l) (hz : start<l)
    (a : r (p.vertex 0) (p.vertex (cut+1)) = true) (b : r (p.vertex cut) (p.vertex (l-1)) = true) :
    ∃ q : Path r xs l, q.vertex 0=p.vertex start ∧ ∀ i, i<l → ∃ j, j<l ∧ q.vertex i=p.vertex j := by
  let L : Fin 8 := ⟨l,by omega⟩
  let C : Fin 8 := ⟨cut,by omega⟩
  let Z : Fin 8 := ⟨start,by omega⟩
  let index := around l cut start
  have bounded (i) (hi : i<l) : index i<l := order_bound L C Z ⟨i,by omega⟩ hc hz hi
  let q : Path r xs l := {
    vertex := fun i => p.vertex (index i)
    mem := fun i hi => p.mem _ (bounded i hi)
    inj := fun i j hi hj eq => congrArg Fin.val (order_inj L C Z ⟨i,by omega⟩ ⟨j,by omega⟩ hc hz hi hj
      (p.inj _ _ (bounded i hi) (bounded j hj) eq))
    edges := by
      intro i hi
      have ord := order_edges L C Z ⟨i,by omega⟩ hc hz hi
      change index i+1=index (i+1) ∨ index (i+1)+1=index i ∨ _ at ord
      rcases ord with h|h|⟨h,k⟩|⟨h,k⟩|⟨h,k⟩|⟨h,k⟩
      · rw [←h]; exact p.edges _ (h ▸ bounded _ hi)
      · rw [←h,sym]; exact p.edges _ (h ▸ bounded _ (by omega))
      · exact (show r (p.vertex (around L C Z i)) (p.vertex (around L C Z (i+1))) = true by rw [h,k]; exact b)
      · exact (show r (p.vertex (around L C Z i)) (p.vertex (around L C Z (i+1))) = true by rw [h,k,sym]; exact b)
      · exact (show r (p.vertex (around L C Z i)) (p.vertex (around L C Z (i+1))) = true by rw [h,k]; exact a)
      · exact (show r (p.vertex (around L C Z i)) (p.vertex (around L C Z (i+1))) = true by rw [h,k,sym]; exact a)
  }
  exact ⟨q,congrArg p.vertex (order_start L C Z hc hz),fun i hi => ⟨_,bounded i hi,rfl⟩⟩

private theorem counts_disjoint {α} (xs : List α) (a b : α → Bool)
    (dis : ∀ x ∈ xs, a x = true → b x ≠ true) :
    xs.countP a + xs.countP b ≤ xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hi := ih (fun y hy => dis y (List.mem_cons_of_mem _ hy))
    have top := dis x List.mem_cons_self
    simp only [List.countP_cons,List.length_cons]
    cases ha : a x <;> cases hb : b x <;> simp_all <;> omega

private theorem triangular_bound {α} (r : α → α → Bool) (xs : List α) :
    DeletionCount.pairs r xs ≤ ((List.range xs.length).sum) := by
  induction xs with
  | nil => simp [DeletionCount.pairs]
  | cons x xs ih =>
    have bound : xs.countP (r x) ≤ xs.length := by simpa [List.countP_eq_length_filter] using List.length_filter_le (r x) xs
    simp [DeletionCount.pairs,List.range_succ]; omega

private theorem split_pairs {α} (r : α → α → Bool) (xs ys : List α)
    (gap : ∀ x ∈ xs, ∀ y ∈ ys, r x y=false) :
    DeletionCount.pairs r (xs++ys)=DeletionCount.pairs r xs + DeletionCount.pairs r ys := by
  induction xs with
  | nil => simp [DeletionCount.pairs]
  | cons x xs ih =>
    have zero : ys.countP (r x)=0 := List.countP_eq_zero.mpr (fun y hy => Bool.eq_false_iff.mp (gap _ List.mem_cons_self y hy))
    simp [DeletionCount.pairs,List.countP_append,zero,ih (fun z hz => gap _ (List.mem_cons_of_mem _ hz)),Nat.add_assoc]


private theorem peak (S : Nat → Prop) (one : S 1) (eight : ¬ S 8) :
    ∃ t, 1 ≤ t ∧ t ≤ 7 ∧ S t ∧ ¬ S (t+1) := by
  by_cases s7 : S 7; · exact ⟨7,by decide,by decide,s7,eight⟩
  by_cases s6 : S 6; · exact ⟨6,by decide,by decide,s6,s7⟩
  by_cases s5 : S 5; · exact ⟨5,by decide,by decide,s5,s6⟩
  by_cases s4 : S 4; · exact ⟨4,by decide,by decide,s4,s5⟩
  by_cases s3 : S 3; · exact ⟨3,by decide,by decide,s3,s4⟩
  by_cases s2 : S 2; · exact ⟨2,by decide,by decide,s2,s3⟩
  exact ⟨1,by decide,by decide,one,s2⟩

private theorem neighbors_inside {α r xs l} (sym : ∀ x y, r x y = r y x) (p : @Path α r xs l)
    (maximal : ¬ Nonempty (Path r xs (l+1))) (x : α) (hx : x ∈ xs) (e : r (p.vertex 0) x = true) :
    ∃ j, j<l ∧ p.vertex j=x := by
  apply Classical.byContradiction
  intro no
  exact maximal ⟨p.prepend x hx (fun i hi eq => no ⟨i,hi,eq⟩) ((sym _ _).trans e)⟩

private theorem spanning_chords {α} {r : α → α → Bool} {xs : List α} {l}
    (sym : ∀ i j, r i j=r j i) (irr : ∀ i, r i i=false) (nd : xs.Nodup)
    (deg : ∀ x ∈ xs, 4≤xs.countP (r x)) (p : Path r xs l) (pos : 1≤l) (small : l≤7)
    (maximal : ¬ Nonempty (Path r xs (l+1))) :
    ∃ j, j+1<l ∧ r (p.vertex 0) (p.vertex (j+1)) = true ∧ r (p.vertex j) (p.vertex (l-1)) = true := by
  let indices := List.range (l-1)
  let A (j : Nat) := r (p.vertex 0) (p.vertex (j+1))
  let B (j : Nat) := r (p.vertex (l-1)) (p.vertex j)
  have boundA : 4 ≤ indices.countP A := by
    have neighbors := List.Nodup.length_le_of_subset (nd.filter (r (p.vertex 0)))
      (l₂ := (indices.filter A).map (fun j => p.vertex (j+1)))
    rw [List.length_map,← List.countP_eq_length_filter,← List.countP_eq_length_filter] at neighbors
    apply Nat.le_trans (deg (p.vertex 0) (p.mem 0 (by omega)))
    apply neighbors
    intro x hx
    obtain ⟨hm,e⟩ := List.mem_filter.mp hx
    obtain ⟨j,hj,eq⟩ := neighbors_inside sym p maximal x hm e
    have nz : j ≠ 0 := by rintro rfl; rw [←eq,irr] at e; contradiction
    have v : p.vertex ((j-1)+1) = x := by rwa [Nat.sub_add_cancel (by omega)]
    exact List.mem_map.mpr ⟨j-1,List.mem_filter.mpr ⟨List.mem_range.mpr (by omega),
      by simpa only [A,v] using e⟩,v⟩
  have boundB : 4 ≤ indices.countP B := by
    have neighbors := List.Nodup.length_le_of_subset (nd.filter (r (p.vertex (l-1))))
      (l₂ := (indices.filter B).map p.vertex)
    rw [List.length_map,← List.countP_eq_length_filter,← List.countP_eq_length_filter] at neighbors
    apply Nat.le_trans (deg (p.vertex (l-1)) (p.mem _ (by omega)))
    apply neighbors
    intro x hx
    obtain ⟨hm,e⟩ := List.mem_filter.mp hx
    obtain ⟨j,hj,eq⟩ := neighbors_inside sym (p.reverse sym) maximal x hm (by simpa [Path.reverse] using e)
    change p.vertex (l-1-j)=x at eq
    have nk : l-1-j ≠ l-1 := by intro h; rw [←eq,h,irr] at e; contradiction
    exact List.mem_map.mpr ⟨l-1-j,List.mem_filter.mpr ⟨List.mem_range.mpr (by omega),
      by simpa only [B,eq] using e⟩,eq⟩
  apply Classical.byContradiction
  intro no
  have apart (j) (hj : j∈indices) (ha : A j = true) (hb : B j = true) : False :=
    no ⟨j,by have := List.mem_range.mp hj; omega,ha,(sym _ _).trans hb⟩
  have count := counts_disjoint indices A B apart
  change _ ≤ indices.length at count
  have len : indices.length=l-1 := List.length_range
  rw [len] at count
  omega

/-- The Erdős–Gallai edge bound for paths on eight vertices. Every graph
without such a path has at most three edges per vertex. -/
theorem edge_bound {α} (r : α → α → Bool) (sym : ∀ i j, r i j=r j i) (irr : ∀ i, r i i=false)
    (xs : List α) (nd : xs.Nodup) (free : ¬ Nonempty (Path r xs 8)) :
    DeletionCount.pairs r xs ≤ 3*xs.length := by
  classical
  generalize eq : xs.length = n
  induction n using Nat.strongRecOn generalizing xs with
  | ind n ih =>
    by_cases empty : xs=[]
    · subst xs; simp at eq; subst n; exact Nat.le_refl _
    by_cases low : ∃ x∈xs, xs.countP (r x) ≤ 3
    · obtain ⟨x,mem,small⟩ := low
      let rest := xs.erase x
      have perm := List.perm_cons_erase mem
      have len : rest.length+1=n := by simpa only [rest, List.length_cons, ← eq] using perm.length_eq.symm
      have smaller :=  ih _ (by omega : rest.length<n) rest (nd.erase x)
        (fun ⟨p⟩ => free ⟨p.onSubset (fun _ => List.mem_of_mem_erase)⟩) rfl
      have hd := perm.countP_eq (r x)
      rw [List.countP_cons,irr] at hd
      simp only [Bool.false_eq_true,↓reduceIte,Nat.add_zero] at hd
      rw [DeletionCount.perm r sym perm,DeletionCount.pairs]
      change rest.countP (r x) + DeletionCount.pairs r rest ≤ 3*n
      change _ = rest.countP (r x) at hd
      omega
    have deg (x) (mem : x∈xs) : 4≤xs.countP (r x) := by
      apply Classical.byContradiction
      intro h
      exact low ⟨x,mem,by omega⟩
    have one : Nonempty (Path r xs 1) := ⟨{
      vertex := fun _ => xs.head empty, mem := fun _ _ => List.head_mem empty,
      inj := fun _ _ _ _ _ => by omega, edges := fun _ _ => by omega }⟩
    obtain ⟨l,pos,small,⟨p⟩,maximal⟩ := peak (fun t => Nonempty (Path r xs t)) one free
    obtain ⟨cut,hc,a,b⟩ := spanning_chords sym irr nd deg p pos small maximal
    let pathVertices := (List.range l).map p.vertex
    let pred (x) := decide (x∈pathVertices)
    let keep := xs.filter pred
    let rest := xs.filter (fun x => !(pred x))
    have perm : (keep++rest).Perm xs := List.filter_append_perm pred xs
    have total := perm.length_eq
    change (keep++rest).length=xs.length at total
    rw [List.length_append,eq] at total
    have bound : keep.length ≤ l := by
      have subset := List.Nodup.length_le_of_subset (nd.filter pred) (l₂ := pathVertices)
        (fun _ h => of_decide_eq_true (List.mem_filter.mp h).2)
      simpa [pathVertices,keep] using subset
    have present : p.vertex 0 ∈ keep := List.mem_filter.mpr ⟨p.mem _ (by omega),
      decide_eq_true (List.mem_map.mpr ⟨0,List.mem_range.mpr (by omega),rfl⟩)⟩
    have nonzero : 0 < keep.length := List.length_pos_iff.mpr (List.ne_nil_of_mem present)
    have smaller :=  ih _ (by omega : rest.length<n) rest (nd.filter _)
      (fun ⟨q⟩ => free ⟨q.onSubset (fun _ h => (List.mem_filter.mp h).1)⟩) rfl
    have boundEdges := triangular_bound r keep
    have factor : (List.range keep.length).sum ≤ 3*keep.length :=
      (show ∀ m : Fin 8, (List.range m.val).sum ≤ 3*m.val by decide) ⟨_,by omega⟩
    have gap (x) (hx : x∈keep) (y) (hy : y∈rest) : r x y=false := by
      obtain ⟨_,inpath⟩ := List.mem_filter.mp hx
      obtain ⟨i,hi,eqx⟩ := List.mem_map.mp (of_decide_eq_true inpath : x∈pathVertices)
      have il := List.mem_range.mp hi
      obtain ⟨q,start,range⟩ := cycle_path sym p small hc il a b
      obtain ⟨ym,out⟩ := List.mem_filter.mp hy
      have away (j) (hj : j<l) : q.vertex j ≠ y := by
        obtain ⟨k,hk,eqk⟩ := range _ hj
        intro e
        have ym : y ∈ pathVertices := List.mem_map.mpr ⟨k,List.mem_range.mpr hk,eqk.symm.trans e⟩
        simp [pred,ym] at out
      apply Bool.eq_false_iff.mpr
      intro arc
      exact maximal ⟨q.prepend y ym away (by rw [start,eqx,sym]; exact arc)⟩
    rw [← DeletionCount.perm r sym perm,split_pairs r keep rest gap]
    omega

end Ramsey556.PathDensity
