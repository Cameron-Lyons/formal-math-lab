import Ramsey556.Biclique13
import Ramsey556.BicliqueObstruction
import Ramsey556.FifteenResult
import Ramsey556.VertexSets

namespace Ramsey556.TenFourteen

private def swap {n} (a b i : Fin n) := if i=a then b else if i=b then a else i

private theorem swap_self {n} (a b i : Fin n) : swap a b (swap a b i)=i := by
  by_cases x : i=a <;> by_cases y : i=b <;> by_cases z : a=b <;> simp_all [swap]

private theorem swap_inj {n} {a b x y : Fin n} (e : swap a b x=swap a b y) : x=y := by
  simpa only [swap_self] using congrArg (swap a b) e

private theorem reindex {n} (s t a b : Fin n) (st : s≠t) (ab : a≠b) :
    ∃ f : Fin n → Fin n, (∀ ⦃i j⦄, f i=f j → i=j) ∧ f s=a ∧ f t=b := by
  let d := swap s a b
  have ds : d ≠ s := by
    have key : swap s a a = s := by by_cases h : s=a <;> simp [swap,h]
    exact fun h => ab (swap_inj (h.trans key.symm)).symm
  refine ⟨fun i => swap s a (swap t d i), fun {_ _} h => swap_inj (swap_inj h),?_,?_⟩
  · simp [swap,st,Ne.symm ds]
  · change swap s a (swap t d t) = b
    rw [show swap t d t=d by simp [swap]]
    exact swap_self s a b

private theorem joined {a b : Nat} (c : Coloring 33) (r : Fin 3)
    (A : Fin a → Fin 33) (B : Fin b → Fin 33)
    (ai : ∀ ⦃i j⦄, A i=A j → i=j) (bi : ∀ ⦃i j⦄, B i=B j → i=j) (sep : ∀ i j, A i≠B j)
    (aa : ∀ i j, i≠j → c.edge (A i) (A j) ≠ r) (bb : ∀ i j, i≠j → c.edge (B i) (B j) ≠ r)
    (ab : ∀ i j, c.edge (A i) (B j) ≠ r) :
    ∃ f : Fin (a+b) → Fin 33, (∀ ⦃i j⦄, f i=f j → i=j) ∧
      ∀ i j, i≠j → c.edge (f i) (f j) ≠ r := by
  let f (i : Fin (a+b)) := Fin.addCases (m:=a) (n:=b) (motive:=fun _ => Fin 33) A B i
  refine ⟨f,?_,?_⟩
  · intro i j eq
    induction i using Fin.addCases <;> induction j using Fin.addCases <;>
      simp only [f,Fin.addCases_left,Fin.addCases_right] at eq
    · exact congrArg _ (ai eq)
    · exact (sep _ _ eq).elim
    · exact (sep _ _ eq.symm).elim
    · exact congrArg _ (bi eq)
  · intro i j ne
    induction i using Fin.addCases <;> induction j using Fin.addCases <;>
      simp only [f,Fin.addCases_left,Fin.addCases_right]
    · exact aa _ _ (fun h => ne (congrArg _ h))
    · exact ab _ _
    · rw [c.symm]; exact ab _ _
    · exact bb _ _ (fun h => ne (congrArg _ h))

/-- With five available vertices on a shore, a red edge inside that shore
closes an eight-edge alternating path through four opposite vertices. -/
private theorem shore {a b : Nat} (ha : 5 ≤ a) (hb : 4 ≤ b) (c : Coloring 33) (r : Fin 3)
    (free : ¬ HasMonoC9 c) (A : Fin a → Fin 33) (B : Fin b → Fin 33)
    (ai : ∀ ⦃i j⦄, A i=A j → i=j) (bi : ∀ ⦃i j⦄, B i=B j → i=j)
    (sep : ∀ i j, A i ≠ B j) (cross : ∀ i j, c.edge (A i) (B j)=r) :
    ∀ i j, i≠j → c.edge (A i) (A j) ≠ r := by
  intro i j ne edge
  let old (z : Fin 5) : Fin a := ⟨z.val,by omega⟩
  let other (z : Fin 4) : Fin b := ⟨z.val,by omega⟩
  obtain ⟨p,pi,first,last⟩ := reindex (old 0) (old 4) i j (by intro h; have := congrArg Fin.val h; contradiction) ne
  apply free (BicliqueObstruction.closeAcross c r (fun u => B (other u)) (fun v => A (p (old v)))
    (fun {_ _} e => Fin.ext (congrArg (fun v : Fin b => v.val) (bi e)))
    (fun {_ _} e => Fin.ext (congrArg (fun v : Fin a => v.val) (pi (ai e)))) (fun _ _ => (sep _ _).symm)
    (fun _ _ => (c.symm _ _).trans (cross _ _)) ?_)
  rwa [first,last]

/-- Red edges between exterior vertices force their red B-neighbors to coincide. -/
private theorem same_neighbor (c : Coloring 33) (r : Fin 3) (free : ¬ HasMonoC9 c)
    (A : Fin 10 → Fin 33) (B : Fin 14 → Fin 33) (w : Fin 9 → Fin 33)
    (ai : ∀ ⦃i j⦄, A i=A j → i=j) (bi : ∀ ⦃i j⦄, B i=B j → i=j)
    (wi : ∀ ⦃i j⦄, w i=w j → i=j) (ab : ∀ i j, A i ≠ B j)
    (aw : ∀ i j, A i ≠ w j) (bw : ∀ i j, B i ≠ w j) (cross : ∀ i j, c.edge (A i) (B j)=r)
    {x y : Fin 9} (xy : x≠y) (edge : c.edge (w x) (w y) = r) {a b : Fin 14}
    (ea : c.edge (w x) (B a) = r) (eb : c.edge (w y) (B b) = r) : a=b := by
  apply Classical.byContradiction
  intro ne
  obtain ⟨p,pi,start,finish⟩ := reindex (0 : Fin 14) 3 a b (by decide) ne
  let Q (k : Fin 14) := B (p k)
  let seq := [w x,Q 0,A 0,Q 1,A 1,Q 2,A 2,Q 3,w y]
  have aa (i j) : A i = A j ↔ i=j := ⟨fun e => ai e,congrArg _⟩
  have qq (i j) : Q i = Q j ↔ i=j := ⟨fun e => pi (bi e),congrArg _⟩
  have ww (i j) : w i = w j ↔ i=j := ⟨fun e => wi e,congrArg _⟩
  have aq (i j) : A i ≠ Q j := ab _ _
  have qa (i j) : Q i ≠ A j := (ab _ _).symm
  have qw (i j) : Q i ≠ w j := bw _ _
  have wq (i j) : w i ≠ Q j := (bw _ _).symm
  have wa (i j) : w i ≠ A j := (aw _ _).symm
  have nd : seq.Nodup := by simp [seq,aa,qq,ww,xy,aq,qa,qw,wq,aw,wa]
  let v (k : Fin 9) := seq[k.val]'k.isLt
  apply free
  refine ⟨r,v,fun {_ _} e => Fin.ext (nd.eq_of_getElem_eq _ _ e),?_⟩
  intro k
  have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 ∨ k=7 ∨ k=8 := by omega
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · change c.edge (w x) (B (p 0)) = r
    rwa [start]
  all_goals first | exact cross _ _ | exact (c.symm _ _).trans (cross _ _) |
    exact (c.symm _ _).trans edge | (change c.edge (B (p 3)) (w y) = r; rw [finish,c.symm]; exact eb)


/-- Orient a matching by the vertex numbers. Larger endpoints form one
independent set, all other vertices form another. -/
private theorem five_of_matching (R : Fin 9 → Fin 9 → Prop) (sym : ∀ i j, R i j → R j i)
    (unique : ∀ x y z, x≠y → x≠z → R x y → R x z → y=z) :
    ∃ f : Fin 5 → Fin 9, (∀ ⦃i j⦄, f i=f j → i=j) ∧ ∀ i j, i≠j → ¬ R (f i) (f j) := by
  classical
  let tag (x : Fin 9) := decide (∃ y, y<x ∧ R x y)
  have proper (x y : Fin 9) (lt : x<y) (edge : R x y) : tag x ≠ tag y := by
    have bigger : tag y = true := decide_eq_true ⟨x,lt,sym _ _ edge⟩
    have smaller : tag x = false := by
      apply decide_eq_false
      rintro ⟨z,l,h⟩
      have eq := unique _ _ _ (by omega : x≠y) (by omega : x≠z) edge h
      omega
    rw [bigger,smaller]
    decide
  obtain ⟨f,b,fi,bit⟩ := select_side (m := 4) tag (by decide)
  refine ⟨f,fi,?_⟩
  intro i j ne edge
  have different := fi.ne ne
  by_cases h : f i < f j
  · exact proper _ _ h edge ((bit i).trans (bit j).symm)
  · exact proper _ _ (by omega) (sym _ _ edge) ((bit j).trans (bit i).symm)

private def inTen (i : Fin 7) : Fin 10 := ⟨i.val,by omega⟩
private def inFourteen (i : Fin 7) : Fin 14 := ⟨i.val,by omega⟩

/-- Any monochromatic K₁₀,₁₄ in K₃₃ forces a monochromatic nine-cycle. -/
theorem forces_cycle (c : Coloring 33) (r : Fin 3) (A : Fin 10 → Fin 33) (B : Fin 14 → Fin 33)
    (ai : ∀ ⦃i j⦄, A i=A j → i=j) (bi : ∀ ⦃i j⦄, B i=B j → i=j)
    (sep : ∀ i j, A i ≠ B j) (cross : ∀ i j, c.edge (A i) (B j)=r) : HasMonoC9 c := by
  classical
  apply Classical.byContradiction
  intro free
  have ia := shore (by decide : 5≤10) (by decide : 4≤14) c r free A B ai bi sep cross
  have ib := shore (by decide : 5≤14) (by decide : 4≤10) c r free B A bi ai
    (fun i j => (sep j i).symm) (fun i j => (c.symm _ _).trans (cross _ _))
  let both (i : Fin 24) := Fin.addCases (m:=10) (n:=14) (motive:=fun _ => Fin 33) A B i
  obtain ⟨w,wi,away⟩ := outside_vertices (a:=24) (b:=9) (by decide) both
  have aw (i j) : A i ≠ w j := by simpa only [both,Fin.addCases_left] using away (Fin.castAdd 14 i) j
  have bw (i j) : B i ≠ w j := by simpa only [both,Fin.addCases_right] using away (Fin.natAdd 10 i) j
  have touches (i : Fin 9) : ∃ b, c.edge (w i) (B b)=r := by
    apply Classical.byContradiction
    intro none
    obtain ⟨f,fi,ind⟩ := joined (b:=1) c r B (fun _ => w i) bi
      (fun {_ _} _ => Fin.ext (by omega)) (fun j _ => bw j i) ib (fun j k ne => by omega)
      (fun j _ e => none ⟨j,(c.symm _ _).trans e⟩)
    exact free (monoC9_of_independent15 c f fi r ind)
  have outside (a x) : c.edge (A a) (w x) ≠ r := by
    intro ea
    obtain ⟨b,eb⟩ := touches x
    let left (i : Fin 7) : Fin 10 := a + inTen i
    let right (i : Fin 7) : Fin 14 := b + inFourteen i
    have li {i j} (h : left i=left j) : i=j := (by decide : ∀ (a : Fin 10) (i j : Fin 7),
      a+inTen i = a+inTen j → i=j) a i j h
    have ri {i j} (h : right i=right j) : i=j := (by decide : ∀ (a : Fin 14) (i j : Fin 7),
      a+inFourteen i = a+inFourteen j → i=j) b i j h
    apply Fifteen.biclique_spokes c r (fun i => A (left i)) (fun i => B (right i)) (w x)
      (fun {_ _} h => li (ai h)) (fun {_ _} h => ri (bi h)) (fun i j => sep _ _) (fun i => aw _ _)
      (fun i => bw _ _) (fun i j => cross _ _) free (a:=0) (b:=0)
    · simpa [left,show inTen 0 = 0 by decide] using (c.symm _ _).trans ea
    · simpa [right,show inFourteen 0 = 0 by decide] using eb
  let R (i j : Fin 9) := c.edge (w i) (w j)=r
  have sym (i j) (h : R i j) : R j i := (c.symm _ _).trans h
  have only (x y z : Fin 9) (xy : x≠y) (xz : x≠z) (ey : R x y) (ez : R x z) : y=z := by
    apply Classical.byContradiction
    intro yz
    obtain ⟨b,e⟩ := touches x
    have ny (a) (edge : c.edge (w y) (B a)=r) : a=b :=
      (same_neighbor c r free A B w ai bi wi sep aw bw cross xy ey e edge).symm
    have nz (a) (edge : c.edge (w z) (B a)=r) : a=b :=
      (same_neighbor c r free A B w ai bi wi sep aw bw cross xz ez e edge).symm
    obtain ⟨a,ha⟩ := touches y
    have nx (j) (edge : c.edge (w x) (B j)=r) : j=b :=
      (same_neighbor c r free A B w ai bi wi sep aw bw cross xy ey edge ha).trans (ny _ ha)
    let old (i : Fin 13) := Fifteen.skip b i
    have skip := Fifteen.skip_spec b
    let xs := [B b,w x,w y,w z]
    let f (k : Fin 4) := xs[k.val]'k.isLt
    have ww (i j) : w i = w j ↔ i=j := ⟨fun h => wi h, congrArg _⟩
    have nd : xs.Nodup := by simp [xs,ww,xy,xz,yz,bw]
    apply free (Biclique13.split_forces c r (fun i => B (old i)) f
      (fun {_ _} h => skip.1 _ _ (bi h)) (fun {_ _} h => Fin.ext (nd.eq_of_getElem_eq _ _ h)) ?_
      (fun i j ne => ib _ _ (fun h => ne (skip.1 _ _ h))) ?_)
    · intro i j
      have cases : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
      rcases cases with rfl|rfl|rfl|rfl
      · exact fun h => skip.2 i (bi h)
      all_goals exact bw _ _
    · intro i j h
      have cases : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
      rcases cases with rfl|rfl|rfl|rfl
      · exact ib _ _ (Ne.symm (skip.2 i)) h
      · exact skip.2 i (nx _ h)
      · exact skip.2 i (ny _ h)
      · exact skip.2 i (nz _ h)
  obtain ⟨f,fi,ind⟩ := five_of_matching R sym only
  obtain ⟨v,vi,miss⟩ := joined c r A (fun j => w (f j)) ai (fun {_ _} h => fi (wi h))
    (fun i j => aw i (f j)) ia ind (fun i j => outside i (f j))
  exact free (monoC9_of_independent15 c v vi r miss)

end Ramsey556.TenFourteen
