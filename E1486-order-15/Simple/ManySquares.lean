import Simple.Graph

namespace E1486.Simple.Counting

private def total {α} (l : List α) (f : α → Nat) := (l.map f).sum
@[simp] private theorem total_nil {α} (f : α → Nat) : total [] f = 0 := rfl
@[simp] private theorem total_cons {α} (x : α) (l : List α) (f : α → Nat) :
    total (x::l) f = f x + total l f := rfl
@[simp] private theorem total_append {α} (l r : List α) (f : α → Nat) :
    total (l++r) f = total l f + total r f := by simp [total]
private theorem mono {α} (l : List α) {f g : α → Nat} (h : ∀ x ∈ l, f x ≤ g x) : total l f ≤ total l g := by
  induction l with
  | nil => simp
  | cons x l ih => exact Nat.add_le_add (h x (by simp)) (ih (fun y hy => h y (by simp [hy])))
private theorem same {α} (l : List α) {f g : α → Nat} (h : ∀ x ∈ l, f x = g x) : total l f = total l g :=
  Nat.le_antisymm (mono l (fun x hx => (Nat.le_of_eq (h x hx)))) (mono l (fun x hx => (Nat.le_of_eq (h x hx).symm)))
private theorem saturated {α} (l : List α) {f g : α → Nat} (h : ∀ x ∈ l, f x ≤ g x)
    (eq : total l f = total l g) : ∀ x ∈ l, f x = g x := by
  induction l with
  | nil => simp
  | cons x l ih =>
    have rest := fun y hy => h y (List.mem_cons_of_mem _ hy)
    have ht := mono l rest; have hx := h x (by simp); simp only [total_cons] at eq
    intro v hv; rcases List.mem_cons.mp hv with rfl | hv
    · omega
    · exact ih rest (by omega) v hv
private theorem add {α} (l : List α) (f g : α → Nat) : total l (fun x => f x + g x) = total l f + total l g := by
  induction l <;> simp [*] <;> omega
private theorem mul {α} (l : List α) (c : Nat) (f : α → Nat) : total l (fun x => c*f x) = c*total l f := by
  induction l <;> simp [*,Nat.mul_add]
private theorem const {α} (l : List α) (c : Nat) : total l (fun _ => c) = l.length*c := by
  induction l <;> simp [*,Nat.add_mul,Nat.add_comm]
private theorem swap {α β} (l : List α) (r : List β) (f : α → β → Nat) :
    total l (fun x => total r (f x)) = total r (fun y => total l (fun x => f x y)) := by
  induction l with
  | nil => simp [const]
  | cons x l ih => simp [add, ih]
private theorem extremal {α} (l : List α) (x : α) (hx : x ∈ l) (f : α → Nat) :
    ∃ a ∈ l, ∃ b ∈ l, ∀ v ∈ l, f a ≤ f v ∧ f v ≤ f b := by
  let ds := l.map f
  have hne : ds ≠ [] := List.ne_nil_of_mem (List.mem_map_of_mem hx (f := f))
  obtain ⟨lo,hl⟩ := Option.isSome_iff_exists.mp (List.isSome_min?_iff.mpr hne)
  obtain ⟨hi,hh⟩ := Option.isSome_iff_exists.mp (List.isSome_max?_iff.mpr hne)
  obtain ⟨hlo,hmin⟩ := List.min?_eq_some_iff.mp hl; obtain ⟨hhi,hmax⟩ := List.max?_eq_some_iff.mp hh
  obtain ⟨a,ha,ea⟩ := List.mem_map.mp hlo; obtain ⟨b,hb,eb⟩ := List.mem_map.mp hhi
  refine ⟨a,ha,b,hb,?_⟩; intro v hv; rw [ea,eb]
  exact ⟨hmin _ (List.mem_map_of_mem hv),hmax _ (List.mem_map_of_mem hv)⟩

private def mmul {α} (l : List α) (a b : α → α → Nat) (x y : α) := total l fun i => a x i*b i y
private theorem assoc {α} (l : List α) (a : α → α → Nat) (x y : α) :
    mmul l a (mmul l a a) x y = mmul l (mmul l a a) a x y := by
  unfold mmul
  calc
    total l (fun i => a x i * total l (fun z => a i z*a z y)) =
      total l (fun i => total l (fun z => a x i * (a i z * a z y))) := by simp [mul]
    _ = total l (fun z => total l (fun i => a z y*(a x i*a i z))) := by
      rw [swap l l]; simp only [Nat.mul_left_comm,Nat.mul_comm]
    _ = _ := by simp [mul,Nat.mul_comm]

/-- Let `M = A²`. All its entries are at most one, every column in `Q` consists
of ones, and each diagonal entry indexed by `T` vanishes. Counting walks shows
that at most eleven columns can belong to `Q` when the matrix has order 15. -/
private theorem matrix_bound {α : Type} (Q T : List α) (A : α → α → Nat)
    (size : Q.length + T.length = 15)
    (M : α → α → Nat) (hM : M = mmul (Q++T) A A)
    (unique : ∀ x y, M x y ≤ 1) (ones : ∀ x q, q∈Q → M x q=1)
    (diag : ∀ t ∈ T, M t t=0) : Q.length ≤ 11 := by
  by_cases large : 12≤Q.length
  · let V := Q++T
    let d := fun x => total V (A x)
    -- The two products A M and M A count the same three-step walks.
    have c (q : α) (hq : q∈Q) (x : α) :
        d x = total Q (fun u => A u q) + total T (fun u => M x u * A u q) := by
      calc
        d x = mmul V A M x q := same V (fun u _ => by simp [ones u q hq])
        _ = mmul V M A x q := by rw [hM]; exact assoc V A x q
        _ = _ := by unfold mmul; rw [show V=Q++T from rfl,total_append]; congr 1;apply same; intro u hu; simp [ones x u hu]
    have row (x : α) : total V (M x) = total V (fun z => A x z*d z) := by
      rw [hM];change total V (fun y=>total V (fun z=>A x z*A z y)) = _
      rw [swap V V];apply same; intro z _;exact mul V (A x z) _
    obtain ⟨x,hx⟩ : ∃ x, x∈V := by cases H : V with
      | nil =>
        have hv : V.length=15 := by simp [V,size]
        rw [H] at hv;contradiction
      | cons x l => exact ⟨x,by simp⟩
    obtain ⟨u,hu,v,hv,ext⟩ := extremal V x hx d
    let r:=d u; let D:=d v
    have minmax (x) (hx : x∈V) : r≤d x ∧ d x≤D := ext x hx
    have tv {q} (h : q∈T) : q∈V := List.mem_append_right _ h
    have count (x : α) : Q.length ≤ total V (M x) ∧ total V (M x) ≤ 15 := by
      constructor
      · have he : total Q (M x)=Q.length := by rw [same Q (fun q hq => ones x q hq),const,Nat.mul_one]
        change Q.length ≤ total (Q++T) _; rw [total_append,he];omega
      · have z:=mono V (f := M x) (g := fun _=>1) (fun y _=>unique x y)
        simpa [const,V,size] using z
    -- From any starting vertex, the two-step endpoints include Q and use at most 15 slots.
    have lower : Q.length ≤ r*D := by
      apply Nat.le_trans (count u).1
      rw [row,Nat.mul_comm]; change _ ≤ D*total V (A u); rw [← mul]
      exact mono V (fun x hx => by rw [Nat.mul_comm]; exact Nat.mul_le_mul_right _ (minmax x hx).2)
    have upper : r*D ≤ 15 := by
      apply Nat.le_trans _ (count v).2
      rw [row];change r*total V (A v) ≤ _;rw [← mul]
      exact mono V (fun x hx => by rw [Nat.mul_comm (A v x)];exact Nat.mul_le_mul_right _ (minmax x hx).1)
    -- P(q) counts predecessors outside Q. B(t) counts successors in Q.
    let P := fun q => total T (fun t => A t q)
    let B := fun t => total Q (A t)
    have frac (q : α) (hq : q∈Q) : D-r ≤ P q := by
      have hi := c q hq v; have lo := c q hq u
      have e := mono T (f := fun t=>M v t*A t q) (g := fun t=>A t q) (fun t _ => by
        have e:=Nat.mul_le_mul_right (A t q) (unique v t);simpa using e)
      dsimp [D,r,P]; omega
    have Bbound (t : α) (ht : t ∈ T) : B t ≤ D := by
      have := (minmax t (tv ht)).2;change total Q (A t) ≤ D;change total (Q++T) (A t) ≤ D at this
      rw [total_append] at this;omega
    have sumP : total Q P = total T B := swap Q T (fun q t=>A t q)
    have a1 : Q.length*(D-r) ≤ total Q P := by rw [← const];exact mono Q frac
    have a2 : total T B ≤ T.length*D := by rw [← const];exact mono T Bbound
    have hnum : Q.length*(D-r) ≤ T.length*D := by omega
    have rr : r≤D := (minmax u hu).2
    have rD : r≤15 ∧ D≤15 := by
      have pos : 0<r := by
        by_cases hz : r=0
        · have lo : Q.length≤0 := by simpa only [hz,Nat.zero_mul] using lower
          omega
        · omega
      have e := Nat.mul_le_mul_right D (show 1≤r from pos);simp at e;omega
    -- For twelve or more squares, the degree bounds leave just one triple.
    have arithmetic : ∀ (k r D : Fin 16), 12≤k.val → r.val≤D.val → k.val≤r.val*D.val → r.val*D.val≤15 →
        k.val*(D.val-r.val) ≤ (15-k.val)*D.val → k.val=12 ∧ r.val=3 ∧ D.val=4 := by decide
    obtain ⟨K,R,U⟩ := arithmetic ⟨Q.length,by omega⟩ ⟨r,by omega⟩ ⟨D,by omega⟩ large rr lower upper (by simpa [show 15-Q.length=T.length by omega] using hnum)
    change Q.length=12 at K;change r=3 at R;change D=4 at U
    have T3 : T.length=3 := by omega
    -- Both bounds must be attained. Each nonsquare uses four outgoing edges
    -- to squares, and each square has exactly one nonsquare predecessor.
    have E1 : total Q (fun _=>D-r)=total Q P := by simp only [const,K,R,U,T3] at *;omega
    have E2 : total T B=total T (fun _=>D) := by simp only [const,K,R,U,T3] at *;omega
    have exactP := saturated Q frac E1
    have exactB := saturated T Bbound E2
    obtain ⟨t,ht⟩ : ∃ t,t∈T := by cases T with | nil => contradiction | cons t l => exact ⟨t,by simp⟩
    have dt : d t=D := by
      have z:=exactB t ht
      have e: B t≤d t := by simp [B,d,V]
      have mx:= (minmax t (tv ht)).2
      omega
    obtain ⟨q,hq,pos⟩ : ∃ q∈Q, 0<A t q := by
      have e : 0<(Q.map (A t)).sum := by change 0<B t; rw [exactB t ht,U];decide
      obtain ⟨v,hv,pos⟩ := List.sum_pos_iff_exists_pos_nat.mp e; obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hv; exact ⟨q,hq,pos⟩
    -- For the edge t → q, the degree of t forces M[t,t] to contribute its edge
    -- to the three-walk count. Its diagonal entry is zero.
    have eqc := c q hq t; have lc := c q hq u; have pc := exactP q hq
    have point (i : α) (_ : i∈T) : M t i*A i q ≤ A i q := by simpa using Nat.mul_le_mul_right (A i q) (unique t i)
    have eqsum : total T (fun i=>M t i*A i q) = total T (fun i=>A i q) := by
      change D-r = total T (fun i => A i q) at pc
      change r = total Q (fun i=>A i q)+ _ at lc
      have le := mono T point
      rw [dt,U] at eqc;rw [R] at lc;rw [R,U] at pc;omega
    have last := saturated T point eqsum t ht; rw [diag t ht,Nat.zero_mul] at last;omega
  · omega

private theorem single (z : Fin 15) : total (List.finRange 15) (fun i => if i=z then 1 else 0) = 1 := by
  revert z; decide

/-- At most eleven vertices have closed walks of length two in a 15-vertex
    graph satisfying the E1486 graph conditions. The proof counts three-step walks. -/
theorem at_most_eleven (G : Fin 15 → Fin 15 → Prop) (h : Conditions G) {k : Nat}
    (hk : k≤15) (marks : ∀ i : Fin 15, Marked G i ↔ i.val<k) : k≤11 := by
  classical
  let V := List.finRange 15
  let Q := V.take k
  let T := V.drop k
  have v : Q++T=V := List.take_append_drop ..
  have len : Q.length=k := by simp [Q,V,Nat.min_eq_left hk]
  have size : Q.length+T.length =15 := by rw [← List.length_append,v];simp [V]
  have typ (i : Fin 15) : (i∈Q ↔ i.val<k) ∧ (i∈T ↔ k≤i.val) := by
    have H : ∀ (k : Fin 16) (i : Fin 15), (i∈V.take k.val ↔ i.val<k.val) ∧
      (i∈V.drop k.val ↔ k.val≤i.val) := by dsimp [V];decide
    exact H ⟨k,by omega⟩ i
  let A := fun x y => if G x y then 1 else 0
  let M := fun x y => if ∃ i, Walk G x i y then 1 else 0
  have hm : M=mmul (Q++T) A A := by
    funext x y;rw [v]; unfold mmul
    by_cases p : ∃ i, Walk G x i y
    · obtain ⟨z,hz⟩ := p
      have hp : ∃ i, Walk G x i y := ⟨z,hz⟩
      simp only [M,ite_eq_left hp]; rw [← single z]
      apply same; intro i hi
      by_cases e : i=z
      · subst i; simp [A,hz.1,hz.2]
      · have hnot : ¬ (G x i ∧ G i y) := fun hxy => e (h.unique hxy hz)
        by_cases g₁ : G x i <;> by_cases g₂ : G i y <;> simp_all [A]
    · simp only [M,ite_eq_right p];rw [same V (g := fun _=>0) (by
        intro i _; by_cases e : G x i
        · have n : ¬ G i y := fun ey=>p ⟨i,e,ey⟩;simp [A,n]
        · simp [A,e]),const,Nat.mul_zero]
  rw [← len];apply matrix_bound Q T A size M hm
  · intro x y; simp [M];split <;> decide
  · intro x q hq;exact ite_eq_left (h.reach x q ((marks q).2 ((typ q).1.mp hq)))
  · intro t ht; exact ite_eq_right fun e => (Nat.not_lt_of_ge ((typ t).2.mp ht)) ((marks t).mp e)

end E1486.Simple.Counting
