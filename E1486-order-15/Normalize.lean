import E1486

namespace E1486

abbrev Vertex := Fin 15
abbrev Operation := Vertex → Vertex → Vertex

def square (m : Operation) (a : Vertex) := m a a
def IsSquare (m : Operation) (a : Vertex) := ∃ x, square m x = a

theorem square_involutive {m : Operation} (hm : Law m) {q : Vertex} (hq : IsSquare m q) :
    square m (square m q) = q :=
  square_involution hm hq

/-- The square map on the initial square segment has its fixed points first,
then its disjoint transpositions in consecutive pairs. -/
def partner (j q : Nat) := if q < j then q else if (q-j)%2=0 then q+1 else q-1

structure DiagNormal (m : Operation) (k j : Nat) : Prop where
  le_size : k ≤ 15
  le_squares : j ≤ k
  parity : (k-j)%2=0
  sq_iff : ∀ a : Vertex, IsSquare m a ↔ a.val < k
  diagram : ∀ a : Vertex, a.val < k → (square m a).val = partner j a.val

structure Label where
  old : Vertex → Vertex
  idx : Vertex → Vertex
  idx_old : ∀ i, idx (old i) = i
  old_idx : ∀ i, old (idx i) = i

def Label.pull (p : Label) (m : Operation) : Operation := fun a b => p.idx (m (p.old a) (p.old b))
theorem Label.law (p : Label) {m : Operation} (hm : Law m) : Law (p.pull m) := by
  intro x y z
  simp only [Label.pull, p.old_idx]
  rw [hm _ _ _, p.idx_old]

theorem Label.sq (p : Label) (m : Operation) (a : Vertex) :
    square (p.pull m) a = p.idx (square m (p.old a)) := rfl

theorem Label.isSq (p : Label) (m : Operation) (a : Vertex) :
    IsSquare (p.pull m) a ↔ IsSquare m (p.old a) := by
  constructor
  · rintro ⟨x,hx⟩
    exact ⟨p.old x, by simpa [p.sq,p.old_idx] using congrArg p.old hx⟩
  · rintro ⟨x,hx⟩
    exact ⟨p.idx x, by simp [p.sq,p.old_idx,hx,p.idx_old]⟩

theorem Label.row (p : Label) (m : Operation) (a b : Vertex) :
    Row (p.pull m) a b ↔ Row m (p.old a) (p.old b) := by
  constructor
  · rintro ⟨z,hz⟩
    exact ⟨p.old z,by simpa [Label.pull,p.old_idx] using congrArg p.old hz⟩
  · rintro ⟨z,hz⟩
    exact ⟨p.idx z,by simp [Label.pull,p.old_idx,hz,p.idx_old]⟩

def doublets {α : Type} (f : α → α) : List α → List α
  | [] => []
  | x :: r => x :: f x :: doublets f r

private theorem len_doublets {α : Type} (f : α → α) (l : List α) :
    (doublets f l).length = 2*l.length := by induction l <;> simp [doublets, *] <;> omega

private theorem mem_doublets {α : Type} (f : α → α) (l : List α) (x : α) :
    x ∈ doublets f l ↔ ∃ a ∈ l, x = a ∨ x = f a := by
  induction l with
  | nil => simp [doublets]
  | cons a l ih => simp [doublets,ih]; grind

private theorem nodup_doublets (f : Vertex → Vertex) {l : List Vertex} (hl : l.Nodup)
    (hf : ∀ x ∈ l, x < f x ∧ f (f x) = x) : (doublets f l).Nodup := by
  induction l with
  | nil => simp [doublets]
  | cons a l ih =>
    obtain ⟨ha,hr⟩ := List.nodup_cons.mp hl
    have H := hf a (by simp)
    have rest : ∀ x ∈ l, x < f x ∧ f (f x) = x := fun x hx => hf x (by simp [hx])
    simp only [doublets, List.nodup_cons, List.mem_cons, not_or]
    refine ⟨⟨Fin.ne_of_lt H.1, ?_⟩, ?_, ih hr rest⟩
    · intro hx; obtain ⟨u,hu,h|h⟩ := (mem_doublets ..).mp hx
      · exact ha (h ▸ hu)
      · have := rest u hu; grind [Fin.lt_def]
    · intro hx; obtain ⟨u,hu,h|h⟩ := (mem_doublets ..).mp hx
      · have := rest u hu; grind [Fin.lt_def]
      · have := rest u hu; grind

private theorem doublets_partner (f : Vertex → Vertex) (l : List Vertex)
    (hf : ∀ x ∈ l, f (f x) = x) (i : Nat) (hi : i < (doublets f l).length) :
    ∃ h : partner 0 i < (doublets f l).length, f (doublets f l)[i] = (doublets f l)[partner 0 i] := by
  induction l generalizing i with
  | nil => simp [doublets] at hi
  | cons a l ih =>
    cases i with
    | zero => exact ⟨by simp [partner,doublets],rfl⟩
    | succ i => cases i with
      | zero => exact ⟨by simp [partner,doublets], by simpa [partner,doublets] using hf a (by simp)⟩
      | succ i =>
        have hp : partner 0 (i+2) = partner 0 i+2 := by simp [partner]; split <;> omega
        obtain ⟨h,e⟩ := ih (fun x hx => hf x (by simp [hx])) i (by simpa [doublets] using hi)
        refine ⟨by simp only [hp,doublets,List.length_cons]; omega,?_⟩
        simpa only [hp, doublets, List.getElem_cons_succ] using e

theorem normalize_diagonal {m : Operation} (law : Law m) :
    ∃ (m' : Operation) (k j : Nat), Law m' ∧ DiagNormal m' k j := by
  classical
  let d := square m
  let Q := IsSquare m
  let I := (List.finRange 15).filter fun x => decide (d x = x)
  let A := (List.finRange 15).filter fun x => decide (Q x ∧ x < d x)
  let T := (List.finRange 15).filter fun x => decide (¬ Q x)
  let B := doublets d A
  let L := I ++ B ++ T
  have hi (x) : x ∈ I ↔ d x = x := by simp [I,List.mem_finRange]
  have ha (x) : x ∈ A ↔ Q x ∧ x < d x := by simp [A,List.mem_finRange]
  have ht (x) : x ∈ T ↔ ¬Q x := by simp [T,List.mem_finRange]
  have hI (x) (hx : x ∈ I) : Q x := ⟨x,(hi x).mp hx⟩
  have hii (x) (hx : Q x) : d (d x) = x := square_involutive law hx
  have hdq (x) : Q (d x) := ⟨x,rfl⟩
  have hb (x) : x ∈ B ↔ Q x ∧ d x ≠ x := by
    rw [show B = doublets d A from rfl,mem_doublets]
    constructor
    · rintro ⟨a,ha',h|h⟩ <;> subst x
      · obtain ⟨h,l⟩ := (ha a).mp ha'; exact ⟨h,(Fin.ne_of_lt l).symm⟩
      · obtain ⟨h,l⟩ := (ha a).mp ha'; exact ⟨hdq a,by rw [hii a h];exact Fin.ne_of_lt l⟩
    · rintro ⟨h,hn⟩
      by_cases hl : x < d x
      · exact ⟨x,(ha x).mpr ⟨h,hl⟩,Or.inl rfl⟩
      · exact ⟨d x,(ha _).mpr ⟨hdq x,by rw [hii x h]; grind [Fin.lt_def]⟩,Or.inr (hii x h).symm⟩
  have hnB : B.Nodup := nodup_doublets _ ((List.nodup_finRange 15).filter _) (by
    intro x hx; obtain ⟨q,l⟩ := (ha x).mp hx; exact ⟨l,hii x q⟩)
  have hnod : L.Nodup := by
    unfold L
    simp only [List.nodup_append,List.mem_append]
    refine ⟨⟨(List.nodup_finRange 15).filter _,hnB,?_⟩,(List.nodup_finRange 15).filter _,?_⟩
    · intro a ha' b hb' e; subst b; exact ((hb a).mp hb').2 ((hi a).mp ha')
    · intro a ha' b hb' e; subst b; apply (ht a).mp hb'
      rcases ha' with h|h; exact hI _ h; exact ((hb _).mp h).1
  have hmem (x : Vertex) : x ∈ L := by
    simp only [L, List.mem_append,hi,hb,ht]; by_cases q : Q x <;> by_cases h : d x=x <;> simp_all
  have hlen : L.length = 15 := by
    have e := (List.perm_ext_iff_of_nodup hnod (List.nodup_finRange 15)).mpr (by simp [hmem,List.mem_finRange])
    simpa using e.length_eq
  let p : Label := {
    old := fun a => L[a.val]'(by rw [hlen];exact a.isLt)
    idx := fun a => ⟨L.idxOf a,by have h := List.idxOf_lt_length_of_mem (hmem a); omega⟩
    idx_old := fun i => Fin.ext (hnod.idxOf_getElem ..)
    old_idx := fun i => List.getElem_idxOf _ }
  let j := I.length
  let k := I.length+B.length
  have sizes : k+T.length = 15 := by simpa [L,k,Nat.add_assoc] using hlen
  have inI (a : Vertex) (h : a.val<j) : p.old a = I[a.val] := by
    change (I++B++T)[a.val]'(by change a.val<L.length;rw [hlen];exact a.isLt) = _
    rw [List.getElem_append_left (by simp;omega),List.getElem_append_left h]
  have inB (a : Vertex) (lo : j≤a.val) (high : a.val<k) :
      p.old a = B[a.val-j]'(by dsimp [k,j] at *;omega) := by
    change (I++B++T)[a.val]'(by change a.val<L.length;rw [hlen];exact a.isLt) = _
    rw [List.getElem_append_left (by simpa [k] using high), List.getElem_append_right lo]
  have inT (a : Vertex) (lo : k≤a.val) : p.old a ∈ T := by
    change (I++B++T)[a.val]'(by change a.val<L.length;rw [hlen];exact a.isLt) ∈ T
    rw [List.getElem_append_right (by simpa [k] using lo)]
    exact List.getElem_mem ..
  have rangeQ (a : Vertex) : Q (p.old a) ↔ a.val<k := by
    constructor
    · intro h; by_cases hn : a.val < k; exact hn; exact False.elim ((ht _).mp (inT a (by omega)) h)
    · intro h; by_cases lt : a.val < j
      · rw [inI a lt]; exact hI _ (List.getElem_mem ..)
      · rw [inB a (by omega) h]; exact ((hb _).mp (List.getElem_mem ..)).1
  refine ⟨p.pull m,k,j,p.law law,⟨by omega,by dsimp [k,j];omega,?_,?_,?_⟩⟩
  · simp [k,j,B,len_doublets]
  · intro a; exact (p.isSq m a).trans (rangeQ a)
  · intro a ha'
    by_cases small : a.val<j
    · have e : d (p.old a) = p.old a := by rw [inI a small]; exact (hi _).mp (List.getElem_mem ..)
      change (p.idx (d (p.old a))).val = _
      rw [e,p.idx_old]; simp [partner,small]
    · have lo : j≤a.val := by omega
      have hbnd : a.val-j < B.length := by dsimp [k,j] at *;omega
      obtain ⟨hs,he⟩ := doublets_partner d A (fun x hx => hii x ((ha _).mp hx).1) (a.val-j) hbnd
      change partner 0 (a.val-j) < B.length at hs
      have hp : partner j a.val = j + partner 0 (a.val-j) := by
        simp [partner,small]; split <;> omega
      have hk : k = j+B.length := rfl
      let b : Vertex := ⟨partner j a.val,by omega⟩
      have bl : j ≤ b.val := by dsimp [b];omega
      have bh : b.val < k := by change partner j a.val < k;omega
      have eq : d (p.old a) = p.old b := by
        rw [inB a lo ha',inB b bl bh]; have ei : b.val-j = partner 0 (a.val-j) := by dsimp [b];omega
        simpa [ei] using he
      change (p.idx (d (p.old a))).val = _
      rw [eq,p.idx_old]

end E1486
