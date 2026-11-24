import Wall133.ShortGirthCertificateData
import Std.Sat.CNF.Basic

namespace Wall133.LabelledPathCertificate
open SimpleGraph FourthCertificate


/-- Graph constraints used to certify an induced path of order eight. -/
inductive Rule where
  | tip (i : ℕ)
  | transfer (i j k : ℕ)
  | square (i j c d : ℕ)
  | path (a b c d e f g h : ℕ)

private def sym (F : ℕ → ℕ → Bool) (i j : ℕ) : Bool := F (min i j) (max i j)

private def factBit (A E : ℕ → ℕ → Bool) : Fact → Bool
  | .edge i j => sym A i j
  | .nonedge i j => !(sym A i j)
  | .distinct i j => !(sym E i j)

private def pathBit (A : ℕ → ℕ → Bool) (a b c d e f g h : ℕ) : Bool :=
  (sym A a b) && !(sym A a c) && !(sym A a d) && !(sym A a e) && !(sym A a f) && !(sym A a g) && !(sym A a h) &&
  (sym A b c) && !(sym A b d) && !(sym A b e) && !(sym A b f) && !(sym A b g) && !(sym A b h) &&
  (sym A c d) && !(sym A c e) && !(sym A c f) && !(sym A c g) && !(sym A c h) &&
  (sym A d e) && !(sym A d f) && !(sym A d g) && !(sym A d h) &&
  (sym A e f) && !(sym A e g) && !(sym A e h) &&
  (sym A f g) && !(sym A f h) &&
  (sym A g h)

private def ruleBit (A E : ℕ → ℕ → Bool) : Rule → Bool
  | .tip i => !(sym A i 4) || sym E i 3 || sym A i 3
  | .transfer i j k => !(sym E i j) || !(sym A i k) || sym A j k
  | .square i j c d => sym E i j || sym E c d || !(sym A i c) || !(sym A i d) || !(sym A j c) || !(sym A j d)
  | .path a b c d e f g h => !(pathBit A a b c d e f g h)


private structure Literal where
  equality : Bool
  left : ℕ
  right : ℕ
  sign : Bool

private def edge (i j : ℕ) (b : Bool) : Literal := ⟨false,i,j,b⟩
private def eqn (i j : ℕ) (b : Bool) : Literal := ⟨true,i,j,b⟩

private def factLiterals : Fact → List Literal
  | .edge i j => [edge i j true]
  | .nonedge i j => [edge i j false]
  | .distinct i j => [eqn i j false]

private def ruleLiterals : Rule → List Literal
  | .tip i => [edge i 4 false,eqn i 3 true,edge i 3 true]
  | .transfer i j k => [eqn i j false,edge i k false,edge j k true]
  | .square i j c d => [eqn i j true,eqn c d true,edge i c false,edge i d false,edge j c false,edge j d false]
  | .path a b c d e f g h => [edge a b false, edge a c true, edge a d true, edge a e true, edge a f true, edge a g true, edge a h true,
    edge b c false, edge b d true, edge b e true, edge b f true, edge b g true, edge b h true,
    edge c d false, edge c e true, edge c f true, edge c g true, edge c h true,
    edge d e false, edge d f true, edge d g true, edge d h true,
    edge e f false, edge e g true, edge e h true,
    edge f g false, edge f h true,
    edge g h false]

private def Literal.value (A E : ℕ → ℕ → Bool) (t : Literal) : Bool :=
  sym (if t.equality then E else A) t.left t.right == t.sign

private def Literal.encode (n : ℕ) (t : Literal) : ℕ × Bool :=
  ((if t.equality then n*n else 0) + max t.left t.right*n + min t.left t.right,t.sign)

private def Literal.bounded (n : ℕ) (t : Literal) : Bool := decide (t.left<n ∧ t.right<n)

private def clauses (inputs : List Fact) (rules : List Rule) := inputs.map factLiterals ++ rules.map ruleLiterals

/-- Numerical variables encode unordered vertex-label pairs and their equalities. -/
def formulaOf (n : ℕ) (inputs : List Fact) (rules : List Rule) : Std.Sat.CNF ℕ :=
  ⟨((clauses inputs rules).map (List.map (Literal.encode n))).toArray⟩

def fits (n : ℕ) (inputs : List Fact) (rules : List Rule) : Bool :=
  (clauses inputs rules).all (fun c => c.all (Literal.bounded n))

private theorem factValue (A E : ℕ → ℕ → Bool) (t : Fact) :
    (factLiterals t).any (Literal.value A E) = factBit A E t := by
  cases t <;> simp [factLiterals, factBit, Literal.value,edge,eqn]

private theorem ruleValue (A E : ℕ → ℕ → Bool) (r : Rule) :
    (ruleLiterals r).any (Literal.value A E) = ruleBit A E r := by
  cases r <;> simp [ruleLiterals,ruleBit,Literal.value,edge,eqn,pathBit,Bool.not_and,Bool.or_assoc]

private def assignment (n : ℕ) (A E : ℕ → ℕ → Bool) (x : ℕ) : Bool :=
  if x < n*n then A (x%n) (x/n) else E ((x-n*n)%n) ((x-n*n)/n)

private theorem assignment_encode (n : ℕ) (A E : ℕ → ℕ → Bool) (t : Literal) (hb : t.bounded n) :
    ((assignment n A E (Literal.encode n t).1) == (Literal.encode n t).2) = t.value A E := by
  obtain ⟨q,i,j,s⟩ := t
  have ij : i<n ∧ j<n := of_decide_eq_true hb
  have small : min i j<n := lt_of_le_of_lt (min_le_left ..) ij.1
  have large : max i j<n := max_lt ij.1 ij.2
  let x := max i j*n + min i j
  have hn : 0<n := by omega
  have lt : x < n*n := by
    have bound := Nat.mul_le_mul_right n large
    rw [Nat.succ_mul] at bound
    dsimp [x]
    omega
  have rem : x % n = min i j := by simp [x,Nat.mod_eq_of_lt small]
  have quo : x / n = max i j := by
    rw [show x=n*(max i j)+min i j by simp [x,Nat.mul_comm],Nat.mul_add_div hn,Nat.div_eq_of_lt small,Nat.add_zero]
  cases q <;> simp only [Literal.encode,Literal.value,sym,assignment,Bool.false_eq_true,if_false,if_true,
    Nat.zero_add,Nat.add_assoc]
  · change ((if x<n*n then A (x%n) (x/n) else _) == s) = (A (min i j) (max i j) == s)
    simp only [if_pos lt,rem,quo]
  · change ((if n*n+x<n*n then _ else E ((n*n+x-n*n)%n) ((n*n+x-n*n)/n)) == s) =
      (E (min i j) (max i j) == s)
    simp only [show ¬n*n+x<n*n by omega,if_false,Nat.add_sub_cancel_left,rem,quo]

private theorem inconsistent (n : ℕ) (inputs : List Fact) (rules : List Rule)
    (bounded : fits n inputs rules) (unsat : (formulaOf n inputs rules).Unsat) (A E : ℕ → ℕ → Bool)
    (hf : inputs.all (factBit A E) = true) (hr : rules.all (ruleBit A E) = true) : False := by
  have evaluate (c) (hc : c∈clauses inputs rules) : c.any (Literal.value A E) = true := by
    rcases List.mem_append.mp hc with h|h
    · obtain ⟨t,ht,rfl⟩ := List.mem_map.mp h
      exact (factValue A E t).trans (List.all_eq_true.mp hf t ht)
    · obtain ⟨r,hr',rfl⟩ := List.mem_map.mp h
      exact (ruleValue A E r).trans (List.all_eq_true.mp hr r hr')
  have sat : (formulaOf n inputs rules).eval (assignment n A E) = true := by
    unfold Std.Sat.CNF.eval formulaOf
    apply Array.all_eq_true_iff_forall_mem.mpr
    intro d hd
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp (List.mem_toArray.mp hd)
    obtain ⟨t,ht,hv⟩ := List.any_eq_true.mp (evaluate _ hc)
    apply List.any_eq_true.mpr
    exact ⟨Literal.encode n t,List.mem_map.mpr ⟨t,ht,rfl⟩,
      (assignment_encode n A E t (List.all_eq_true.mp (List.all_eq_true.mp bounded c hc) t ht)).trans hv⟩
  exact Bool.noConfusion (sat.symm.trans (unsat (assignment n A E)))

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

omit [Fintype V] [DecidableEq V] in
private theorem symAdj [DecidableRel G.Adj] (f : ℕ → V) (i j) :
    sym (fun u v => decide (G.Adj (f u) (f v))) i j = decide (G.Adj (f i) (f j)) := by
  rcases le_total i j with hij|hji
  · simp [sym,min_eq_left hij,max_eq_right hij]
  · simp [sym,min_eq_right hji,max_eq_left hji,G.adj_comm]

omit [Fintype V] in
private theorem symEq (f : ℕ → V) (i j) :
    sym (fun u v => decide (f u=f v)) i j = decide (f i=f j) := by
  rcases le_total i j with hij|hji
  · simp [sym,min_eq_left hij,max_eq_right hij]
  · simp [sym,min_eq_right hji,max_eq_left hji,eq_comm]

set_option maxHeartbeats 1600000 in
private theorem eight_of_pathBit [DecidableRel G.Adj] (f : ℕ → V) (a b c d e t g h : ℕ)
    (hp : pathBit (fun u v => decide (G.Adj (f u) (f v))) a b c d e t g h = true) : 8≤G.path := by
  simp only [pathBit,symAdj,Bool.and_eq_true,Bool.not_eq_true',decide_eq_true_eq,decide_eq_false_iff_not,and_assoc] at hp
  obtain ⟨h01,h02,h03,h04,h05,h06,h07,h12,h13,h14,h15,h16,h17,h23,h24,h25,h26,h27,h34,h35,h36,h37,h45,h46,h47,h56,h57,h67⟩ := hp
  let p : Fin 8 → V := ![f a,f b,f c,f d,f e,f t,f g,f h]
  have edges (i j : Fin 8) : G.Adj (p i) (p j) ↔ i.val+1=j.val ∨ j.val+1=i.val := by
    fin_cases i <;> fin_cases j <;> dsimp [p]
    all_goals first | exact iff_of_true (by assumption) (by decide)
                    | exact iff_of_true (Adj.symm (by assumption)) (by decide)
                    | exact iff_of_false (by assumption) (by decide)
                    | exact iff_of_false (mt Adj.symm (by assumption)) (by decide)
                    | exact iff_of_false G.irrefl (by decide)
  apply path_bound_of_indices p _ edges
  have twins : ∀ a b : Fin 8, (∀ k : Fin 8,(a.val+1=k.val ∨ k.val+1=a.val) ↔
      (b.val+1=k.val ∨ k.val+1=b.val)) → a=b := by decide
  intro i j eq
  apply twins i j
  intro k
  exact (edges i k).symm.trans ((congrArg (fun z => G.Adj z (p k)) eq).to_iff.trans (edges j k))

/-- The listed local graph facts force an induced path on eight vertices. -/
theorem eight_of_unsat (n : ℕ) (inputs : List Fact) (rules : List Rule)
    (bounded : fits n inputs rules) (unsat : (formulaOf n inputs rules).Unsat)
    (f : ℕ → V) (h4 : NoFourCycle G)
    (simplicial : ∀ i,Rule.tip i∈rules → G.Adj (f i) (f 4) → f i≠f 3 → G.Adj (f i) (f 3))
    (facts : ∀ t∈inputs,Holds G f t) : 8≤G.path := by
  classical
  let A (i j : ℕ) := decide (G.Adj (f i) (f j))
  let E (i j : ℕ) := decide (f i=f j)
  by_contra short
  apply inconsistent n inputs rules bounded unsat A E
  · apply List.all_eq_true.mpr
    intro t ht
    have h := facts t ht
    cases t <;> simpa [factBit,A,E,symAdj,symEq,Holds] using h
  · apply List.all_eq_true.mpr
    intro r hr
    cases r with
    | tip i =>
      have tip := simplicial i hr
      simp [ruleBit,A,E,symAdj,symEq]
      grind
    | transfer i j k =>
      simp [ruleBit,A,E,symAdj,symEq]
      grind
    | square i j c d =>
      simp [ruleBit,A,E,symAdj,symEq]
      by_contra! h
      exact False.elim (by have noSquare := @h4 (f i) (f j) (f c) (f d); grind)
    | path a b c d e t g h =>
      change (!(pathBit A a b c d e t g h))=true
      have no := fun hp => short (eight_of_pathBit f a b c d e t g h hp)
      have eq : pathBit A a b c d e t g h=false := Bool.eq_false_iff.mpr no
      simp [eq]

end Wall133.LabelledPathCertificate
