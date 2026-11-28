/-
Soundness of the CNF encoding (Layer 2): the base formula (`QueenDomSat.baseClauses`).

A set `D` of squares gives the valuation `boardVal D` of the variables `q, oR, oC, oT, oS`.  The squares, the
rows, the columns and the two sorts of diagonals are treated once, as instances of `Kind`.

Besides the cardinality constraints, the base formula says: DEF, the variable of a line is true iff one of its
squares carries a queen; DOM, every square lies on an occupied line; AMO, a line of a sort with deficit `0`
carries at most one queen.
-/
module

public import Queens48.Framework

@[expose] public section

namespace QueenDom.Sat

open QueenDomSat Finset

variable {n : ℕ} {D : Finset (Sq n)} {τ : ℕ → Bool}

/-! ### The valuation given by a set of squares -/

/-- The variable `q[x][y]` of a square. -/
def sqv (p : Sq n) : ℕ := qv n p.1 p.2

/-- `v` is the variable of the square `p` or of one of the four lines through `p`. -/
def VarOf (p : Sq n) (v : ℕ) : Prop :=
  v = sqv p ∨ v = oRv n p.2 ∨ v = oCv n p.1 ∨ v = oTv n (tIdx n p.1 p.2) ∨ v = oSv n (p.1 + p.2)

instance (p : Sq n) (v : ℕ) : Decidable (VarOf p v) := by unfold VarOf; infer_instance

/-- The variables of the squares of `D` and of the lines through them are true. -/
def boardVal (D : Finset (Sq n)) (v : ℕ) : Bool := decide (∃ p ∈ D, VarOf p v)

/-- `v` is one of the variables `q, oR, oC, oT, oS` (the first `baseVars n`). -/
def IsBoardVar (n v : ℕ) : Prop := 0 < v ∧ v ≤ baseVars n

/-- `τ` has the values `boardVal D` on the variables `q, oR, oC, oT, oS`. -/
def Encodes (D : Finset (Sq n)) (τ : ℕ → Bool) : Prop := Agree (boardVal D) τ (baseVars n)

theorem Encodes.value (h : Encodes D τ) {v : ℕ} (hv : IsBoardVar n v) : Value τ v (boardVal D v) :=
  value_var hv.1 (h v hv.2)

theorem sqv_pos (p : Sq n) : 0 < sqv p := Nat.succ_pos _

/-- The variables of the squares are numbered like `Fin n × Fin n ≃ Fin (n * n)`. -/
theorem sqv_eq (p : Sq n) : sqv p = finProdFinEquiv p + 1 := by
  rw [finProdFinEquiv_apply_val, sqv, qv, add_comm (p.2 : ℕ), mul_comm n]

theorem sqv_le (p : Sq n) : sqv p ≤ n * n := by
  rw [sqv_eq]; exact (finProdFinEquiv p).isLt

theorem sqv_injective : Function.Injective (sqv (n := n)) := fun p q h =>
  finProdFinEquiv.injective (Fin.ext (by simpa only [sqv_eq, Nat.add_right_cancel_iff] using h))

/-! ### Squares, rows, columns, diagonals -/

/-- A classification of the squares (by the square itself, its row, its column or a diagonal) into the classes
`0, ..., num - 1`.  The variable `var i` says that some square of `D` is in the class `i`. -/
structure Kind (n : ℕ) where
  /-- the number of classes -/
  num : ℕ
  /-- the class of a square -/
  key : Sq n → ℕ
  /-- the variable of a class -/
  var : ℕ → ℕ
  key_lt : ∀ p, key p < num
  isBoardVar : ∀ i < num, IsBoardVar n (var i)
  varOf_iff : ∀ p, ∀ i < num, VarOf p (var i) ↔ key p = i

/-- Every square is a class of its own. -/
def Kind.Q : Kind n where
  num := n * n
  key p := p.1 * n + p.2
  var i := i + 1
  key_lt p := sqv_le p
  isBoardVar i hi := by unfold IsBoardVar baseVars; omega
  varOf_iff p i hi := by simp only [VarOf, sqv, qv, oRv, oCv, oTv, oSv]; omega

/-- The rows. -/
def Kind.R : Kind n where
  num := n
  key p := p.2
  var := oRv n
  key_lt p := p.2.isLt
  isBoardVar i hi := by unfold IsBoardVar oRv baseVars; omega
  varOf_iff p i hi := by have := sqv_le p; simp only [VarOf, oRv, oCv, oTv, oSv]; omega

/-- The columns. -/
def Kind.C : Kind n where
  num := n
  key p := p.1
  var := oCv n
  key_lt p := p.1.isLt
  isBoardVar i hi := by unfold IsBoardVar oCv baseVars; omega
  varOf_iff p i hi := by have := sqv_le p; simp only [VarOf, oRv, oCv, oTv, oSv]; omega

/-- The difference diagonals. -/
def Kind.T : Kind n where
  num := 2 * n - 1
  key p := tIdx n p.1 p.2
  var := oTv n
  key_lt p := by unfold tIdx; omega
  isBoardVar i hi := by unfold IsBoardVar oTv baseVars; omega
  varOf_iff p i hi := by have := sqv_le p; simp only [VarOf, oRv, oCv, oTv, oSv, tIdx]; omega

/-- The sum diagonals. -/
def Kind.S : Kind n where
  num := 2 * n - 1
  key p := p.1 + p.2
  var := oSv n
  key_lt p := by omega
  isBoardVar i hi := by unfold IsBoardVar oSv baseVars; omega
  varOf_iff p i hi := by have := sqv_le p; simp only [VarOf, oRv, oCv, oTv, oSv, tIdx]; omega

theorem Kind.Q_injective : Function.Injective (Kind.Q (n := n)).key := fun _ _ e =>
  sqv_injective (congrArg Nat.succ e)

theorem tIdx_eq_iff {p q : Sq n} : tIdx n p.1 p.2 = tIdx n q.1 q.2 ↔ dg p = dg q := by
  unfold tIdx dg; omega

theorem Kind.image_subset (K : Kind n) (D : Finset (Sq n)) : D.image K.key ⊆ range K.num :=
  image_subset_iff.mpr fun p _ => mem_range.mpr (K.key_lt p)

/-- The variable of a class is true iff the class is occupied. -/
theorem Kind.val (K : Kind n) {i : ℕ} (hi : i < K.num) :
    boardVal D (K.var i) = true ↔ i ∈ D.image K.key := by
  simp only [boardVal, decide_eq_true_eq, K.varOf_iff _ i hi, mem_image]

theorem val_R (y : Fin n) : boardVal D (oRv n y) = true ↔ y ∈ occR D := by
  rw [mem_occR]; simp only [Fin.ext_iff]; exact (Kind.R.val y.isLt).trans mem_image

theorem val_C (x : Fin n) : boardVal D (oCv n x) = true ↔ x ∈ occC D := by
  rw [mem_occC]; simp only [Fin.ext_iff]; exact (Kind.C.val x.isLt).trans mem_image

theorem val_T (p : Sq n) : boardVal D (oTv n (tIdx n p.1 p.2)) = true ↔ dg p ∈ occT D := by
  rw [mem_occT]; simp only [← tIdx_eq_iff]; exact (Kind.T.val (Kind.T.key_lt p)).trans mem_image

theorem val_S (p : Sq n) : boardVal D (oSv n (p.1 + p.2)) = true ↔ sm p ∈ occS D :=
  Kind.S.val (Kind.S.key_lt p)

section

variable (hτ : Encodes D τ)

include hτ

theorem Kind.lit_var (K : Kind n) {i : ℕ} (hi : i < K.num) : Lit τ (K.var i) ↔ i ∈ D.image K.key :=
  (hτ.value (K.isBoardVar i hi)).2.trans (K.val hi)

theorem Kind.lit_neg_var (K : Kind n) {i : ℕ} (hi : i < K.num) : Lit τ (-K.var i) ↔ i ∉ D.image K.key :=
  (lit_neg (var_ne_zero (K.isBoardVar i hi).1)).trans (K.lit_var hτ hi).not

theorem lit_sqv {p : Sq n} : Lit τ (sqv p) ↔ p ∈ D :=
  (Kind.Q.lit_var hτ (Kind.Q.key_lt p)).trans Kind.Q_injective.mem_finset_image

theorem lit_neg_sqv {p : Sq n} : Lit τ (-sqv p) ↔ p ∉ D :=
  (lit_neg (var_ne_zero (sqv_pos p))).trans (lit_sqv hτ).not

theorem lit_R (y : Fin n) : Lit τ (oRv n y) ↔ y ∈ occR D :=
  (hτ.value (Kind.R.isBoardVar y y.isLt)).2.trans (val_R y)

theorem lit_C (x : Fin n) : Lit τ (oCv n x) ↔ x ∈ occC D :=
  (hτ.value (Kind.C.isBoardVar x x.isLt)).2.trans (val_C x)

theorem lit_T (p : Sq n) : Lit τ (oTv n (tIdx n p.1 p.2)) ↔ dg p ∈ occT D :=
  (hτ.value (Kind.T.isBoardVar _ (Kind.T.key_lt p))).2.trans (val_T p)

theorem lit_S (p : Sq n) : Lit τ (oSv n (p.1 + p.2)) ↔ sm p ∈ occS D :=
  (hτ.value (Kind.S.isBoardVar _ (Kind.S.key_lt p))).2.trans (val_S p)

/-! ### DOM -/

theorem holds_domCls (hD : Dominating D) : Holds τ (domCls n) := by
  simp only [domCls, holds_flatMap, holds_map, List.mem_range, exists_lit_cons, exists_lit_nil, or_false]
  intro x hx y hy
  have hp := (dominating_iff D).mp hD (⟨x, hx⟩, ⟨y, hy⟩)
  exact hp.imp (lit_R hτ _).mpr (.imp (lit_C hτ _).mpr (.imp (lit_T hτ _).mpr (lit_S hτ _).mpr))

end

/-! ### DEF and AMO -/

/-- `line i` lists the variables of the squares of the class `i`, each once. -/
def Kind.Lines (K : Kind n) (line : ℕ → List ℕ) : Prop :=
  ∀ i < K.num, (line i).Nodup ∧ ∀ v, v ∈ line i ↔ ∃ p, K.key p = i ∧ sqv p = v

/-- A line listed by a coordinate `f` of its squares: `l` lists the values of `f` on the line, and the square
with the value `x` has the variable `g x`. -/
theorem line_ok {key f : Sq n → ℕ} {g : ℕ → ℕ} {l : List ℕ} {i : ℕ} (hl : l.Nodup)
    (hf : ∀ x, x ∈ l ↔ ∃ p, key p = i ∧ f p = x) (hg : ∀ p, key p = i → g (f p) = sqv p) :
    (l.map g).Nodup ∧ ∀ v, v ∈ l.map g ↔ ∃ p, key p = i ∧ sqv p = v := by
  refine ⟨hl.map_on fun x hx x' hx' e => ?_, fun v => ?_⟩
  · obtain ⟨p, hp, rfl⟩ := (hf x).mp hx
    obtain ⟨q, hq, rfl⟩ := (hf x').mp hx'
    rw [hg p hp, hg q hq] at e
    rw [sqv_injective e]
  · simp only [List.mem_map, hf, exists_exists_and_eq_and]
    exact exists_congr fun p => and_congr_right fun hp => by rw [hg p hp]

theorem lines_R : (Kind.R (n := n)).Lines (lineR n) := fun i hi =>
  line_ok (f := fun p => p.1) List.nodup_range
    (fun x => List.mem_range.trans
      ⟨fun hx => ⟨(⟨x, hx⟩, ⟨i, hi⟩), rfl, rfl⟩, by rintro ⟨p, -, rfl⟩; exact p.1.isLt⟩)
    (by rintro p rfl; rfl)

theorem lines_C : (Kind.C (n := n)).Lines (lineC n) := fun i hi =>
  line_ok (f := fun p => p.2) List.nodup_range
    (fun y => List.mem_range.trans
      ⟨fun hy => ⟨(⟨i, hi⟩, ⟨y, hy⟩), rfl, rfl⟩, by rintro ⟨p, -, rfl⟩; exact p.2.isLt⟩)
    (by rintro p rfl; rfl)

theorem lines_T : (Kind.T (n := n)).Lines (lineT n) := fun i hi =>
  line_ok (f := fun p => p.1) (List.nodup_range.filter _)
    (fun x => by
      simp only [List.mem_filter, List.mem_range, decide_eq_true_eq, Kind.T, tIdx]
      exact ⟨fun hx => ⟨(⟨x, hx.1⟩, ⟨_, hx.2.2⟩), by dsimp only; omega, rfl⟩, by rintro ⟨p, rfl, rfl⟩; omega⟩)
    (by rintro p rfl; simp only [qv, sqv, Kind.T, tIdx]; omega)

theorem lines_S : (Kind.S (n := n)).Lines (lineS n) := fun i hi =>
  line_ok (f := fun p => p.1) (List.nodup_range.filter _)
    (fun x => by
      simp only [List.mem_filter, List.mem_range, decide_eq_true_eq, Kind.S]
      exact ⟨fun hx => ⟨(⟨x, hx.1⟩, ⟨_, hx.2.2⟩), by dsimp only; omega, rfl⟩, by rintro ⟨p, rfl, rfl⟩; omega⟩)
    (by rintro p rfl; simp only [qv, sqv, Kind.S]; omega)

theorem holds_amoLine {qs : List ℕ} :
    Holds τ (amoLine qs) ↔ qs.Pairwise fun u v : ℕ => Lit τ (-u) ∨ Lit τ (-v) := by
  induction qs with
  | nil => simp [amoLine, holds_nil]
  | cons q qs ih => simp [amoLine, holds_append, holds_map, ih]

section

variable (hτ : Encodes D τ) {K : Kind n} {line : ℕ → List ℕ} (hK : K.Lines line)

include hτ

include hK in
/-- DEF for the lines of one kind. -/
theorem holds_defKind : Holds τ
    (((List.range K.num).map fun i => (K.var i, line i)).flatMap fun p => defLine p.1 p.2) := by
  rw [holds_flatMap, List.forall_mem_map]
  intro i hi
  have hi := List.mem_range.mp hi
  have hmem := (hK i hi).2
  simp only [defLine, holds_append, holds_map, holds_cons, holds_nil, exists_lit_cons, exists_lit_nil,
    or_false, and_true, List.mem_map, exists_exists_and_eq_and]
  constructor
  · intro v hv
    obtain ⟨p, rfl, rfl⟩ := (hmem v).mp hv
    rw [lit_neg_sqv hτ, K.lit_var hτ hi, ← imp_iff_not_or]
    exact mem_image_of_mem K.key
  · rw [K.lit_neg_var hτ hi, ← imp_iff_not_or, mem_image]
    rintro ⟨p, hp, hk⟩
    exact ⟨sqv p, (hmem _).mpr ⟨p, hk, rfl⟩, (lit_sqv hτ).mpr hp⟩

include hK in
/-- AMO for the lines of one kind. -/
theorem holds_amoKind (hD : Set.InjOn K.key D) :
    Holds τ (amoFam ((List.range K.num).map fun i => (K.var i, line i))) := by
  rw [amoFam, holds_flatMap, List.forall_mem_map]
  intro i hi
  obtain ⟨hnd, hmem⟩ := hK i (List.mem_range.mp hi)
  refine holds_amoLine.mpr (hnd.imp_of_mem fun {u v} hu hv hne => ?_)
  obtain ⟨p, hp, rfl⟩ := (hmem u).mp hu
  obtain ⟨q, hq, rfl⟩ := (hmem v).mp hv
  rw [lit_neg_sqv hτ, lit_neg_sqv hτ, ← not_and_or]
  exact fun h => hne (congrArg sqv (hD h.1 h.2 (hp.trans hq.symm)))

theorem holds_defCls : Holds τ (defCls n) := by
  simp only [defCls, fam, List.flatMap_append, holds_append]
  exact ⟨holds_defKind hτ lines_R, holds_defKind hτ lines_C, holds_defKind hτ lines_T, holds_defKind hτ lines_S⟩

theorem holds_amoCls {k : ℕ} {cs : Case} (h : CaseSat n k cs D) :
    Holds τ (amoCls n cs.dR cs.dC cs.dT cs.dS) := by
  simp only [amoCls, holds_append]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> split_ifs with h0 <;> try exact holds_nil
  · exact holds_amoKind hτ lines_R fun p hp q hq e => h.amoR h0 hp hq (Fin.ext e)
  · exact holds_amoKind hτ lines_C fun p hp q hq e => h.amoC h0 hp hq (Fin.ext e)
  · exact holds_amoKind hτ lines_T fun p hp q hq e => h.amoT h0 hp hq (tIdx_eq_iff.mp e)
  · exact holds_amoKind hτ lines_S (h.amoS h0)

end

/-! ### The cardinality constraints -/

/-- Counting in a list without repetition is counting in a finite set. -/
theorem countP_eq_card {α : Type} [DecidableEq α] {l : List α} (hl : l.Nodup) {p : α → Bool} {S : Finset α}
    (h : ∀ a, a ∈ S ↔ a ∈ l ∧ p a = true) : l.countP p = S.card := by
  have hS : S = l.toFinset.filter (p · = true) := by ext a; simp [h]
  rw [hS, hl.card_eq_countP]; simp

/-- `enc.exactly` on the variables of one kind, if `k` classes are occupied. -/
theorem Kind.exactly_sound (K : Kind n) {nv : ℕ} {k : ℤ} (hc : (D.image K.key).card = k) :
    Sound (Encodes D) nv (exactlyNew K.num k)
      (Holds · (exactlyCls ((List.range K.num).map fun i => (K.var i : ℤ)) k nv)) := by
  have hv (τ : ℕ → Bool) (hτ : Encodes D τ) : Values τ ((List.range K.num).map fun i => (K.var i : ℤ))
      ((List.range K.num).map fun i => boardVal D (K.var i)) :=
    values_map fun i hi => hτ.value (K.isBoardVar i (List.mem_range.mp hi))
  have hcard : ((List.range K.num).map fun i => boardVal D (K.var i)).count true = (D.image K.key).card := by
    refine count_map.trans (countP_eq_card List.nodup_range fun i => ?_)
    rw [List.mem_range, and_congr_right K.val, and_iff_right_of_imp fun h => mem_range.mp (K.image_subset D h)]
  have := QueenDom.Sat.exactly_sound (nv := nv) hv (by rw [hcard, hc])
  rwa [List.length_map, List.length_range] at this

/-- `0, ..., m * k - 1` in `m` rows of length `k`. -/
theorem range_mul (m k : ℕ) :
    List.range (m * k) = (List.range m).flatMap fun x => (List.range k).map fun y => x * k + y := by
  induction m with
  | zero => simp
  | succ m ih => simp [Nat.succ_mul, List.range_add, ih, List.range_succ]

theorem qLits_eq : qLits n = (List.range (n * n)).map fun i => ((i + 1 : ℕ) : ℤ) := by
  simp only [range_mul, List.map_flatMap, List.map_map]
  rfl

/-- The difference diagonal with the index `i` is the diagonal `t = i - (n - 1)`. -/
theorem dg_eq (p : Sq n) : dg p = (Kind.T.key p : ℤ) - (n - 1) := by
  simp only [dg, Kind.T, tIdx]; omega

theorem tShift_injective : Function.Injective fun i : ℕ => (i : ℤ) - (n - 1) := fun a b e => by
  simpa using e

/-- **The clauses of `baseClauses`.** -/
theorem base_sound {k : ℕ} {cs : Case} (h : CaseSat n k cs D) :
    ∃ m, baseNv n k cs.dR cs.dC cs.dT cs.dS = baseVars n + m ∧
      Sound (Encodes D) (baseVars n) m (Holds · (baseClauses n k cs.dR cs.dC cs.dT cs.dS)) := by
  -- the numbers of occupied classes
  have hR : (D.image Kind.R.key).card + cs.dR = k := by
    rw [← h.cardR, occR, ← card_image_of_injective _ Fin.val_injective, image_image]; rfl
  have hC : (D.image Kind.C.key).card + cs.dC = k := by
    rw [← h.cardC, occC, ← card_image_of_injective _ Fin.val_injective, image_image]; rfl
  have hT : (D.image Kind.T.key).card + cs.dT = k := by
    rw [← h.cardT, occT, funext dg_eq, ← card_image_of_injective _ (tShift_injective (n := n)), image_image]; rfl
  have hS : (D.image Kind.S.key).card + cs.dS = k := h.cardS
  have hQ : (D.image Kind.Q.key).card = k := h.card ▸ card_image_of_injective D Kind.Q_injective
  -- the five groups with counters
  have queens : Sound (Encodes D) (nvCardEnd n k cs.dR cs.dC cs.dT cs.dS)
      (if NoZero cs.dR cs.dC cs.dT cs.dS then exactlyNew (n * n) k else 0)
      (Holds · (queensCls n k cs.dR cs.dC cs.dT cs.dS)) := by
    unfold queensCls
    split_ifs
    · rw [qLits_eq]; exact Kind.Q.exactly_sound (by omega)
    · exact .of_forall fun _ _ => holds_nil
  have groups := (Kind.R.exactly_sound (k := k - cs.dR) (by omega)).append <|
    (Kind.C.exactly_sound (k := k - cs.dC) (by omega)).append <|
    (Kind.T.exactly_sound (k := k - cs.dT) (by omega)).append <|
    (Kind.S.exactly_sound (k := k - cs.dS) (by omega)).append queens
  refine ⟨_, ?_, groups.imp fun τ hτ hH => ?_⟩
  · simp only [baseNv, nvCardEnd, nvCardS, nvCardT, nvCardC, nvCardR, Nat.add_assoc]
    rfl
  · simp only [baseClauses, cardCls, holds_append] at hH ⊢
    obtain ⟨h1, h2, h3, h4, h5⟩ := hH
    exact ⟨holds_defCls hτ, holds_domCls hτ h.dom, ⟨h1, h2, h3, h4⟩, holds_amoCls hτ h, h5⟩

end QueenDom.Sat
