/-
Soundness of the CNF encoding (Layer 2).

Goal (`Sound.lean`): if a set `D` of squares satisfies the constraints `CaseSat n k cs D` of a case, then the
CNF formula `QueenDomSat.caseFormula n k cs` of the case is satisfiable.  So, if the formulas of all cases
are unsatisfiable (and `k ≤ n - 2`), `k` queens do not dominate the board.  Files, in order:

* `Framework.lean`  choosing the fresh variables of one clause group after another; the sequential counter;
* `Base.lean`       the clauses about queens, occupied lines and their numbers;
* `Waste.lean`      the literals that count the three waste terms of the identities (F), (V), (H);
* `Extra.lean`      the frame and the bounds (F), (V), (H);
* `Sound.lean`      the statement above and its consequence for `γ`;
* `Gamma48.lean`    the `48 × 48` board.

The satisfying assignment is built group by group.  A clause group started at the variable counter `nv` uses
the fresh variables `nv + 1, ..., nv + m`, and the one notion needed is `Sound A nv m P`:

  if `A` holds by the values of the variables up to `nv`, then the variables `nv + 1, ..., nv + m` can be
  given values such that `P` holds, whatever the later variables are.

`Sound.fresh` proves it by giving these values; `Sound.bind` combines groups emitted one after the other.
-/
module

public import QueenDom.Cases
public import QueenDomSat

@[expose] public section

namespace QueenDom.Sat

open QueenDomSat

variable {σ τ : ℕ → Bool} {A B P Q : (ℕ → Bool) → Prop} {nv m m' : ℕ} {lits lits' : List ℤ}
  {bs bs' : List Bool} {cls cls' : List Clause}

/-! ### Literals and clauses under a valuation of the variables `1, 2, ...` -/

/-- The DIMACS literal `l` is true under the valuation `τ` (the variable `v` is the atom `v - 1`). -/
abbrev Lit (τ : ℕ → Bool) (l : ℤ) : Prop := LitTrue (fun i => τ (i + 1)) l

/-- Every clause of the list has a true literal. -/
def Holds (τ : ℕ → Bool) (cls : List Clause) : Prop := ∀ c ∈ cls, ∃ l ∈ c, Lit τ l

theorem lit_pos {v : ℕ} (hv : 0 < v) : Lit τ v ↔ τ v = true := by
  rw [Lit, litTrue_ofNat hv, Nat.sub_add_cancel hv]

theorem lit_neg {l : ℤ} (hl : l ≠ 0) : Lit τ (-l) ↔ ¬ Lit τ l := by
  rcases lt_or_gt_of_ne hl with h | h <;> simp [Lit, LitTrue, h, h.not_gt]

theorem var_ne_zero {v : ℕ} (hv : 0 < v) : (v : ℤ) ≠ 0 := by omega

theorem exists_lit_nil : ¬ ∃ l ∈ ([] : Clause), Lit τ l := by simp

theorem exists_lit_cons {l : ℤ} {c : Clause} : (∃ l' ∈ l :: c, Lit τ l') ↔ Lit τ l ∨ ∃ l' ∈ c, Lit τ l' :=
  List.exists_mem_cons_iff _ _ _

theorem holds_nil : Holds τ [] := by simp [Holds]

theorem holds_cons {c : Clause} : Holds τ (c :: cls) ↔ (∃ l ∈ c, Lit τ l) ∧ Holds τ cls :=
  List.forall_mem_cons

theorem holds_append : Holds τ (cls ++ cls') ↔ Holds τ cls ∧ Holds τ cls' := List.forall_mem_append

theorem holds_map {α : Type} {l : List α} {f : α → Clause} :
    Holds τ (l.map f) ↔ ∀ x ∈ l, ∃ y ∈ f x, Lit τ y := List.forall_mem_map

theorem holds_flatMap {α : Type} {l : List α} {f : α → List Clause} :
    Holds τ (l.flatMap f) ↔ ∀ x ∈ l, Holds τ (f x) := by
  simp only [Holds, List.forall_mem_flatMap]

/-- The integer `l` is a literal (not `0`, so that `Value.neg` holds) with the value `b`. -/
def Value (τ : ℕ → Bool) (l : ℤ) (b : Bool) : Prop := l ≠ 0 ∧ (Lit τ l ↔ b = true)

/-- The literals `lits` have the values `bs`. -/
def Values (τ : ℕ → Bool) (lits : List ℤ) (bs : List Bool) : Prop := List.Forall₂ (Value τ) lits bs

theorem value_var {v : ℕ} (hv : 0 < v) {b : Bool} (h : τ v = b) : Value τ v b :=
  ⟨var_ne_zero hv, by rw [lit_pos hv, h]⟩

theorem Value.neg {l : ℤ} {b : Bool} (h : Value τ l b) : Value τ (-l) !b :=
  ⟨neg_ne_zero.mpr h.1, by rw [lit_neg h.1, h.2]; simp⟩

theorem values_map {α : Type} {l : List α} {f : α → ℤ} {g : α → Bool} (h : ∀ x ∈ l, Value τ (f x) (g x)) :
    Values τ (l.map f) (l.map g) := by
  simpa [Values, List.forall₂_same] using h

theorem values_replicate {l : ℤ} {b : Bool} (h : Value τ l b) (m : ℕ) :
    Values τ (List.replicate m l) (List.replicate m b) := by
  induction m with
  | zero => exact .nil
  | succ m ih => exact .cons h ih

theorem Values.append (h : Values τ lits bs) (h' : Values τ lits' bs') :
    Values τ (lits ++ lits') (bs ++ bs') :=
  List.rel_append h h'

theorem Values.neg (h : Values τ lits bs) : Values τ (lits.map fun l => -l) (bs.map not) := by
  simp only [Values, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  exact h.imp fun _ _ => Value.neg

theorem Values.getElem? (h : Values τ lits bs) {i : ℕ} {l : ℤ} (hl : lits[i]? = some l) :
    ∃ b, bs[i]? = some b ∧ Value τ l b := by
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp hl
  have hi' : i < bs.length := h.length_eq ▸ hi
  exact ⟨bs[i], List.getElem?_eq_getElem hi', h.get hi hi'⟩

theorem count_map {α : Type} {l : List α} {f : α → Bool} : (l.map f).count true = l.countP f := by
  simp [List.count, List.countP_map, Function.comp_def]

/-! ### Choosing the values of the fresh variables -/

/-- `τ` agrees with `σ` up to the variable `nv`. -/
def Agree (σ τ : ℕ → Bool) (nv : ℕ) : Prop := ∀ v ≤ nv, τ v = σ v

theorem Agree.refl : Agree σ σ nv := fun _ _ => rfl

theorem Agree.trans {σ' : ℕ → Bool} (h : Agree σ σ' nv) (h' : Agree σ' τ (nv + m)) : Agree σ τ nv :=
  fun v hv => (h' v (Nat.le_add_right_of_le hv)).trans (h v hv)

/-- If `A` holds for all valuations that agree with `σ` up to `nv`, then `σ` can be changed above `nv` so that
`P` holds for all valuations that agree with it up to `nv + m`. -/
def Sound (A : (ℕ → Bool) → Prop) (nv m : ℕ) (P : (ℕ → Bool) → Prop) : Prop :=
  ∀ σ, (∀ τ, Agree σ τ nv → A τ) → ∃ σ', Agree σ σ' nv ∧ ∀ τ, Agree σ' τ (nv + m) → P τ

/-- To prove soundness, give the fresh variables the values `f 0, f 1, ...`. -/
theorem Sound.fresh (f : ℕ → Bool) (h : ∀ τ, A τ → (∀ j < m, τ (nv + j + 1) = f j) → P τ) :
    Sound A nv m P := by
  intro σ hσ
  let σ' v := if v ≤ nv then σ v else f (v - nv - 1)
  have ha : Agree σ σ' nv := fun v hv => ite_eq_left hv
  refine ⟨σ', ha, fun τ hτ => h τ (hσ τ (ha.trans hτ)) fun j hj => ?_⟩
  rw [hτ _ (by omega)]
  exact (ite_eq_right (by omega)).trans (congrArg f (by omega))

/-- The same with the values `f 0 0, ..., f 0 (K - 1), f 1 0, ...`. -/
theorem Sound.fresh₂ {M K : ℕ} (f : ℕ → ℕ → Bool)
    (h : ∀ τ, A τ → (∀ i < M, ∀ j < K, τ (nv + i * K + j + 1) = f i j) → P τ) : Sound A nv (M * K) P := by
  refine .fresh (fun t => f (t / K) (t % K)) fun τ hτ hf => h τ hτ fun i hi j hj => ?_
  have hK : 0 < K := by omega
  have hdiv : (i * K + j) / K = i := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hK, Nat.div_eq_of_lt hj, Nat.zero_add]
  have := hf (i * K + j) ((Nat.div_lt_iff_lt_mul hK).mp (by rwa [hdiv]))
  rwa [hdiv, Nat.mul_add_mod_of_lt hj, ← Nat.add_assoc] at this

theorem Sound.of_forall (h : ∀ τ, A τ → P τ) : Sound A nv m P := .fresh (fun _ => false) fun τ hτ _ => h τ hτ

theorem Sound.imp (h : Sound A nv m P) (hPQ : ∀ τ, A τ → P τ → Q τ) : Sound A nv m Q := by
  intro σ hσ
  obtain ⟨σ', ha, hP⟩ := h σ hσ
  exact ⟨σ', ha, fun τ hτ => hPQ τ (hσ τ (ha.trans hτ)) (hP τ hτ)⟩

theorem Sound.weaken (h : Sound A nv m P) (hBA : ∀ τ, B τ → A τ) : Sound B nv m P :=
  fun σ hσ => h σ fun τ hτ => hBA τ (hσ τ hτ)

/-- Two groups, one after the other: the second one starts where the first one stopped, and may use what
the first one has established. -/
theorem Sound.bind (h : Sound A nv m P) (h' : Sound (fun τ => A τ ∧ P τ) (nv + m) m' Q) :
    Sound A nv (m + m') fun τ => P τ ∧ Q τ := by
  intro σ hσ
  obtain ⟨σ₁, a₁, hP⟩ := h σ hσ
  obtain ⟨σ₂, a₂, hQ⟩ := h' σ₁ fun τ hτ => ⟨hσ τ (a₁.trans hτ), hP τ hτ⟩
  rw [← Nat.add_assoc]
  exact ⟨σ₂, a₁.trans a₂, fun τ hτ => ⟨hP τ (a₂.trans hτ), hQ τ hτ⟩⟩

/-- The same for clauses. -/
theorem Sound.append (h : Sound A nv m (Holds · cls)) (h' : Sound A (nv + m) m' (Holds · cls')) :
    Sound A nv (m + m') (Holds · (cls ++ cls')) :=
  (h.bind (h'.weaken fun _ => And.left)).imp fun _ _ => holds_append.mpr

/-- A loop over a list `xs` that allocates one fresh variable `f` per element `x` and emits the clause
`cl x f`.  If the clause is true whenever `f` has the value `val x`, then the fresh variables can be given
these values, and all clauses of the loop hold. -/
theorem loop_sound {α : Type} (xs : List α) (val : α → Bool) (cl : α → ℤ → Clause)
    (h : ∀ τ, A τ → ∀ x ∈ xs, ∀ f, (Lit τ f ↔ val x = true) → ∃ l ∈ cl x f, Lit τ l) :
    Sound A nv xs.length fun τ =>
      Holds τ (xs.zipIdx.map fun p => cl p.1 ((nv + p.2 + 1 : ℕ) : ℤ)) ∧
      Values τ ((List.range xs.length).map fun j => ((nv + j + 1 : ℕ) : ℤ)) (xs.map val) := by
  refine .fresh (fun j => xs[j]?.any val) fun τ hτ hf => ?_
  have hf (j : ℕ) (hj : j < xs.length) : Value τ ((nv + j + 1 : ℕ) : ℤ) (val xs[j]) :=
    value_var (Nat.succ_pos _) (by simp [hf j hj, hj])
  constructor
  · rw [holds_map]
    rintro ⟨x, j⟩ hxj
    obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.mp (List.mk_mem_zipIdx_iff_getElem?.mp hxj)
    exact h τ hτ _ (List.getElem_mem hj) _ (hf j hj).2
  · refine List.forall₂_iff_get.mpr ⟨by simp, fun j hj _ => ?_⟩
    simpa using hf j (by simpa using hj)

/-! ### The sequential counter -/

/-- The main branch of `atmostCls`.  Let `C i` be the number of true literals among the first `i`.  The counter
variable `s[i][j]` gets the value `j < C (i + 1)`; then every clause is a disjunction of inequalities, true
because `C 0 = 0`, `C i ≤ C (i + 1) ≤ C i + 1` and all `C i` are at most `K`. -/
theorem atmostSeq_sound {K : ℕ} (hK : 0 < K) (hlen : K < lits.length) (hv : ∀ τ, A τ → Values τ lits bs)
    (hc : bs.count true ≤ K) : Sound A nv ((lits.length - 1) * K) (Holds · (atmostSeq lits K nv)) := by
  let C i := (bs.take i).count true
  refine .fresh₂ (fun i j => decide (j < C (i + 1))) fun τ hτ hs => ?_
  -- the counter literals
  have pos (i j : ℕ) (hi : i + 1 < lits.length) (hj : j < K) : Lit τ (seqVar nv K i j) ↔ j < C (i + 1) := by
    rw [seqVar, lit_pos (Nat.succ_pos _), hs i (by omega) j hj, decide_eq_true_eq]
  have neg (i j : ℕ) (hi : i + 1 < lits.length) (hj : j < K) : Lit τ (-seqVar nv K i j) ↔ C (i + 1) ≤ j :=
    (lit_neg (var_ne_zero (Nat.succ_pos _))).trans ((pos i j hi hj).not.trans not_lt)
  -- the literal `l = lits[i]` of the row
  refine holds_flatMap.mpr fun ⟨l, i⟩ hli => ?_
  have hil : lits[i]? = some l := List.mk_mem_zipIdx_iff_getElem?.mp hli
  have hi : i < lits.length := (List.getElem?_eq_some_iff.mp hil).1
  obtain ⟨b, hib, hb⟩ := (hv τ hτ).getElem? hil
  obtain ⟨hl, h1, h2⟩ : (Lit τ (-l) ↔ C (i + 1) ≤ C i) ∧ C i ≤ C (i + 1) ∧ C (i + 1) ≤ C i + 1 := by
    rw [hb.neg.2]
    cases b <;> simp [C, List.take_add_one, hib]
  have h3 : C (i + 1) ≤ K := ((List.take_sublist _ bs).count_le true).trans hc
  -- the clauses of the row
  rcases i with _ | i
  · have h0 : C 0 = 0 := rfl
    simp only [atmostRow, ite_true, holds_cons, holds_map, List.mem_range'_1, exists_lit_cons, exists_lit_nil,
      or_false]
    refine ⟨?_, fun j hj => ?_⟩ <;> simp (disch := omega) only [hl, pos, neg] <;> omega
  · simp only [atmostRow, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel]
    split_ifs with hlast <;> simp only [holds_cons, holds_append, holds_flatMap, holds_nil, List.mem_range'_1,
      exists_lit_cons, exists_lit_nil, or_false, and_true]
    · refine ⟨?_, ?_, fun j hj => ⟨?_, ?_⟩, ?_⟩ <;> simp (disch := omega) only [hl, pos, neg] <;> omega
    · simp (disch := omega) only [hl, neg]
      omega

/-- **The clauses of `atmostCls`.**  If at most `k` of the literals are true, the clauses can be made true by
the choice of the fresh variables. -/
theorem atmost_sound {k : ℤ} (hv : ∀ τ, A τ → Values τ lits bs) (hc : (bs.count true : ℤ) ≤ k) :
    Sound A nv (atmostNew lits.length k) (Holds · (atmostCls lits k nv)) := by
  rcases le_or_gt (lits.length : ℤ) k with h1 | h1
  · rw [atmostCls_of_le (by omega) h1]
    exact .of_forall fun _ _ => holds_nil
  rcases eq_or_ne k 0 with rfl | h2
  · rw [atmostCls_zero (by rintro rfl; simp at h1)]
    refine .of_forall fun τ hτ => holds_map.mpr fun l hl => ⟨-l, List.mem_singleton_self _, ?_⟩
    obtain ⟨i, hil⟩ := List.mem_iff_getElem?.mp hl
    obtain ⟨b, hib, hlb⟩ := (hv τ hτ).getElem? hil
    have hb : b ≠ true := fun e =>
      List.count_eq_zero.mp (show bs.count true = 0 by omega) (e ▸ List.mem_of_getElem? hib)
    simp [hlb.neg.2, hb]
  · rw [atmostCls_main (by omega) h1, atmostNew_main (by omega) h1]
    exact atmostSeq_sound (by omega) (by omega) hv (by omega)

/-- **The clauses of `exactlyCls`**: the same if exactly `k` of the literals are true. -/
theorem exactly_sound {k : ℤ} (hv : ∀ τ, A τ → Values τ lits bs) (hc : (bs.count true : ℤ) = k) :
    Sound A nv (exactlyNew lits.length k) (Holds · (exactlyCls lits k nv)) := by
  intro σ hσ
  have hc' : (bs.map not).count true + bs.count true = lits.length := by
    rw [(hv σ (hσ σ .refl)).length_eq, ← List.count_not_add_count bs true]
    congr 1
    exact List.count_map_of_injective bs not Bool.not_injective false
  have := atmost_sound (nv := nv + atmostNew lits.length k) (k := lits.length - k)
    (fun τ hτ => (hv τ hτ).neg) (by omega)
  rw [List.length_map] at this
  exact (atmost_sound hv hc.le).append this σ hσ

end QueenDom.Sat
