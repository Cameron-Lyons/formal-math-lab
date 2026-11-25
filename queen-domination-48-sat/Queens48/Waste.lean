/-
Soundness of the CNF encoding (Layer 2): the waste literals (`QueenDomSat.waste`).

For a set `X` of squares of the border of the frame, `waste` emits three sorts of literals.

* For a diagonal `L` with `β` squares of `X`: copies of its variable, `2 - β` of them (`full`, for the border),
  or one if `β = 0` (for the sides).  The true ones number `wasteF D X`, or `zeros D X`.
* For a diagonal `L` and a square of `X` on `L` that is not a corner: a fresh variable, true iff `L` is occupied
  and the square is not needy.  The true ones number `waste2 D X`.
* For a square of `X`: a fresh variable, true iff the square is needy and both its diagonals are occupied.  The
  true ones number `needy2 D X`.

`waste_sound`: the clauses can be satisfied, with literals of these values.  `count_wasteValues`: the number of
true literals is the sum of the three waste terms of the identity (F), (V) or (H).

`nl` stands for `nonneedy` of a square: the variable that says that the square is not needy (none for the
corners, which are needy).
-/
module

public import Queens48.Base

@[expose] public section

namespace QueenDom.Sat

open QueenDomSat Finset

variable {n : ℕ} {D X : Finset (Sq n)} {a b c d : Fin n} {sqs : List (ℕ × ℕ)} {nv : ℕ}

/-! ### The clauses of `waste` -/

/-- If the board variables have the values given by `D`, the fresh variables of `W`, started at the counter
`nv`, can be chosen so that its clauses hold and its literals have the values `bs`. -/
def WasteSound (D : Finset (Sq n)) (nv : ℕ) (W : Waste) (bs : List Bool) : Prop :=
  Sound (Encodes D) nv W.new fun τ => Holds τ W.cls ∧ Values τ W.lits bs

/-- Two parts of `waste`, one after the other. -/
theorem WasteSound.append {W W' : Waste} {bs bs' : List Bool} (h : WasteSound D nv W bs)
    (h' : WasteSound D (nv + W.new) W' bs') :
    WasteSound D nv ⟨W.cls ++ W'.cls, W.lits ++ W'.lits, W.new + W'.new⟩ (bs ++ bs') :=
  (h.bind (h'.weaken fun _ => And.left)).imp fun _ _ h =>
    ⟨holds_append.mpr ⟨h.1.1, h.2.1⟩, h.1.2.append h.2.2⟩

/-- The values of the literals of one diagonal: the copies of its variable, then one literal for every `nl`,
true iff the diagonal is occupied and `nl` is true. -/
def lineValues (D : Finset (Sq n)) (full : Bool) (L : WLine) : List Bool :=
  List.replicate (lineCopies full L.onLen) (boardVal D L.lv) ++
    L.nls.map fun v => boardVal D L.lv && boardVal D v

/-- One diagonal. -/
theorem wasteLine_sound (full : Bool) {L : WLine} (hL : IsBoardVar n L.lv) (hnl : ∀ v ∈ L.nls, IsBoardVar n v) :
    WasteSound D nv ⟨wasteLineCls L nv, wasteLineLits full L nv, L.nls.length⟩ (lineValues D full L) := by
  refine (loop_sound L.nls (fun v => boardVal D L.lv && boardVal D v) (fun v f => [-(L.lv : ℤ), -(v : ℤ), f])
    fun τ hτ v hv f hf => ?_).imp fun τ hτ h => ⟨h.1, .append (values_replicate (hτ.value hL) _) h.2⟩
  simp only [exists_lit_cons, (hτ.value hL).neg.2, (hτ.value (hnl v hv)).neg.2, hf]
  cases boardVal D L.lv <;> cases boardVal D v <;> simp

/-- The loop over the diagonals. -/
theorem wasteLines_sound (full : Bool) {Ls : List WLine}
    (hLs : ∀ L ∈ Ls, IsBoardVar n L.lv ∧ ∀ v ∈ L.nls, IsBoardVar n v) :
    WasteSound D nv (wasteLines full Ls nv) (Ls.flatMap (lineValues D full)) := by
  induction Ls generalizing nv with
  | nil => exact .of_forall fun _ _ => ⟨holds_nil, .nil⟩
  | cons L Ls ih =>
    obtain ⟨hL, hLs⟩ := List.forall_mem_cons.mp hLs
    exact (wasteLine_sound full hL.1 hL.2).append (ih hLs)

/-- The value of the fresh variable of a square: both diagonals are occupied and `nl` (if any) is false. -/
def sqTrue (D : Finset (Sq n)) (a b c d : ℕ) (sq : ℕ × ℕ) : Bool :=
  boardVal D (oTv n (tIdx n sq.1 sq.2)) && boardVal D (oSv n (sq.1 + sq.2)) &&
    !(nonneedy n a b c d sq).any (boardVal D)

theorem isBoardVar_nonneedy {a b c d : ℕ} {sq : ℕ × ℕ} (h : sq.1 < n ∧ sq.2 < n) {v : ℕ}
    (hv : nonneedy n a b c d sq = some v) : IsBoardVar n v := by
  unfold nonneedy at hv
  split_ifs at hv <;> cases hv
  exacts [Kind.R.isBoardVar _ h.2, Kind.C.isBoardVar _ h.1]

/-- The loop over the squares. -/
theorem wasteSqs_sound (a b c d : ℕ) (hsq : ∀ sq ∈ sqs, sq.1 < n ∧ sq.2 < n) :
    WasteSound D nv
      ⟨wasteSqCls n a b c d sqs nv, (List.range sqs.length).map fun j => ((nv + j + 1 : ℕ) : ℤ), sqs.length⟩
      (sqs.map (sqTrue D a b c d)) := by
  refine loop_sound sqs (sqTrue D a b c d)
    (fun sq f => [-(oTv n (tIdx n sq.1 sq.2) : ℤ), -(oSv n (sq.1 + sq.2) : ℤ), f] ++
      (nonneedy n a b c d sq).toList.map fun v : ℕ => (v : ℤ)) fun τ hτ sq hs f hf => ?_
  have hlt := hsq sq hs
  have hT := hτ.value (Kind.T.isBoardVar (tIdx n sq.1 sq.2) (by simp only [Kind.T, tIdx]; omega))
  have hS := hτ.value (Kind.S.isBoardVar (sq.1 + sq.2) (by simp only [Kind.S]; omega))
  have hnl : (∃ l ∈ (nonneedy n a b c d sq).toList.map fun v : ℕ => (v : ℤ), Lit τ l) ↔
      (nonneedy n a b c d sq).any (boardVal D) = true := by
    cases hv : nonneedy n a b c d sq with
    | none => simp
    | some v => simp [(hτ.value (isBoardVar_nonneedy hlt hv)).2]
  simp only [List.cons_append, List.nil_append, exists_lit_cons, hnl, hf, sqTrue]
  rw [show Lit τ (-oTv n _) ↔ _ from hT.neg.2, show Lit τ (-oSv n _) ↔ _ from hS.neg.2]
  simp only [Kind.T, Kind.S, Bool.not_eq_true', Bool.and_eq_true, ← Bool.not_eq_true]
  tauto

theorem isBoardVar_wasteLineList {a b c d : ℕ} (hsq : ∀ sq ∈ sqs, sq.1 < n ∧ sq.2 < n) :
    ∀ L ∈ wasteLineList n a b c d sqs, IsBoardVar n L.lv ∧ ∀ v ∈ L.nls, IsBoardVar n v := by
  simp only [wasteLineList, List.forall_mem_append, List.forall_mem_map, List.mem_range, mkWLine,
    List.mem_filterMap]
  refine ⟨fun i hi => ⟨Kind.T.isBoardVar i hi, ?_⟩, fun i hi => ⟨Kind.S.isBoardVar i hi, ?_⟩⟩
  · rintro v ⟨sq, h, hv⟩; exact isBoardVar_nonneedy (hsq sq (mem_onT.mp h).2.2.2.2) hv
  · rintro v ⟨sq, h, hv⟩; exact isBoardVar_nonneedy (hsq sq (mem_onS.mp h).2.2.2) hv

/-- The values of the literals of `waste`. -/
def wasteValues (D : Finset (Sq n)) (a b c d : ℕ) (full : Bool) (sqs : List (ℕ × ℕ)) : List Bool :=
  (wasteLineList n a b c d sqs).flatMap (lineValues D full) ++ sqs.map (sqTrue D a b c d)

/-- **The clauses of `waste`.** -/
theorem waste_sound (a b c d : ℕ) (full : Bool) (hsq : ∀ sq ∈ sqs, sq.1 < n ∧ sq.2 < n) :
    WasteSound D nv (waste n a b c d full sqs nv) (wasteValues D a b c d full sqs) :=
  (wasteLines_sound full (isBoardVar_wasteLineList hsq)).append (wasteSqs_sound a b c d hsq)

/-! ### Lists of squares -/

/-- A square as a pair of naturals `(x, y)`. -/
def sqN (p : Sq n) : ℕ × ℕ := (p.1, p.2)

theorem sqN_injective : Function.Injective (sqN (n := n)) := fun p q h => by
  simp only [sqN, Prod.mk.injEq] at h
  exact Prod.ext (Fin.ext h.1) (Fin.ext h.2)

/-- The list enumerates the squares of `X`, each once. -/
structure Enumerates (sqs : List (ℕ × ℕ)) (X : Finset (Sq n)) : Prop where
  nodup : sqs.Nodup
  lt : ∀ sq ∈ sqs, sq.1 < n ∧ sq.2 < n
  mem : ∀ p, sqN p ∈ sqs ↔ p ∈ X

theorem Enumerates.countP (h : Enumerates sqs X) {P : ℕ × ℕ → Bool} {Q : Sq n → Prop} [DecidablePred Q]
    (hPQ : ∀ p ∈ X, P (sqN p) = true ↔ Q p) : sqs.countP P = (X.filter Q).card := by
  rw [← card_image_of_injective _ sqN_injective]
  refine countP_eq_card h.nodup fun sq => ?_
  rw [mem_image]
  constructor
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨hp, hq⟩ := mem_filter.mp hp
    exact ⟨(h.mem p).mpr hp, (hPQ p hp).mpr hq⟩
  · rintro ⟨hsq, hP⟩
    obtain ⟨p, rfl⟩ : ∃ p : Sq n, sqN p = sq := ⟨(⟨sq.1, (h.lt sq hsq).1⟩, ⟨sq.2, (h.lt sq hsq).2⟩), rfl⟩
    have hp := (h.mem p).mp hsq
    exact ⟨p, mem_filter.mpr ⟨hp, (hPQ p hp).mp hP⟩, rfl⟩

theorem Enumerates.length (h : Enumerates sqs X) : sqs.length = X.card := by
  simpa using h.countP (P := fun _ => true) (Q := fun _ => True) (by simp)

/-- A part of the list: the squares of `X` with the property `Q`. -/
theorem Enumerates.filter (h : Enumerates sqs X) {sqs' : List (ℕ × ℕ)} (hnd : sqs'.Nodup) (hsub : sqs' ⊆ sqs)
    {Q : Sq n → Prop} [DecidablePred Q] (hQ : ∀ p ∈ X, sqN p ∈ sqs' ↔ Q p) : Enumerates sqs' (X.filter Q) where
  nodup := hnd
  lt sq hsq := h.lt sq (hsub hsq)
  mem p := by
    have hsub' (hp : sqN p ∈ sqs') : p ∈ X := (h.mem p).mp (hsub hp)
    rw [mem_filter]
    exact ⟨fun hp => ⟨hsub' hp, (hQ p (hsub' hp)).mp hp⟩, fun hp => (hQ p hp.1).mpr hp.2⟩

theorem nodup_borderSqs (a b c d : ℕ) : (borderSqs a b c d).Nodup := by
  have e : borderSqs a b c d = (List.range' a (b + 1 - a) ×ˢ List.range' c (d + 1 - c)).filter fun sq =>
      decide (sq.1 = a ∨ sq.1 = b ∨ sq.2 = c ∨ sq.2 = d) := by
    simp only [borderSqs, SProd.sprod, List.product, List.filter_flatMap, List.filter_map, Function.comp_def]
  exact e ▸ .filter _ (.product List.nodup_range' List.nodup_range')

theorem nodup_vsideSqs {a b : ℕ} (hab : a ≠ b) (c d : ℕ) : (vsideSqs a b c d).Nodup := by
  have : [a, b].Nodup := by simpa using hab
  exact this.product List.nodup_range'

theorem nodup_hsideSqs {c d : ℕ} (a b : ℕ) (hcd : c ≠ d) : (hsideSqs a b c d).Nodup := by
  have e : hsideSqs a b c d = (vsideSqs c d a b).map Prod.swap := by
    simp only [hsideSqs, vsideSqs, List.map_flatMap, List.map_map]; rfl
  exact e ▸ (nodup_vsideSqs hcd a b).map Prod.swap_injective

theorem enumerates_border (a b c d : Fin n) : Enumerates (borderSqs a b c d) (border a b c d) where
  nodup := nodup_borderSqs a b c d
  lt sq h := by have := mem_borderSqs.mp h; omega
  mem p := by simp only [mem_borderSqs, mem_border, sqN, Fin.val_fin_le, Fin.val_inj]

theorem enumerates_vsides (hab : a ≠ b) (c d : Fin n) : Enumerates (vsideSqs a b c d) (vsides a b c d) where
  nodup := nodup_vsideSqs (Fin.val_ne_of_ne hab) c d
  lt sq h := by have := mem_vsideSqs.mp h; omega
  mem p := by simp only [mem_vsideSqs, mem_vsides, sqN, Fin.val_fin_le, Fin.val_inj]

theorem enumerates_hsides (a b : Fin n) (hcd : c ≠ d) : Enumerates (hsideSqs a b c d) (hsides a b c d) where
  nodup := nodup_hsideSqs a b (Fin.val_ne_of_ne hcd)
  lt sq h := by have := mem_hsideSqs.mp h; omega
  mem p := by simp only [mem_hsideSqs, mem_hsides, sqN, Fin.val_fin_le, Fin.val_inj]

/-- The squares of `X` on one difference diagonal. -/
theorem enumerates_onT (hl : Enumerates sqs X) (hX : X ⊆ border a b c d) (i : ℕ) :
    Enumerates (onT n a b sqs i) (X.filter fun p => Kind.T.key p = i) := by
  have hnd : (onT n a b sqs i).Nodup :=
    (List.Nodup.filter _ List.nodup_range').map fun _ _ h => (Prod.mk.inj h).1
  refine hl.filter hnd (fun sq h => (mem_onT.mp h).2.2.2.2) fun p hp => ?_
  have := (mem_border.mp (hX hp)).1
  rw [mem_onT, hl.mem]
  simp only [hp, and_true, sqN, Kind.T, tIdx]
  omega

/-- The squares of `X` on one sum diagonal. -/
theorem enumerates_onS (hl : Enumerates sqs X) (hX : X ⊆ border a b c d) (s : ℕ) :
    Enumerates (onS a b sqs s) (X.filter fun p => Kind.S.key p = s) := by
  have hnd : (onS a b sqs s).Nodup :=
    (List.Nodup.filter _ List.nodup_range').map fun _ _ h => (Prod.mk.inj h).1
  refine hl.filter hnd (fun sq h => (mem_onS.mp h).2.2.2) fun p hp => ?_
  have := (mem_border.mp (hX hp)).1
  rw [mem_onS, hl.mem]
  simp only [hp, and_true, sqN, Kind.S]
  omega

/-! ### The number of true literals of `waste` -/

section

variable (h : IsFrame D a b c d) (hX : X ⊆ border a b c d)

include h

/-- `nonneedy_lit(sq)` is true iff the square is not needy; the corners are needy. -/
theorem nonneedy_val {p : Sq n} (hp : p ∈ border a b c d) :
    (nonneedy n a b c d (sqN p)).any (boardVal D) = true ↔ ¬ Needy D p := by
  have hx : p.1 = a ∨ p.1 = b → p.1 ∉ occC D := by rintro (e | e) <;> rw [e]; exacts [h.ha, h.hb]
  have hy : p.2 = c ∨ p.2 = d → p.2 ∉ occR D := by rintro (e | e) <;> rw [e]; exacts [h.hc, h.hd]
  have hp := (mem_border.mp hp).2
  simp only [nonneedy, sqN, Fin.val_inj, Needy]
  split_ifs with h1 h2
  · simp [hx h1.1, hy h1.2]
  · simp [hx h2, val_R]
  · simp [hy (by tauto), val_C]

/-- The fresh variable of a square is true iff the square is needy and lies on two occupied diagonals. -/
theorem sqTrue_val {p : Sq n} (hp : p ∈ border a b c d) :
    sqTrue D a b c d (sqN p) = true ↔ Needy D p ∧ dg p ∈ occT D ∧ sm p ∈ occS D := by
  rw [← val_T, ← val_S, ← not_not (a := Needy D p), ← nonneedy_val h hp]
  simp only [sqTrue, sqN, Bool.and_eq_true, Bool.not_eq_true', Bool.not_eq_true]
  tauto

include hX

/-- The true literals of one diagonal: none if it is not occupied; otherwise its copies, and one for every
square of `X` on it that is not needy. -/
theorem count_lineValues (full : Bool) (K : Kind n) {i : ℕ} (hi : i < K.num) {on : List (ℕ × ℕ)}
    (hon : Enumerates on (X.filter fun p => K.key p = i)) :
    (lineValues D full (mkWLine n a b c d (K.var i) on)).count true =
      if i ∈ D.image K.key then lineCopies full (X.filter fun p => K.key p = i).card +
        ((X.filter fun p => ¬ Needy D p).filter fun p => K.key p = i).card else 0 := by
  have hnls : (mkWLine n a b c d (K.var i) on).nls.countP (boardVal D) =
      ((X.filter fun p => ¬ Needy D p).filter fun p => K.key p = i).card := by
    rw [mkWLine, List.countP_filterMap, filter_comm]
    refine hon.countP fun p hp => ?_
    rw [← nonneedy_val h (hX (mem_filter.mp hp).1)]
    cases nonneedy n a b c d (sqN p) <;> rfl
  rw [lineValues, List.count_append, count_map, List.count_replicate, ← hon.length, ← hnls]
  simp only [← K.val hi, mkWLine]
  by_cases ho : boardVal D (K.var i) = true <;> simp [ho]

/-- The true literals of all diagonals of one sort.  `δ p` is the diagonal of the square `p`, and `e i` is the
diagonal with the index `i`. -/
theorem count_lines (full : Bool) (K : Kind n) {on : ℕ → List (ℕ × ℕ)}
    (hon : ∀ i, Enumerates (on i) (X.filter fun p => K.key p = i)) {ι : Type} [DecidableEq ι] {δ : Sq n → ι}
    {e : ℕ → ι} (he : Function.Injective e) (hδ : ∀ p, δ p = e (K.key p)) :
    (((List.range K.num).map fun i => mkWLine n a b c d (K.var i) (on i)).flatMap
      (lineValues D full)).count true =
      ∑ t ∈ D.image δ, lineCopies full (X.filter fun p => δ p = t).card +
        (X.filter fun p => ¬ Needy D p ∧ δ p ∈ D.image δ).card := by
  obtain rfl : δ = e ∘ K.key := funext hδ
  rw [← image_image, sum_image he.injOn, List.count_flatMap, List.map_map]
  simp only [Function.comp_apply, he.eq_iff, he.mem_finset_image]
  calc ∑ i ∈ range K.num, (lineValues D full (mkWLine n a b c d (K.var i) (on i))).count true
    _ = ∑ i ∈ D.image K.key, (lineCopies full (X.filter fun p => K.key p = i).card +
          ((X.filter fun p => ¬ Needy D p).filter fun p => K.key p = i).card) := by
      rw [sum_congr rfl fun i hi => count_lineValues h hX full K (mem_range.mp hi) (hon i), sum_ite_mem,
        inter_eq_right.mpr (K.image_subset D)]
    _ = _ := by rw [sum_add_distrib, sum_card_fiberwise_eq_card_filter, filter_filter]

/-- **The number of true literals of `waste`**, for a list of the squares of a part `X` of the border: the sum of
the three waste terms of (F) for the border (`full`), of (V) and (H) for the sides. -/
theorem count_wasteValues (hl : Enumerates sqs X) (full : Bool) :
    (wasteValues D a b c d full sqs).count true =
      (if full then wasteF D X else zeros D X) + waste2 D X + needy2 D X := by
  have eT := count_lines h hX full .T (enumerates_onT hl hX) tShift_injective dg_eq
  have eS := count_lines h hX full .S (enumerates_onS hl hX) Function.injective_id fun p => rfl
  have copies : ∑ t ∈ occT D, lineCopies full (betaT X t) + ∑ s ∈ occS D, lineCopies full (betaS X s) =
      if full then wasteF D X else zeros D X := by
    cases full <;> simp [lineCopies, wasteF, zeros]
  have squares : (sqs.map (sqTrue D a b c d)).count true = needy2 D X :=
    count_map.trans (hl.countP fun p hp => sqTrue_val h (hX hp))
  rw [wasteValues, wasteLineList, List.flatMap_append, List.count_append, List.count_append, squares,
    ← copies, waste2, Nat.add_right_cancel_iff, Nat.add_add_add_comm]
  exact congrArg₂ (· + ·) eT eS

end

end QueenDom.Sat
