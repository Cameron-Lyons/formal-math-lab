/-
Soundness of the CNF encoding (Layer 2): the frame-dependent clauses (`QueenDomSat.extraGroup`): FRAME and the
bounds (F), (V), (H).  `CaseSat` gives the identities (F), (V), (H); the sums of their waste terms are the
numbers of true waste literals (`Waste.lean`), so the bounds hold.  For a square box, (V) and (H) have the extra
term `sqTerm`; the encoder adds the two literals `-u0`, `-v0`, and `2` to the bound (`sqExtra_sound`).
-/
module

public import Queens48.Waste

@[expose] public section

namespace QueenDom.Sat

open QueenDomSat Finset

variable {n : ℕ} {D X : Finset (Sq n)} {a b c d : Fin n} {nv : ℕ}

/-- FRAME: the columns outside `[a, b]` and the rows outside `[c, d]` are occupied, the columns `a`, `b` and
the rows `c`, `d` are empty. -/
theorem holds_frameCls (h : IsFrame D a b c d) {τ : ℕ → Bool} (hτ : Encodes D τ) :
    Holds τ (frameCls n a b c d) := by
  have neg_C (x : Fin n) : Lit τ (-oCv n x) ↔ x ∉ occC D :=
    (lit_neg (var_ne_zero (Nat.succ_pos _))).trans (lit_C hτ x).not
  have neg_R (y : Fin n) : Lit τ (-oRv n y) ↔ y ∉ occR D :=
    (lit_neg (var_ne_zero (Nat.succ_pos _))).trans (lit_R hτ y).not
  simp only [frameCls, holds_append, holds_cons, holds_nil, holds_map, List.mem_filter, List.mem_range,
    decide_eq_true_eq, exists_lit_cons, exists_lit_nil, or_false, and_true, neg_C, neg_R]
  refine ⟨fun x hx => ?_, fun y hy => ?_, h.ha, h.hb, h.hc, h.hd⟩
  · refine (lit_C hτ ⟨x, hx.1⟩).mpr (by_contra fun hne => ?_)
    have := h.hcol _ hne
    simp only [Fin.le_def] at this; omega
  · refine (lit_R hτ ⟨y, hy.1⟩).mpr (by_contra fun hne => ?_)
    have := h.hrow _ hne
    simp only [Fin.le_def] at this; omega

/-- `atmost(waste(X) + extra, bound)`. -/
theorem wasteAtmost_sound (h : IsFrame D a b c d) (full : Bool) {sqs : List (ℕ × ℕ)} (hl : Enumerates sqs X)
    (hX : X ⊆ border a b c d) {extra : List ℤ} {bs : List Bool} (hextra : ∀ τ, Encodes D τ → Values τ extra bs)
    {bound : ℤ}
    (hc : ((if full then wasteF D X else zeros D X) + waste2 D X + needy2 D X + bs.count true : ℕ) ≤ bound) :
    Sound (Encodes D) nv (wasteAtmost (waste n a b c d full sqs nv) extra bound nv).new
      (Holds · (wasteAtmost (waste n a b c d full sqs nv) extra bound nv).cls) := by
  refine ((waste_sound a b c d full hl.lt).bind (atmost_sound (fun τ h => h.2.2.append (hextra τ h.1)) ?_)).imp
    fun τ _ h => holds_append.mpr ⟨h.1.1, h.2⟩
  rwa [List.count_append, count_wasteValues h hX hl]

/-- For a square box, `2 - sqTerm` of the two literals `-u0`, `-v0` are true. -/
theorem sqExtra_sound (hbox : (b : ℕ) - a = (d : ℕ) - c) : ∃ bs,
    (∀ τ, Encodes D τ → Values τ (sqExtra n a c d) bs) ∧ bs.count true + sqTerm D a b c d = 2 := by
  have bT : IsBoardVar n (oTv n (tIdx n a c)) := Kind.T.isBoardVar _ (Kind.T.key_lt (a, c))
  have bS : IsBoardVar n (oSv n (a + d)) := Kind.S.isBoardVar _ (Kind.S.key_lt (a, d))
  refine ⟨_, fun τ hτ => .cons (hτ.value bT).neg (.cons (hτ.value bS).neg .nil), ?_⟩
  have hT : _ ↔ (c : ℤ) - a ∈ occT D := val_T (a, c)
  have hS : _ ↔ (a : ℕ) + d ∈ occS D := val_S (a, d)
  rw [sqTerm, ite_eq_left hbox]
  simp only [← hT, ← hS]
  cases boardVal D (oTv n (tIdx n a c)) <;> cases boardVal D (oSv n (a + d)) <;> rfl

/-- The common form of (V) and (H), with the condition `w` and the bound `g`. -/
theorem side_sound (h : IsFrame D a b c d) {sqs : List (ℕ × ℕ)} (hl : Enumerates sqs X) (hX : X ⊆ border a b c d)
    {w : Prop} [Decidable w] {g : ℤ}
    (hg : w → (zeros D X + waste2 D X + needy2 D X : ℤ) = g + sqTerm D a b c d) {G : Group}
    (hG : G = if w then
        if (b : ℕ) - a = (d : ℕ) - c
        then wasteAtmost (waste n a b c d false sqs nv) (sqExtra n a c d) (g + 2) nv
        else wasteAtmost (waste n a b c d false sqs nv) [] g nv
      else ⟨[], 0⟩) :
    Sound (Encodes D) nv G.new (Holds · G.cls) := by
  split_ifs at hG with hw hbox <;> subst hG
  · obtain ⟨bs, hx, e⟩ := sqExtra_sound (D := D) hbox
    exact wasteAtmost_sound h false hl hX hx (by have := hg hw; simp only [Bool.false_eq_true, ite_false]; omega)
  · refine wasteAtmost_sound h false hl hX (fun _ _ => .nil) ?_
    have := hg hw
    rw [sqTerm, ite_eq_right hbox] at this
    simp only [Bool.false_eq_true, ite_false, List.count_nil]; omega
  · exact .of_forall fun _ _ => holds_nil

section

variable {k dR dC dT dS : ℕ} (h : IsFrame D a b c d)

include h

theorem groupF_sound (hF : wasteF D (border a b c d) + waste2 D (border a b c d) + needy2 D (border a b c d)
      + 4 * n + 2 * (dR + dC + dT + dS) = 8 * k + 4) :
    Sound (Encodes D) nv (groupF n k dR dC dT dS a b c d nv).new
      (Holds · (groupF n k dR dC dT dS a b c d nv).cls) := by
  refine wasteAtmost_sound h true (enumerates_border a b c d) Subset.rfl (fun _ _ => .nil) ?_
  simp only [ite_true, boundF, List.count_nil]; omega

theorem groupV_sound (hV : (d : ℕ) - c ≤ (b : ℕ) - a →
      zeros D (vsides a b c d) + waste2 D (vsides a b c d) + needy2 D (vsides a b c d) + 2 * n
        + dT + dS + 2 * dR = 4 * k + sqTerm D a b c d) :
    Sound (Encodes D) nv (groupV n k dR dT dS a b c d nv).new
      (Holds · (groupV n k dR dT dS a b c d nv).cls) :=
  side_sound h (enumerates_vsides h.hab.ne c d) (border_eq_union h.hab.le h.hcd.le ▸ subset_union_left)
    (g := boundV n k dR dT dS) (fun hwh => by have := hV hwh; unfold boundV; omega) rfl

theorem groupH_sound (hH : (b : ℕ) - a ≤ (d : ℕ) - c →
      zeros D (hsides a b c d) + waste2 D (hsides a b c d) + needy2 D (hsides a b c d) + 2 * n
        + dT + dS + 2 * dC = 4 * k + sqTerm D a b c d) :
    Sound (Encodes D) nv (groupH n k dC dT dS a b c d nv).new
      (Holds · (groupH n k dC dT dS a b c d nv).cls) :=
  side_sound h (enumerates_hsides a b h.hcd.ne) (border_eq_union h.hab.le h.hcd.le ▸ subset_union_right)
    (g := boundH n k dC dT dS) (fun hhw => by have := hH hhw; unfold boundH; omega) rfl

end

/-- **The clauses of `extraGroup`.** -/
theorem extra_sound {k : ℕ} {cs : Case} (h : CaseSat n k cs D) (nv : ℕ) :
    ∃ m, Sound (Encodes D) nv m (Holds · (extraGroup n k cs.dR cs.dC cs.dT cs.dS cs.ml (n - 1 - cs.mr) cs.mb
      (n - 1 - cs.mt) nv).cls) := by
  obtain ⟨a, b, c, d, hfr, ha, hb, hc, hd, hF, hV, hH⟩ := h.frame
  rw [← ha, ← hc, show n - 1 - cs.mr = b by omega, show n - 1 - cs.mt = d by omega]
  exact ⟨_, ((groupF_sound hfr hF).append ((groupV_sound hfr hV).append (groupH_sound hfr hH))).imp
    fun τ hτ h => holds_append.mpr ⟨holds_frameCls hfr hτ, h⟩⟩

end QueenDom.Sat
