module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.Data.Sym.Sym2
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Push

@[expose] public section

namespace Erdos617

/-- Ordinary slopes are colors. Totalized field division gives all vertical edges color zero. -/
def slopeColor {F : Type} [Field F] : Sym2 (F × F) → F :=
  Sym2.lift ⟨fun u v => (u.2 - v.2) / (u.1 - v.1), by
    intro u v
    dsimp only
    rw [← neg_sub (v.2) (u.2), ← neg_sub (v.1) (u.1), neg_div_neg_eq]⟩

/-- Among more than |F| points, two lie on a common line of any prescribed finite slope. -/
theorem slopeColor_hits {F : Type} [Field F] [Fintype F]
    (S : Finset (F × F)) (h : Fintype.card F < S.card) (k : F) :
    ∃ u ∈ S, ∃ v ∈ S, u ≠ v ∧ slopeColor s(u, v) = k := by
  classical
  let intercept (u : F × F) := u.2 - k * u.1
  obtain ⟨u, hu, v, hv, huv, hk⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to
      (s := S) (t := Finset.univ) (f := intercept)
      (by simpa using h) (fun _ _ => Finset.mem_univ _)
  change u.2 - k * u.1 = v.2 - k * v.1 at hk
  have hx : u.1 ≠ v.1 := by
    intro hx
    apply huv
    apply Prod.ext hx
    rw [hx] at hk
    exact sub_left_inj.mp hk
  refine ⟨u, hu, v, hv, huv, ?_⟩
  change (u.2 - v.2) / (u.1 - v.1) = k
  apply (div_eq_iff (sub_ne_zero.mpr hx)).mpr
  linear_combination hk

/-- The balanced affine example on p² vertices, for each prime p. -/
theorem balanced_at_prime_square (p : ℕ) (hp : p.Prime) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V), Fintype.card V = p^2 ∧
      ∃ (coloring : Sym2 V → Fin p),
        ∀ (S : Finset V), S.card = p + 1 →
          ∀ (k : Fin p), ∃ u ∈ S, ∃ v ∈ S, u ≠ v ∧ coloring s(u, v) = k := by
  let : Fact p.Prime := ⟨hp⟩
  refine ⟨ZMod p × ZMod p, inferInstance, inferInstance, by simp [pow_two], ?_⟩
  refine ⟨fun e => (ZMod.finEquiv p).symm (slopeColor e), ?_⟩
  intro S hS k
  obtain ⟨u, hu, v, hv, huv, hk⟩ :=
    slopeColor_hits S (by simp [hS]) (ZMod.finEquiv p k)
  exact ⟨u, hu, v, hv, huv, by simp [hk]⟩

/-- Sharpness variant from the formal-conjectures statement of Erdős problem 617. -/
theorem erdos_617.variants.r2 :
    {r : ℕ | ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V), Fintype.card V = r^2 ∧
      ∃ (coloring : Sym2 V → Fin r),
        ∀ (S : Finset V), S.card = r + 1 →
          ∀ (k : Fin r), ∃ u ∈ S, ∃ v ∈ S, u ≠ v ∧ coloring s(u, v) = k}.Infinite :=
  Nat.infinite_setOfPred_prime.mono fun p hp => balanced_at_prime_square p hp

private theorem missing_of_transversal
    {V : Type*} [DecidableEq V] {r : ℕ} (coloring : Sym2 V → Fin r)
    (x : V) (k : Fin r) (line : {v : V // v ≠ x} → Fin r)
    (hline : ∀ u v, u ≠ v → coloring s(u.val, v.val) = k → line u = line v)
    (hrep : ∀ a, ∃ v, line v = a ∧ coloring s(x, v.val) ≠ k) :
    ∃ S : Finset V, S.card = r + 1 ∧
      ∀ u ∈ S, ∀ v ∈ S, u ≠ v → coloring s(u, v) ≠ k := by
  classical
  choose rep hindex hspoke using hrep
  let f (a : Fin r) : V := (rep a).val
  have hinj : Function.Injective f := by
    intro a b hab
    exact (hindex a).symm.trans ((congrArg line (Subtype.ext hab)).trans (hindex b))
  let T := Finset.univ.image f
  have hx : x ∉ T := by
    intro hx
    obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hx
    exact (rep a).property ha
  refine ⟨insert x T, ?_, ?_⟩
  · rw [Finset.card_insert_of_notMem hx, Finset.card_image_of_injective _ hinj]
    simp
  · intro u hu v hv huv
    rcases Finset.mem_insert.mp hu with rfl | hu <;>
      rcases Finset.mem_insert.mp hv with rfl | hv
    · exact (huv rfl).elim
    · obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hv
      exact hspoke b
    · obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hu
      rw [Sym2.eq_swap]
      exact hspoke a
    · obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hv
      intro he
      have h := hline (rep a) (rep b) (fun h => huv (congrArg Subtype.val h)) he
      rw [hindex, hindex] at h
      exact huv (congrArg f h)

/-- If, off a vertex `x`, two colors occur only within the blocks of two
partitions into `r` classes, and every block of one partition meets every
block of the other, adjoining `x` forces an `(r+1)`-set missing a color.
In particular, two pure directions of an affine-plane coloring suffice. -/
theorem missing_of_transverse_partitions
    {V : Type*} [DecidableEq V] {r : ℕ} (coloring : Sym2 V → Fin r)
    (x : V) (i j : Fin r) (hij : i ≠ j)
    (row col : {v : V // v ≠ x} → Fin r)
    (hrow : ∀ u v, u ≠ v → coloring s(u.val, v.val) = i → row u = row v)
    (hcol : ∀ u v, u ≠ v → coloring s(u.val, v.val) = j → col u = col v)
    (hmeet : ∀ a b, ∃ v, row v = a ∧ col v = b) :
    ∃ (S : Finset V) (k : Fin r), S.card = r + 1 ∧
      ∀ u ∈ S, ∀ v ∈ S, u ≠ v → coloring s(u, v) ≠ k := by
  classical
  by_cases h : ∀ a, ∃ v, row v = a ∧ coloring s(x, v.val) ≠ i
  · obtain ⟨S, hS⟩ := missing_of_transversal coloring x i row hrow h
    exact ⟨S, i, hS⟩
  · push Not at h
    obtain ⟨a, h⟩ := h
    have hrep : ∀ b, ∃ v, col v = b ∧ coloring s(x, v.val) ≠ j := by
      intro b
      obtain ⟨v, hv, hv'⟩ := hmeet a b
      exact ⟨v, hv', fun he => hij ((h v hv).symm.trans he)⟩
    obtain ⟨S, hS⟩ := missing_of_transversal coloring x j col hcol hrep
    exact ⟨S, j, hS⟩

/-- An edge of nonzero slope k has equal k-intercepts at its two endpoints. -/
private theorem intercept_eq_of_slopeColor {F : Type} [Field F] {k : F} (hk : k ≠ 0)
    {u v : F × F} (h : slopeColor s(u,v) = k) :
    u.2 - k * u.1 = v.2 - k * v.1 := by
  change (u.2 - v.2) / (u.1 - v.1) = k at h
  by_cases hx : u.1 = v.1
  · simp [hx] at h
    exact (hk h.symm).elim
  · have hd := (div_eq_iff (sub_ne_zero.mpr hx)).mp h
    linear_combination hd

/-- Lines of distinct finite slopes meet for every pair of intercepts. -/
private theorem intercepts_intersect {F : Type} [Field F] {k l : F}
    (hkl : k ≠ l) (a b : F) :
    ∃ u : F × F, u.2 - k * u.1 = a ∧ u.2 - l * u.1 = b := by
  let x := (b - a) / (k - l)
  have hx : x * (k - l) = b - a := div_mul_cancel₀ _ (sub_ne_zero.mpr hkl)
  refine ⟨(x, a + k * x), ?_, ?_⟩
  · simp
  · dsimp only
    linear_combination hx

/-- More than two field elements give two distinct nonzero slopes. -/
private theorem exists_two_nonzero_slopes {F : Type} [Field F] [Fintype F]
    (hF : 3 ≤ Fintype.card F) : ∃ k l : F, k ≠ 0 ∧ l ≠ 0 ∧ k ≠ l := by
  classical
  have hcard : ({0, 1} : Finset F).card < (Finset.univ : Finset F).card := by
    simpa [zero_ne_one] using (show 2 < Fintype.card F from hF)
  obtain ⟨l, _, hl⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hl
  exact ⟨1, l, one_ne_zero, hl.1, Ne.symm hl.2⟩

/-- Adjoining a vertex to the affine slope coloring, with arbitrary colors on the
new edges, always produces a missing color when the field has at least three elements.
Here `coords` identifies the old vertices with the affine plane, and `colors`
identifies the field elements with the color labels. -/
theorem missing_of_affine_extension {F V : Type} [Field F] [Fintype F] [DecidableEq V]
    {r : ℕ} (hr : 3 ≤ r) (colors : F ≃ Fin r) (coloring : Sym2 V → Fin r)
    (x : V) (coords : {v : V // v ≠ x} ≃ F × F)
    (hgrid : ∀ u v, u ≠ v →
      coloring s(u.val, v.val) = colors (slopeColor s(coords u, coords v))) :
    ∃ (S : Finset V) (k : Fin r), S.card = r + 1 ∧
      ∀ u ∈ S, ∀ v ∈ S, u ≠ v → coloring s(u, v) ≠ k := by
  have hcard : Fintype.card F = r := by simpa using Fintype.card_congr colors
  obtain ⟨k, l, hk, hl, hkl⟩ := exists_two_nonzero_slopes (F := F) (hcard ▸ hr)
  let line (m : F) (u : {v : V // v ≠ x}) := colors ((coords u).2 - m * (coords u).1)
  have hline (m : F) (hm : m ≠ 0) (u v : {v : V // v ≠ x}) (huv : u ≠ v)
      (h : coloring s(u.val, v.val) = colors m) : line m u = line m v := by
    rw [hgrid u v huv] at h
    exact congrArg colors (intercept_eq_of_slopeColor hm (colors.injective h))
  refine missing_of_transverse_partitions coloring x (colors k) (colors l)
    (fun h => hkl (colors.injective h)) (line k) (line l) (hline k hk) (hline l hl) ?_
  intro a b
  obtain ⟨u, hu, hv⟩ := intercepts_intersect hkl (colors.symm a) (colors.symm b)
  exact ⟨coords.symm u, by simp [line, hu], by simp [line, hv]⟩

end Erdos617
