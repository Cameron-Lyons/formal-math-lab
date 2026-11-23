import Coloring
import Cycles

namespace Erdos835

open Equiv.Perm

private theorem sign_of_free_involution {V : Type*} [Fintype V] [DecidableEq V]
    (nV : Fintype.card V = 18) {s : Equiv.Perm V} (hs : s ^ 2 = 1)
    (hf : ∀ x, s x ≠ x) : sign s = -1 := by
  have : IsEmpty (Function.fixedPoints s) := ⟨fun x => hf x.val x.property⟩
  rw [sign_of_pow_two_eq_one hs, nV, Fintype.card_eq_zero]
  decide

/-- A fixed-point-free involution on 18 vertices must fix an edge of each invariant
perfect matching. The sign argument pairs off the edges exchanged by the involution. -/
private theorem invariant_matching_uses_pair {V : Type*} [Fintype V] [DecidableEq V]
    (nV : Fintype.card V = 18) (s : Equiv.Perm V) (ss : ∀ x, s (s x) = x)
    (sf : ∀ x, s x ≠ x) (r : V → V → Prop)
    (sym : ∀ {x y}, r x y → r y x) (irr : ∀ x, ¬ r x x)
    (unique : ∀ x, ∃! y, r x y) (inv : ∀ {x y}, r x y → r (s x) (s y)) :
    ∃ x, r x (s x) := by
  classical
  let f (x : V) := Classical.choose (unique x)
  have hf (x) : r x (f x) := (Classical.choose_spec (unique x)).1
  have hu {x y} (h : r x y) : y = f x := (Classical.choose_spec (unique x)).2 y h
  have ff (x) : f (f x) = x := (hu (sym (hf x))).symm
  have fs (x) : f (s x) = s (f x) := (hu (inv (hf x))).symm
  let m : Equiv.Perm V := ⟨f, f, ff, ff⟩
  have hs : s ^ 2 = 1 := Equiv.ext (fun x => by simpa [pow_two] using ss x)
  have hm : m ^ 2 = 1 := Equiv.ext (fun x => by simpa [pow_two, m] using ff x)
  have hp : (s * m) ^ 2 = 1 := by
    apply Equiv.ext
    intro x
    change s (f (s (f x))) = x
    rw [fs, ff, ss]
  have sm := sign_of_free_involution nV hs sf
  have mm := sign_of_free_involution nV hm (by
    intro x hx
    change f x = x at hx
    exact irr x (by simpa only [hx] using hf x))
  by_contra! none
  have pp := sign_of_free_involution nV hp (by
    intro x hx
    change s (f x) = x at hx
    have : f x = s x := (ss (f x)).symm.trans (congrArg s hx)
    exact none x (by simpa only [this] using hf x))
  rw [map_mul, sm, mm] at pp
  norm_num at pp

/-- Each invariant color matching uses a pair of the point involution. -/
theorem fixedColor_uses_pair {c g τ W i} (hc : Rainbow c) (he : Equivariant c g τ)
    (hW : W.card = 18) (stable : W.map g.toEmbedding = W)
    (hinv : ∀ x, g (g x) = x) (hfree : ∀ x, g x ≠ x) (hi : τ i = i) :
    ∃ x ∈ W, EdgeHasColor c W i x (g x) := by
  classical
  have closed {x : Point} (hx : x ∈ W) : g x ∈ W :=
    stable ▸ Finset.mem_map_of_mem g.toEmbedding hx
  let f (x : W) : W := ⟨g x, closed x.property⟩
  have ff (x) : f (f x) = x := Subtype.ext (hinv x.val)
  let s : Equiv.Perm W := ⟨f, f, ff, ff⟩
  obtain ⟨x, hx⟩ := invariant_matching_uses_pair (by simpa using hW) s ff
    (fun x e => hfree x.val (congrArg Subtype.val e))
    (fun x y : W => EdgeHasColor c W i x.val y.val)
    (fun h => edge_symm h) (fun x => edge_irrefl x.val)
    (fun x => edge_unique hc hW i x.val x.property)
    (fun {x y} h => by
      change EdgeHasColor c W i (g x.val) (g y.val)
      simpa only [hi] using edge_map he stable h)
  exact ⟨x.val, x.property, hx⟩

/-- An edge exchanged end-for-end by a symmetry has fixed color. -/
theorem pair_color_fixed {c g τ W i x} (he : Equivariant c g τ)
    (stable : W.map g.toEmbedding = W) (hinv : ∀ x, g (g x) = x)
    (h : EdgeHasColor c W i x (g x)) : τ i = i := by
  apply edge_color_unique _ h
  simpa only [hinv] using edge_symm (edge_map he stable h)

/-- A fixed-point-free involution can fix at most nine palette colors. -/
theorem fixedFree_palette_bound {c g τ} (hc : Rainbow c) (he : Equivariant c g τ)
    (hinv : ∀ x, g (g x) = x) (hfree : ∀ x, g x ≠ x) :
    Fintype.card (Function.fixedPoints τ) ≤ 9 := by
  classical
  obtain ⟨W, hW, stable⟩ := involution_witness18 g hinv hfree
  let I := Function.fixedPoints τ
  choose x xW hx using fun i : I => fixedColor_uses_pair hc he hW stable hinv hfree i.property
  let endpoints (p : I × Bool) : Point := if p.2 then g (x p.1) else x p.1
  have h (p : I × Bool) : EdgeHasColor c W p.1.val (endpoints p) (g (endpoints p)) := by
    rcases p with ⟨i,b⟩
    cases b
    · exact hx _
    · simpa [endpoints, hinv] using edge_symm (hx i)
  have closed {z : Point} (hz : z ∈ W) : g z ∈ W :=
    stable ▸ Finset.mem_map_of_mem g.toEmbedding hz
  let toW (p : I × Bool) : W := ⟨endpoints p, by
    rcases p with ⟨i, b⟩
    cases b
    · exact xW _
    · exact closed (xW _)⟩
  have inj : Function.Injective toW := by
    rintro ⟨i,a⟩ ⟨j,b⟩ e
    have hab : endpoints (i,a) = endpoints (j,b) := congrArg Subtype.val e
    obtain rfl : i = j := Subtype.ext (edge_color_unique (hab ▸ h (i,a)) (h (j,b)))
    cases a <;> cases b
    · rfl
    · exact (hfree _ hab.symm).elim
    · exact (hfree _ hab).elim
    · rfl
  have := Fintype.card_le_of_injective toW inj
  simp only [Fintype.card_prod, Fintype.card_bool, Fintype.card_coe, hW] at this
  change Fintype.card I ≤ 9
  omega

private theorem block_map_one (B : Block) :
    (⟨B.val.map (1 : Equiv.Perm Point).toEmbedding, by simp [B.property]⟩ : Block) = B := by
  apply Subtype.ext
  exact Finset.map_refl

theorem equivariant_one (c : Block → Fin 17) : Equivariant c 1 1 := by
  intro B
  simp only [one_apply, block_map_one]

theorem equivariant_mul {c g h τ υ} (eg : Equivariant c g τ) (eh : Equivariant c h υ) :
    Equivariant c (g * h) (τ * υ) := by
  intro B
  let A : Block := ⟨B.val.map h.toEmbedding, by simp [B.property]⟩
  have hm : B.val.map (g * h).toEmbedding = A.val.map g.toEmbedding := by
    simp only [A, Finset.map_map]
    congr 1
  calc
    c _ = c ⟨A.val.map g.toEmbedding, by simp [A.property]⟩ := congrArg c (Subtype.ext hm)
    _ = τ (c A) := eg A
    _ = (τ * υ) (c B) := congrArg τ (eh B)

theorem equivariant_pow {c g τ} (he : Equivariant c g τ) (n : ℕ) :
    Equivariant c (g ^ n) (τ ^ n) := by
  induction n with
  | zero => simpa only [pow_zero] using equivariant_one c
  | succ n ih => simpa only [pow_succ] using equivariant_mul ih he

/-- A point permutation determines its palette action because every color occurs. -/
theorem equivariant_palette_unique {c g τ υ} (hc : Rainbow c)
    (hτ : Equivariant c g τ) (hυ : Equivariant c g υ) : τ = υ := by
  apply Equiv.ext
  intro i
  obtain ⟨A, _, hA⟩ := Finset.exists_subset_card_eq
    (show 17 ≤ (Finset.univ : Finset Point).card by simp)
  obtain ⟨x, hx⟩ := (face_bijective hc A hA).2 i
  simpa only [hx] using (hτ (face A hA x)).symm.trans (hυ (face A hA x))

/-- The order of the induced permutation of the colors divides the point order. -/
theorem palette_pow_eq_one {c g τ} (hc : Rainbow c) (he : Equivariant c g τ)
    {n : ℕ} (hg : g ^ n = 1) : τ ^ n = 1 :=
  equivariant_palette_unique hc (hg ▸ equivariant_pow he n) (equivariant_one c)

/-- A 32-cycle cannot be a symmetry, even when it can permute the colors. -/
theorem no_order32_symmetry {c g τ} (hc : Rainbow c) (hg : orderOf g = 32) :
    ¬ Equivariant c g τ := by
  intro he
  have pow32 : g ^ 32 = 1 := hg ▸ pow_orderOf_eq_one g
  have ht := palette_pow_eq_one hc he pow32
  have he16 := equivariant_pow he 16
  rw [palette_pow16 _ ht] at he16
  obtain ⟨_, _, _, hfree⟩ := order32_witness18 _ hg
  have hinv (x : Point) : (g ^ 16) ((g ^ 16) x) = x := by
    rw [← Equiv.Perm.mul_apply, ← pow_add]
    exact congrArg (fun v : Equiv.Perm Point => v x) pow32
  have bound := fixedFree_palette_bound hc he16 hinv hfree
  let includeColor (i : Fin 17) : Function.fixedPoints (1 : Equiv.Perm (Fin 17)) := ⟨i, rfl⟩
  have all := Fintype.card_le_of_injective includeColor
    (fun _ _ h => congrArg Subtype.val h)
  rw [Fintype.card_fin] at all
  omega

end Erdos835
