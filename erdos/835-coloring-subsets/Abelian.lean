module

public import PaletteBound
public import TranslationGroup

@[expose] public section

namespace Erdos835

/-- The points fixed by a group element are also fixed by its powers, so one may
take an involution for the eight-color lower bound. -/
theorem many_fixed_colors_involution {G : Type*} [CommGroup G] [Fintype G]
    (hG : Fintype.card G = 32) (ρ : G →* Equiv.Perm (Fin 17)) :
    ∃ u : G, u ≠ 1 ∧ u ^ 2 = 1 ∧ 8 ≤ Fintype.card (Function.fixedPoints (ρ u)) := by
  classical
  obtain ⟨g, hg, hc⟩ := many_fixed_colors hG ρ
  have hd : orderOf g ∣ 32 := hG ▸ orderOf_dvd_card
  obtain ⟨e, _, he⟩ := (Nat.dvd_prime_pow Nat.prime_two (m := 5)).mp hd
  cases e with
  | zero =>
    exact (hg (orderOf_eq_one_iff.mp (by simpa using he))).elim
  | succ e =>
    have ho : orderOf g = 2 ^ e * 2 := he.trans (pow_succ _ _)
    have pos : 0 < 2 ^ e := by positivity
    have hne : g ^ (2 ^ e) ≠ 1 := by
      intro h
      have := Nat.le_of_dvd pos (orderOf_dvd_of_pow_eq_one h)
      omega
    refine ⟨g ^ (2 ^ e), hne, by rw [← pow_mul, ← ho, pow_orderOf_eq_one], ?_⟩
    rw [map_pow, Fintype.card_subtype]
    apply hc.trans (Finset.card_le_card ?_)
    intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Function.IsFixedPt.perm_pow
      (Finset.mem_filter.mp hx).2 _⟩

/-- No abelian group of order 32 acting freely on the ground set can preserve
the coloring, even when each group element may individually relabel all colors. -/
theorem no_regular_abelian_symmetry {G : Type*} [CommGroup G] [Fintype G]
    (hG : Fintype.card G = 32) (points : G →* Equiv.Perm Point)
    (free : ∀ u : G, u ≠ 1 → ∀ x, points u x ≠ x) {c} (hc : Rainbow c) :
    ¬ ∀ u : G, ∃ τ : Equiv.Perm (Fin 17), Equivariant c (points u) τ := by
  classical
  intro sym
  choose colors equiv using sym
  -- Surjectivity of a rainbow coloring forces the separate relabelings to form an action.
  let ρ : G →* Equiv.Perm (Fin 17) :=
    { toFun := colors
      map_one' := equivariant_palette_unique hc (by simpa using equiv 1) (equivariant_one c)
      map_mul' := fun u v => equivariant_palette_unique hc (equiv (u * v))
        (by simpa only [map_mul] using equivariant_mul (equiv u) (equiv v)) }
  obtain ⟨u, hu, usq, lower⟩ := many_fixed_colors_involution hG ρ
  have ptSq : (points u) ^ 2 = 1 := by rw [← map_pow, usq, map_one]
  have inv (x : Point) : points u (points u x) = x := by
    exact congrArg (fun s : Equiv.Perm Point => s x) ptSq
  have upper : Fintype.card (Function.fixedPoints (ρ u)) ≤ 7 :=
    fixedFree_palette_le_seven hc (equiv u) inv (free u hu)
  omega

end Erdos835
