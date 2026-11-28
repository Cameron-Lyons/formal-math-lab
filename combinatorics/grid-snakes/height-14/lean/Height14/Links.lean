import Height14.Cut

namespace Height14.Ranked
open Interval
variable {w l : Nat} (P : Ranked w l)

/-- Rows connected to an old neighbor of the square being inserted. -/
theorem touches_iff {t} {p : Fin l} (hp : P.pos p=t) (s : Row) :
    (P.profile t).touches (row t) s = true ↔
    ∃ i, P.At t s i ∧ Interval.touches P.pos t p i := by
  simp only [Profile.touches, Profile.above, profile, Bool.or_eq_true, Bool.and_eq_true,
    bne_iff_ne, row, bit_true]
  change P.Link t s (row t) ∨ (t%14 ≠ 0 ∧ P.Link t s (upRow t)) ↔ _
  constructor
  · rintro (⟨i,k,hi,hk,hik⟩ | ⟨hr,i,k,hi,hk,hik⟩)
    · exact ⟨i,hi,k,((P.older_neighbor hp).mpr (Or.inl hk)).1,hik⟩
    · exact ⟨i,hi,k,((P.older_neighbor hp).mpr (Or.inr ⟨hr,hk⟩)).1,hik⟩
  · rintro ⟨i,hi,k,adj,hik⟩
    rcases (P.older_neighbor hp).mp ⟨adj,joined_right hik⟩ with h | ⟨hr,h⟩
    · exact Or.inl ⟨i,k,hi,h,hik⟩
    · exact Or.inr ⟨hr,i,k,hi,h,hik⟩

theorem neighbors_unlinked {t} {p : Fin l} (hp : P.pos p=t) :
    Profile.above ((P.profile t).linked (row t)) (row t) = false := by
  apply Bool.eq_false_iff.mpr
  simp only [ne_eq,Profile.above, profile, row, Bool.and_eq_true, bne_iff_ne, bit_true]
  change ¬ (t%14 ≠ 0 ∧ P.Link t (row t) (upRow t))
  rintro ⟨hr,i,j,hi,hj,hij⟩
  have ai := ((P.older_neighbor hp).mpr (Or.inl hi)).1
  have aj := ((P.older_neighbor hp).mpr (Or.inr ⟨hr,hj⟩)).1
  have li := P.at_same.mp hi
  have lj := (P.at_above hr).mp hj
  have ne : i.val ≠ j.val := by intro he; have := Fin.ext he; subst j; omega
  have hmid : between i p j := by unfold nextTo between at *; omega
  have := hij p hmid
  omega

theorem link_insert {t} {p : Fin l} (hp : P.pos p=t) (r s : Row) :
    bit (P.Link (t+1) r s) = ((P.profile t).insert (row t)).linked r s := by
  apply Bool.eq_iff_iff.mpr
  rw [bit_true]
  have pivot := P.at_new.mpr hp
  have head (s : Row) (hs : s ≠ row t) :
      P.Link (t+1) (row t) s ↔ (P.profile t).touches (row t) s = true := by
    rw [P.touches_iff hp]
    constructor
    · rintro ⟨i,j,hi,hj,h⟩
      have e : i=p := P.at_unique hi pivot
      subst i
      have old := (P.at_other hs).mp hj
      have hjp : j ≠ p := by rintro rfl; have := old.2.1; omega
      rcases (joined_fill P.injective hp).mp h with h | ⟨_,h | h⟩
      · have := joined_left h; omega
      · exact False.elim (hjp h)
      · exact ⟨j,old,h⟩
    · rintro ⟨i,hi,hit⟩
      exact ⟨p,i,pivot,(P.at_other hs).mpr hi,
        (joined_fill P.injective hp).mpr (Or.inr ⟨Or.inl rfl,Or.inr hit⟩)⟩
  by_cases hr : r=row t
  · subst r; by_cases hs : s=row t
    · subst s; simp only [Profile.insert, beq_self_eq_true, ite_true, Bool.true_or, iff_true]
      exact ⟨p,p,pivot,pivot,joined_refl.mpr (by omega)⟩
    · simpa [Profile.insert, hs] using head s hs
  · by_cases hs : s=row t
    · subst s; rw [P.link_comm]; simpa [Profile.insert,hr] using head r hr
    · simp only [Profile.insert, beq_iff_eq, hr, hs, ite_false, profile, Bool.or_eq_true,
          Bool.and_eq_true, bit_true]
      change P.Link (t+1) r s ↔ P.Link t r s ∨
        ((P.profile t).touches (row t) r = true ∧ (P.profile t).touches (row t) s = true)
      rw [P.touches_iff hp,P.touches_iff hp]
      constructor
      · rintro ⟨i,j,hi,hj,h⟩
        have hi' := (P.at_other hr).mp hi
        have hj' := (P.at_other hs).mp hj
        rcases (joined_fill P.injective hp).mp h with h | ⟨h₁,h₂⟩
        · exact Or.inl ⟨i,j,hi',hj',h⟩
        · have ne {a : Fin l} (h : P.pos a < t) : a ≠ p := by rintro rfl; omega
          exact Or.inr ⟨⟨i,hi',h₁.resolve_left (ne hi'.2.1)⟩,
            ⟨j,hj',h₂.resolve_left (ne hj'.2.1)⟩⟩
      · rintro (⟨i,j,hi,hj,h⟩ | ⟨⟨i,hi,hit⟩,⟨j,hj,hjt⟩⟩)
        · exact ⟨i,j,(P.at_other hr).mpr hi,(P.at_other hs).mpr hj,joined_mono h⟩
        · exact ⟨i,j,(P.at_other hr).mpr hi,(P.at_other hs).mpr hj,
            (joined_fill P.injective hp).mpr (Or.inr ⟨Or.inr hit,Or.inr hjt⟩)⟩

theorem at_skip {t} (empty : ∀ i, P.pos i ≠ t) {r i} :
    P.At (t+1) r i ↔ r ≠ row t ∧ P.At t r i := by
  by_cases h : r=row t
  · subst r; simp [P.at_new,empty]
  · simp [h,P.at_other h]

theorem link_skip {t} (empty : ∀ i, P.pos i ≠ t) (r s : Row) :
    bit (P.Link (t+1) r s) = ((P.profile t).keep (row t)).linked r s := by
  apply Bool.eq_iff_iff.mpr
  simp only [bit_true, Profile.keep, profile, Bool.and_eq_true, bne_iff_ne]
  constructor
  · rintro ⟨i,j,hi,hj,h⟩
    obtain ⟨hr,hi'⟩ := (P.at_skip empty).mp hi
    obtain ⟨hs,hj'⟩ := (P.at_skip empty).mp hj
    exact ⟨⟨hr,hs⟩,i,j,hi',hj',(joined_skip empty).mp h⟩
  · rintro ⟨⟨hr,hs⟩,i,j,hi,hj,h⟩
    exact ⟨i,j,(P.at_skip empty).mpr ⟨hr,hi⟩,(P.at_skip empty).mpr ⟨hs,hj⟩,joined_mono h⟩

end Height14.Ranked
