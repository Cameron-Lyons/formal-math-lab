import Height14.Cut

namespace Height14.Ranked
open Interval
variable {w l : Nat} (P : Ranked w l)

private theorem flip {i j : Fin l} (h : nextTo i j) : nextTo j i :=
  h.symm

private theorem neighbor_ne {i j : Fin l} (h : nextTo i j) : i ≠ j := by
  rintro rfl; unfold nextTo at h; omega

private theorem no_third {p i j k : Fin l} (ha : nextTo p i)
    (hb : nextTo p j) (hc : nextTo p k) (h : i ≠ j) : k = i ∨ k = j := by
  have hne : i.val ≠ j.val := fun e => h (Fin.ext e)
  unfold nextTo at *
  by_cases hki : k.val = i.val
  · exact Or.inl (Fin.ext hki)
  · exact Or.inr (Fin.ext (by omega))

private theorem earlier {t} {p i : Fin l} (hp : P.pos p = t) (h : i ≠ p)
    (h' : P.pos i < t + 1) : P.pos i < t := by
  have : P.pos i ≠ P.pos p := fun e => h (P.injective e)
  omega

private theorem not_sat_neighbor {t} {p i : Fin l} (hp : P.pos p = t)
    (edge : nextTo i p) : ¬ P.Saturated t i := by
  rintro ⟨j,k,ne,hj,hk,jold,kold⟩
  rcases no_third hj hk edge ne with h | h <;> subst p <;> omega

theorem fill_unsaturated {t} {p : Fin l} (hp : P.pos p = t) :
    ¬P.Sat t (row t) ∧ (t%14 ≠ 0 → ¬P.Sat t (upRow t)) := by
  constructor
  · rintro ⟨i,hi,hs⟩
    exact P.not_sat_neighbor hp ((P.older_neighbor hp).mpr (.inl hi)).1 hs
  · rintro hr ⟨i,hi,hs⟩
    exact P.not_sat_neighbor hp ((P.older_neighbor hp).mpr (.inr ⟨hr,hi⟩)).1 hs

private theorem bool_eq {a b : Bool} (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b <;> simp_all

private theorem left_up_ne {t i j} (hr : t%14 ≠ 0)
    (hi : P.At t (row t) i) (hj : P.At t (upRow t) j) : i ≠ j := by
  rintro rfl
  have a := (P.at_same).mp hi
  have b := (P.at_above hr).mp hj
  omega

private theorem new_sat {t} {p : Fin l} (hp : P.pos p = t) :
    P.Sat (t+1) (row t) ↔ P.Occ t (row t) ∧ (t%14 ≠ 0 ∧ P.Occ t (upRow t)) := by
  constructor
  · rintro ⟨i,hi,j,k,ne,hj,hk,tj,tk⟩
    have eq := P.injective ((P.at_new.mp hi).trans hp.symm)
    subst i
    have a := (P.older_neighbor hp).mp ⟨flip hj,P.earlier hp (neighbor_ne (flip hj)) tj⟩
    have b := (P.older_neighbor hp).mp ⟨flip hk,P.earlier hp (neighbor_ne (flip hk)) tk⟩
    rcases a with a | ⟨hr,a⟩ <;> rcases b with b | ⟨hr',b⟩
    · exact (ne (P.at_unique a b)).elim
    · exact ⟨⟨j,a⟩,hr',⟨k,b⟩⟩
    · exact ⟨⟨k,b⟩,hr,⟨j,a⟩⟩
    · exact (ne (P.at_unique a b)).elim
  · rintro ⟨⟨j,hj⟩,hr,⟨k,hk⟩⟩
    exact ⟨p,P.at_new.mpr hp,j,k,P.left_up_ne hr hj hk,
      flip ((P.older_neighbor hp).mpr (.inl hj)).1,
      flip ((P.older_neighbor hp).mpr (.inr ⟨hr,hk⟩)).1,
      Nat.lt_succ_of_lt hj.2.1,Nat.lt_succ_of_lt hk.2.1⟩

private theorem same_saturation {t} {p i : Fin l} (hp : P.pos p = t)
    (hn : ¬nextTo i p) : P.Saturated (t+1) i ↔ P.Saturated t i := by
  constructor
  · rintro ⟨j,k,h,a,b,c,d⟩
    exact ⟨j,k,h,a,b,P.earlier hp (fun eq => hn (eq ▸ a)) c,
      P.earlier hp (fun eq => hn (eq ▸ b)) d⟩
  · rintro ⟨j,k,h,a,b,c,d⟩
    exact ⟨j,k,h,a,b,by omega,by omega⟩

private theorem above_sat {t} {p : Fin l} (hp : P.pos p = t) (hr : t%14 ≠ 0) :
    P.Sat (t+1) (upRow t) ↔ P.Occ t (upRow t) ∧ ¬P.Pivot t := by
  have diff : upRow t ≠ row t := by
    intro e; have := congrArg Fin.val e; simp [upRow,row] at this; omega
  constructor
  · rintro ⟨i,a,j,k,ne,hj,hk,tj,tk⟩
    have atOld := (P.at_other diff).mp a
    refine ⟨⟨i,atOld⟩, ?_⟩
    rintro ⟨_,z,hz,iso⟩
    have zi : z = i := P.at_unique ((P.at_above hr).mpr hz) atOld
    subst z
    by_cases jp : j = p
    · have h := iso k hk
      have h' := P.earlier hp (fun e => ne (jp.trans e.symm)) tk
      omega
    · have h := iso j hj
      have h' := P.earlier hp jp tj
      omega
  · rintro ⟨⟨i,a⟩,h⟩
    classical
    have bad : ¬P.isolatedAt t i := fun iso => h ⟨hr,i,(P.at_above hr).mp a,iso⟩
    simp only [isolatedAt, Classical.not_forall, Nat.not_le] at bad
    obtain ⟨j,hj,tj⟩ := bad
    refine ⟨i,(P.at_other diff).mpr a,j,p,?_,hj,
      ((P.older_neighbor hp).mpr (.inr ⟨hr,a⟩)).1,by omega,by omega⟩
    rintro rfl; omega

theorem fill_sat {t} {p : Fin l} (hp : P.pos p = t) (i : Row) :
    bit (P.Sat (t+1) i) = ((P.profile t).insert (row t)).sat i := by
  apply bool_eq
  by_cases eq : i = row t
  · subst i
    simpa [Profile.insert, profile, Profile.above, row, upRow] using P.new_sat hp
  have hrow : i ≠ (⟨t%14, Nat.mod_lt _ (by decide)⟩ : Row) := eq
  by_cases prev : i.val + 1 = t%14
  · have hr : t%14 ≠ 0 := by omega
    have hi : i = upRow t := Fin.ext (by simp [upRow]; omega)
    simpa [Profile.insert, hrow, row, prev, profile] using
      (show P.Sat (t+1) i ↔ P.Occ t i ∧ ¬P.Pivot t from hi ▸ P.above_sat hp hr)
  · have iff : P.Sat (t+1) i ↔ P.Sat t i := by
      have same (j : Fin l) (a : P.At t i j) : P.Saturated (t+1) j ↔ P.Saturated t j := by
        apply P.same_saturation hp
        intro adj
        rcases (P.older_neighbor hp).mp ⟨adj,a.2.1⟩ with b | ⟨hr,b⟩
        · exact eq ((P.at_row a).trans (P.at_row b).symm)
        · have hi := (P.at_row a).trans (P.at_row b).symm
          have e := congrArg Fin.val hi
          simp [upRow] at e
          omega
      constructor
      · rintro ⟨j,a,h⟩
        have b := (P.at_other eq).mp a
        exact ⟨j,b,(same j b).mp h⟩
      · rintro ⟨j,a,h⟩
        exact ⟨j,(P.at_other eq).mpr a,(same j a).mpr h⟩
    simpa [Profile.insert, hrow, row, prev, profile] using iff

theorem fill_pivot {t} {p : Fin l} (hp : P.pos p = t) :
    bit (P.Pivot (t+1)) = ((P.profile t).insert (row t)).isolated := by
  apply bool_eq
  have h : P.Pivot (t+1) ↔ t%14 + 1 < 14 ∧ ¬P.Occ t (row t) ∧
      ¬(t%14 ≠ 0 ∧ P.Occ t (upRow t)) := by
    constructor
    · rintro ⟨hr,i,hi,iso⟩
      have eq : i=p := P.injective (by omega)
      subst i
      refine ⟨by omega,?_,?_⟩
      · rintro ⟨j,hj⟩
        obtain ⟨adj,old⟩ := (P.older_neighbor hp).mpr (.inl hj)
        have := iso j (flip adj); omega
      · rintro ⟨hr',j,hj⟩
        obtain ⟨adj,old⟩ := (P.older_neighbor hp).mpr (.inr ⟨hr',hj⟩)
        have := iso j (flip adj); omega
    · rintro ⟨hr,hl,hu⟩
      refine ⟨by omega,p,by omega,?_⟩
      intro j adj
      apply Nat.le_of_not_lt
      intro te
      have old := P.earlier hp (neighbor_ne (flip adj)) te
      rcases (P.older_neighbor hp).mp ⟨flip adj,old⟩ with a | ⟨hr',a⟩
      · exact hl ⟨j,a⟩
      · exact hu ⟨hr',j,a⟩
  change bit _ = true ↔ ((decide (t % 14 + 1 < 14) && !bit (P.Occ t (row t)))
    && !((t%14 != 0) && bit (P.Occ t (upRow t)))) = true
  rw [bit_true,h]
  by_cases hz : t % 14 = 0 <;> simp [hz, and_assoc]

theorem skip_sat {t} (hs : ∀ i, P.pos i ≠ t) (r : Row) :
    bit (P.Sat (t+1) r) = ((P.profile t).keep (row t)).sat r := by
  apply bool_eq
  by_cases eq : r = row t
  · subst r
    simp only [Profile.keep, bne_self_eq_false, Bool.false_and, Bool.false_eq_true, iff_false, bit_true]
    rintro ⟨i,a,_⟩; exact hs i (P.at_new.mp a)
  · have iff : P.Sat (t+1) r ↔ P.Sat t r := by
      constructor
      · rintro ⟨i,a,j,k,h,hj,hk,tj,tk⟩
        have h₁ := hs j; have h₂ := hs k
        exact ⟨i,(P.at_other eq).mp a,j,k,h,hj,hk,by omega,by omega⟩
      · rintro ⟨i,a,j,k,h,hj,hk,tj,tk⟩
        exact ⟨i,(P.at_other eq).mpr a,j,k,h,hj,hk,by omega,by omega⟩
    simpa [Profile.keep,eq,profile] using iff

theorem skip_pivot {t} (hs : ∀ i, P.pos i ≠ t) : ¬P.Pivot (t+1) := by
  rintro ⟨_,i,hi,_⟩
  exact hs i (by omega)

end Height14.Ranked
