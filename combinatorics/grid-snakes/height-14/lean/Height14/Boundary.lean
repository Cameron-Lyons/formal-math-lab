import Height14.Links

namespace Height14.Ranked
open Interval
variable {w l : Nat} (P : Ranked w l)

noncomputable def fills (t : Nat) : Bool := bit (∃ i, P.pos i=t)

theorem initial : P.profile 0 = Profile.empty := by
  have h (r : Row) (i : Fin l) : ¬P.At 0 r i := fun h => Nat.not_lt_zero _ h.2.1
  apply Profile.ext <;> simp [profile,Profile.empty,Done,Occ,Sat,Link,Pivot,h,
    funext_iff]
  exact ⟨⟨0,P.nonempty⟩,trivial⟩

theorem final_accept : (P.profile (14*w)).accept = true := by
  have hall (i : Fin l) : P.pos i<14*w := by have := P.bounded i; omega
  by_cases occ : ∃ r, P.Occ (14*w) r
  · have linked (r s : Row) (hr : P.Occ (14*w) r) (hs : P.Occ (14*w) s) :
        P.Link (14*w) r s := by
      obtain ⟨i,hi⟩ := hr; obtain ⟨j,hj⟩ := hs
      exact ⟨i,j,hi,hj,fun z _ => hall z⟩
    apply Bool.or_eq_true_iff.mpr; right
    apply Bool.and_eq_true_iff.mpr
    constructor
    · apply decide_eq_true
      obtain ⟨r,hr⟩ := occ
      exact ⟨r,(bit_true _).mpr hr⟩
    · apply decide_eq_true
      intro r q hr hq
      exact (bit_true _).mpr (linked _ _ ((bit_true _).mp hr) ((bit_true _).mp hq))
  · have d : P.Done (14*w) := ⟨hall,occ⟩
    exact Bool.or_eq_true_iff.mpr (.inl ((bit_true _).mpr d))

theorem finished_profile {t} (done : P.Done t) : P.profile t = Profile.finished := by
  have h (r : Row) (i : Fin l) : ¬P.At t r i := fun hi => done.2 ⟨r,i,hi⟩
  have h' : ¬P.Pivot t := by
    rintro ⟨hr,i,hi,_⟩
    exact h _ _ ((P.at_above hr).mpr hi)
  apply Profile.ext <;> simp [profile,Profile.finished,Profile.empty,Occ,Sat,Link,h,
    done,h',funext_iff]

theorem occ_insert {t} {p : Fin l} (hp : P.pos p=t) (r : Row) :
    bit (P.Occ (t+1) r) = ((P.profile t).insert (row t)).occ r := by
  apply Bool.eq_iff_iff.mpr
  by_cases hr : r=row t
  · subst r
    simpa [Profile.insert] using (show P.Occ (t+1) (row t) from ⟨p,P.at_new.mpr hp⟩)
  · simp [Profile.insert,profile,Occ,hr,P.at_other hr]

theorem occ_keep {t} (hs : ∀ i, P.pos i ≠ t) (r : Row) :
    bit (P.Occ (t+1) r) = ((P.profile t).keep (row t)).occ r := by
  apply Bool.eq_iff_iff.mpr
  simp [Profile.keep,profile,Occ,P.at_skip hs,exists_and_left]

theorem fill_not_done {t} {p : Fin l} (hp : P.pos p=t) : ¬P.Done t ∧ ¬P.Done (t+1) := by
  constructor
  · intro h; have := h.1 p; omega
  · intro h; exact h.2 ⟨_,p,P.at_new.mpr hp⟩

theorem skip_done {t} (h : P.Done t) : P.Done (t+1) := by
  have skipped (i : Fin l) : P.pos i ≠ t := by have := h.1 i; omega
  refine ⟨fun i => Nat.lt_succ_of_lt (h.1 i),?_⟩
  rintro ⟨r,i,hi⟩
  exact h.2 ⟨r,i,((P.at_skip skipped).mp hi).2⟩

/-- Omitting the current square either keeps every live component on the
boundary, or seals the whole path. -/
theorem keep_live {t} (skipped : ∀ i, P.pos i ≠ t) (live : ¬P.Done t)
    (remains : ¬P.Occ t (row t) ∨ ∃ r, r ≠ row t ∧ P.Link t r (row t)) :
    ¬ P.Done (t+1) := by
  intro h
  rcases remains with empty | ⟨r,hr,hrl⟩
  · apply live
    refine ⟨fun i => ?_, ?_⟩
    · have := h.1 i; have := skipped i; omega
    · rintro ⟨r,i,hi⟩
      by_cases hr : r=row t
      · subst r; exact empty ⟨i,hi⟩
      · exact h.2 ⟨r,i,(P.at_other hr).mpr hi⟩
  · obtain ⟨i,hi⟩ := P.occ_of_link hrl
    exact h.2 ⟨r,i,(P.at_other hr).mpr hi⟩

theorem sealed_component {t} (skipped : ∀ i, P.pos i ≠ t) (atCut : P.Occ t (row t))
    (vanishes : ¬∃ r, r ≠ row t ∧ P.Link t r (row t)) :
    P.Done (t+1) ∧ ¬∃ r, r ≠ row t ∧ P.Occ t r := by
  classical
  obtain ⟨i,hi⟩ := atCut
  have old : P.pos i < t+1 := Nat.lt_succ_of_lt hi.2.1
  have hall (j : Fin l) : P.pos j < t+1 := by
    apply Classical.byContradiction
    intro bad
    have later : t+1 ≤ P.pos j := by omega
    obtain ⟨a,b,hia,adj,hb⟩ := exit_edge i j old later
    have here := P.edge_hits_boundary adj (joined_right hia) hb
    obtain ⟨neq,pre⟩ := (P.at_skip skipped).mp here
    exact vanishes ⟨_,neq,a,i,pre,hi,joined_symm ((joined_skip skipped).mp hia)⟩
  have allOld (j : Fin l) : P.pos j<t := by have := hall j; have := skipped j; omega
  have none : ¬∃ r, r ≠ row t ∧ P.Occ t r := by
    rintro ⟨r,hr,j,hj⟩
    exact vanishes ⟨r,hr,j,i,hj,hi,fun z _ => allOld z⟩
  refine ⟨⟨hall,?_⟩,none⟩
  rintro ⟨r,j,hj⟩
  obtain ⟨hr,hold⟩ := (P.at_skip skipped).mp hj
  exact none ⟨r,hr,j,hold⟩

theorem count_fills : (List.range (14*w)).countP P.fills = l := by
  let selected := (List.range (14*w)).filter P.fills
  let path := (List.finRange l).map P.pos
  have selected_nd : selected.Nodup := (List.nodup_range).filter _
  have path_nd : path.Nodup := (List.nodup_finRange l).map P.pos (fun _ _ h e => h (P.injective e))
  have perm : selected.Perm path := (List.perm_ext_iff_of_nodup selected_nd path_nd).mpr (by
    intro a
    simp only [selected,path,List.mem_filter,List.mem_range,List.mem_map,List.mem_finRange,
       true_and,fills,bit_true]
    constructor
    · exact And.right
    · rintro ⟨i,rfl⟩; exact ⟨by have := P.bounded i; omega,i,rfl⟩)
  simpa [List.countP_eq_length_filter,selected,path] using perm.length_eq

end Height14.Ranked
