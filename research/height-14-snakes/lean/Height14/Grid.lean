import Height14.Boundary
import Height14.Degrees

namespace Height14.Ranked
variable {w l : Nat} (P : Ranked w l)

private theorem insert_profile {t} {p : Fin l} (hp : P.pos p=t) :
    P.profile (t+1) = (P.profile t).insert (row t) := by
  apply Profile.ext
  · exact (bit_false _).mpr (P.fill_not_done hp).2
  · exact funext (P.occ_insert hp)
  · exact funext (P.fill_sat hp)
  · exact funext fun r => funext (P.link_insert hp r)
  · exact P.fill_pivot hp

private theorem keep_profile {t} (hs : ∀ i, P.pos i≠t) (live : ¬P.Done (t+1)) :
    P.profile (t+1) = (P.profile t).keep (row t) := by
  apply Profile.ext
  · exact (bit_false _).mpr live
  · exact funext (P.occ_keep hs)
  · exact funext (P.skip_sat hs)
  · exact funext fun r => funext (P.link_skip hs r)
  · exact (bit_false _).mpr (P.skip_pivot hs)

/-- Scanning an actual induced grid path always follows a legal transition,
with the boundary predicted by its intervals of processed path indices. -/
theorem step (t : Nat) :
    (P.profile t).change (row t) (P.fills t) = some (P.profile (t+1)) := by
  classical
  by_cases filled : ∃ i, P.pos i=t
  · obtain ⟨p,hp⟩ := filled
    have fill : P.fills t = true := (bit_true _).mpr ⟨p,hp⟩
    have live : (P.profile t).done = false := (bit_false _).mpr (P.fill_not_done hp).1
    have sat := P.fill_unsaturated hp
    have left : (P.profile t).sat (row t) = false := (bit_false _).mpr sat.1
    have up : Profile.above (P.profile t).sat (row t) = false := by
      apply Bool.eq_false_iff.mpr
      simp only [ne_eq, Profile.above, profile, row, Bool.and_eq_true, bne_iff_ne, bit_true]
      rintro ⟨r,h⟩; exact sat.2 r h
    simp [Profile.change,fill,live,left,up,P.neighbors_unlinked hp,P.insert_profile hp]
  · have skipped : ∀ i, P.pos i≠t := fun i hi => filled ⟨i,hi⟩
    have skip : P.fills t = false := (bit_false _).mpr filled
    by_cases done : P.Done t
    · have done' := P.skip_done done
      rw [skip,P.finished_profile done,P.finished_profile done']
      rfl
    · have live : (P.profile t).done = false := (bit_false _).mpr done
      let stays := ¬P.Occ t (row t) ∨ ∃ r, r≠row t ∧ P.Link t r (row t)
      have test : (!((P.profile t).occ (row t)) ||
          decide (∃ r, r≠row t ∧ (P.profile t).linked r (row t)=true)) = true ↔ stays := by
        simp [profile,stays]
      by_cases keep : stays
      · have b := test.mpr keep
        simp [Profile.change,skip,live,b,P.keep_profile skipped (P.keep_live skipped done keep)]
      · have here : P.Occ t (row t) := Classical.byContradiction (fun h => keep (.inl h))
        have gone := P.sealed_component skipped here (fun h => keep (.inr h))
        have b := Bool.eq_false_iff.mpr (fun h => keep (test.mp h))
        have noOther : ¬∃ i, i≠row t ∧ (P.profile t).occ i = true := by
          simpa only [profile,bit_true] using gone.2
        simp [Profile.change,skip,live,b,noOther,P.finished_profile gone.1]

end Height14.Ranked
