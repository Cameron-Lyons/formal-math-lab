module

public import Wall133.GirthSix
public import Wall133.GeodesicRotation

@[expose] public section

namespace Wall133
open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- On a stalled induced path of length twice the endpoint degree lower bound,
a neighbor has exactly one positive contact with the path, at its far end. -/
theorem girth_six_private_end [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {u v : V} {p : G.Walk u v} (hg : 6 ≤ G.egirth) (hp : Chordless p)
    {d : ℕ} (hd : 3 ≤ d) (hlen : p.length=2*d) (hdeg : d ≤ G.degree u)
    (sat : ∀ w, G.Adj u w → w ∉ p.support →
      ∃ i ≤ p.length, i≠0 ∧ G.Adj w (p.getVert i)) :
    ∃ w, G.Adj u w ∧ G.Adj (p.getVert (2*d)) w ∧
      ∀ i ≤ p.length, i≠0 → G.Adj (p.getVert i) w → i=2*d := by
  classical
  let W := (G.neighborFinset u).erase (p.getVert 1)
  have info (w : W) : G.Adj u w.val ∧ w.val ∉ p.support := by
    obtain ⟨hne,hadj⟩ := Finset.mem_erase.mp w.property
    have ha := (G.mem_neighborFinset _ _).mp hadj
    exact ⟨ha,hp.pending_off_path ha hne⟩
  choose idx hi hz hadj using fun w : W => sat w.val (info w).1 (info w).2
  have lower {w : W} {i : ℕ} (hlen' : i ≤ p.length) (hpos : i ≠ 0)
      (h : G.Adj w.val (p.getVert i)) : 4 ≤ i := by
    have := first_blocker (g := 6) hg hp (info w).1 (info w).2 hlen' hpos h
    omega
  have uniqueSite {w z : W} {i j : ℕ} (ilen : i ≤ p.length) (jlen : j ≤ p.length)
      (ipos : i ≠ 0) (jpos : j ≠ 0) (hwi : G.Adj w.val (p.getVert i))
      (hzj : G.Adj z.val (p.getVert j)) (he : (i-4)/2=(j-4)/2) : w=z := by
    by_contra hne
    have il := lower ilen ipos hwi
    have jl := lower jlen jpos hzj
    rcases le_total i j with ij|ji
    · have := separated_blockers (g := 6) hg hp (info w).1 (info z).1 (info w).2 (info z).2
        (fun h => hne (Subtype.ext h)) (by omega) ij jlen hwi hzj (by decide)
      omega
    · have := separated_blockers (g := 6) hg hp (info z).1 (info w).1 (info z).2 (info w).2
        (fun h => hne (Subtype.ext h.symm)) (by omega) ji ilen hzj hwi (by decide)
      omega
  let code (w : W) : Fin (d-1) := ⟨(idx w-4)/2,by have := hi w; omega⟩
  have inj : Function.Injective code := fun w z e =>
    uniqueSite (hi w) (hi z) (hz w) (hz z) (hadj w) (hadj z) (congrArg Fin.val e)
  have surj : Function.Surjective code := by
    apply ((Fintype.bijective_iff_injective_and_card code).2 ⟨inj,?_⟩).2
    apply le_antisymm (Fintype.card_le_of_injective code inj)
    have er : G.degree u-1 ≤ W.card := Finset.pred_card_le_card_erase
    simp only [Fintype.card_coe,Fintype.card_fin]
    omega
  let last : Fin (d-1) := ⟨d-2,by omega⟩
  obtain ⟨w,hw⟩ := surj last
  have ends : idx w = 2*d := by
    have := congrArg Fin.val hw
    change (idx w-4)/2=d-2 at this
    have := hi w
    omega
  refine ⟨w,(info w).1,ends ▸ (hadj w).symm,?_⟩
  intro i ilen ipos hwi
  let slot : Fin (d-1) := ⟨(i-4)/2,by omega⟩
  obtain ⟨z,hz'⟩ := surj slot
  have eq := congrArg Fin.val hz'
  change (idx z-4)/2 = (i-4)/2 at eq
  have ez := uniqueSite (hi z) ilen (hz z) ipos (hadj z) hwi.symm eq
  rw [ez,ends] at eq
  omega

end Wall133
