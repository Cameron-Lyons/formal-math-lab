module

public import Wall133.OddRadiusSeven

@[expose] public section

namespace Wall133
open SimpleGraph

private def protectedGap (s : Finset (Fin 6)) (i : Fin 5) : Prop :=
  i.castSucc ∉ s ∧ i.succ ∉ s

private instance (s : Finset (Fin 6)) (i : Fin 5) : Decidable (protectedGap s i) := by
  unfold protectedGap; infer_instance

private def spaced (s : Finset (Fin 6)) : Prop :=
  s.card ≤ 2 ∧ ∀ i ∈ s, ∀ j ∈ s, j.val ≠ i.val+1
private instance (s : Finset (Fin 6)) : Decidable (spaced s) := by
  unfold spaced; infer_instance

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem distinct_gaps : ∀ s t : Finset (Fin 6), spaced s → spaced t →
    (s.card = 2 → s ≠ t) → ∃ i j : Fin 5, i ≠ j ∧ protectedGap s i ∧ protectedGap t j := by
  decide

variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Two stalled first extensions whose degrees are one below saturation have
distinct detours among the final six columns. -/
theorem two_even_row_stalls {d : ℕ} (P : Chain G (2*d+2)) (c : G.Coloring (Fin 2))
    (h4 : NoFourCycle G) (hd : 6 ≤ d) (x : Fin 2 ↪ V) (hx : ∀ r, Good P (x r))
    (hdeg : ∀ r, d ≤ G.degree (x r)) (sat : ∀ r z, ¬Good (grow P (x r) (hx r)) z) :
    2*d+6 ≤ G.path := by
  classical
  let R (r : Fin 2) := grow P (x r) (hx r)
  choose A B hw hpriv using fun r : Fin 2 =>
    near_saturation_with_witness (R r) c h4 (by omega)
      (by have := hdeg r; change (2*d+2+1)/2 ≤ G.degree (x r)+1; omega) (sat r)
  let idx (i : Fin 6) : Fin ((2*d+2+1)/2) := ⟨d-5+i.val,by have := i.isLt; omega⟩
  let site (i : Fin 6) := 2*(idx i).val+1
  have idx_inj : Function.Injective idx := by
    intro i j e
    exact Fin.ext (Nat.add_left_cancel (congrArg Fin.val e))
  have site_inj : Function.Injective site := by
    intro i j e
    apply idx_inj
    apply Fin.ext
    dsimp [site] at e
    omega
  have bounds (i : Fin 6) : 3 ≤ site i ∧ site i ≤ 2*d+2 := by
    have := i.isLt
    dsimp [site,idx]
    omega
  let bad (r : Fin 2) := Finset.univ.filter (fun i : Fin 6 => idx i=A r ∨ idx i=B r)
  have mem {r i} : i ∈ bad r ↔ idx i=A r ∨ idx i=B r := by simp [bad]
  have shared {r i j} (hij : i ≠ j) (hi : i ∈ bad r) (hj : j ∈ bad r) :
      ∃ w, G.Adj (x r) w ∧ G.Adj (P.vertex (site i)) w ∧ G.Adj (P.vertex (site j)) w := by
    have ne := fun e => hij (idx_inj e)
    have hi' := mem.mp hi
    have hj' := mem.mp hj
    rcases hw r with hab | ⟨w,hr,ha,hb⟩
    · rw [hab] at hi' hj'
      exact (ne ((hi'.elim id id).trans (hj'.elim id id).symm)).elim
    · change G.Adj (P.vertex (2*(A r).val+1)) w at ha
      change G.Adj (P.vertex (2*(B r).val+1)) w at hb
      change ∃ w, G.Adj (x r) w ∧ G.Adj (P.vertex (2*(idx i).val+1)) w ∧
        G.Adj (P.vertex (2*(idx j).val+1)) w
      exact ⟨w,hr,hi'.elim (fun h => h ▸ ha) (fun h => h ▸ hb),
        hj'.elim (fun h => h ▸ ha) (fun h => h ▸ hb)⟩
  have goodRows (r : Fin 2) : spaced (bad r) := by
    constructor
    · have hh : (bad r).image idx ⊆ {A r,B r} := by
        intro y hy
        obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hy
        simpa using mem.mp hi
      have h := Finset.card_le_card hh
      rw [Finset.card_image_of_injective _ idx_inj] at h
      exact h.trans (Finset.card_le_two)
    · intro i hi j hj hsucc
      have hs : site i+2 = site j := by dsimp [site,idx]; omega
      have hne : i ≠ j := by intro he; rw [he] at hsucc; omega
      obtain ⟨w,hr,hiw,hjw⟩ := shared hne hi hj
      have hn : P.vertex (site i) ≠ P.vertex (site j) :=
        fun e => hne (site_inj (P.inj (bounds i).2 (bounds j).2 e))
      have e := h4 hn hiw hjw
        ((P.edges (bounds i).2 (show site i+1 ≤ 2*d+2 by have := bounds j; omega)).2 (Or.inl rfl))
        ((P.edges (bounds j).2 (show site i+1 ≤ 2*d+2 by have := bounds j; omega)).2 (Or.inr hs))
      exact (hx r).2.2 _ (by have := bounds j; omega) (by omega) (e ▸ hr)
  have diff (r t : Fin 2) (hrt : r ≠ t) (hc : (bad r).card=2) (e : bad r=bad t) : False := by
    obtain ⟨i,j,hi,hj,hij⟩ := Finset.one_lt_card_iff.mp (show 1 < (bad r).card by omega)
    obtain ⟨w,hr,hiw,hjw⟩ := shared hij hi hj
    obtain ⟨z,ht,hiz,hjz⟩ := shared hij (e ▸ hi) (e ▸ hj)
    have hn : P.vertex (site i) ≠ P.vertex (site j) :=
      fun he => hij (site_inj (P.inj (bounds i).2 (bounds j).2 he))
    have hwz := h4 hn hiw hjw hiz hjz
    have hw₀ := h4 (fun he => hrt (x.injective he)) hr (hwz ▸ ht) (hx r).1.symm (hx t).1.symm
    rw [hw₀] at hiw
    have := (P.edges (bounds i).2 (Nat.zero_le _)).1 hiw
    have := (bounds i).1
    omega
  have contact {r i} (hi : i ∉ bad r) :
      ∃ w, G.Adj (x r) w ∧ Off P w (· = site i) := by
    have hgood := hpriv r (idx i) (fun e => hi (mem.mpr (Or.inl e))) (fun e => hi (mem.mpr (Or.inr e)))
    exact contactOnSuffix P (R r) (r := 1) (by decide) (by have := bounds i; omega) (bounds i).2
      le_rfl (fun _ _ => rfl) (fun a ha h => ((offGood (hx r)).contact a ha).mp h)
      (idx i) rfl hgood
  obtain ⟨i,j,hij,hi,hj⟩ := distinct_gaps _ _ (goodRows 0) (goodRows 1)
    (diff 0 1 (by decide))
  have detour (r t : Fin 2) (i j : Fin 5) (hrt : r ≠ t)
      (hij : i.val < j.val) (hi : protectedGap (bad r) i) (hj : protectedGap (bad t) j) :
      2*d+6 ≤ G.path := by
    have succSite (k : Fin 5) : site k.succ = site k.castSucc+2 := by dsimp [site,idx]; omega
    have sep : site i.castSucc+2 ≤ site j.castSucc := by dsimp [site,idx]; omega
    have last : site j.castSucc+2 ≤ 2*d+2 := by rw [←succSite]; exact (bounds _).2
    obtain ⟨Q,_⟩ := twoDetours P c h4 (by have := (bounds i.castSucc).1; omega) sep last
      (hx r) (hx t) (fun e => hrt (x.injective e))
      (contact hi.1) ((succSite i) ▸ contact hi.2)
      (contact hj.1) ((succSite j) ▸ contact hj.2)
    exact Q.length_le
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h|h
  · exact detour 0 1 i j (by decide) h hi hj
  · exact detour 1 0 j i (by decide) h hj hi

end Wall133
