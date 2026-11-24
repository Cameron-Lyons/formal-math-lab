import Wall133.OddLastDetour

/-!
# Two detours near the end of an odd path

Each saturated row can lose two columns to a shared neighbor. Distinct rows
cannot lose the same pair. The final column can be used to extend the path
as well as to finish an internal detour.
-/
namespace Wall133
open SimpleGraph

private def feature (s : Finset (Fin 4)) (i : Fin 4) : Prop :=
  i ∉ s ∧ ∀ j : Fin 4, j.val = i.val+1 → j ∉ s

private instance (s : Finset (Fin 4)) (i : Fin 4) : Decidable (feature s i) := by
  unfold feature; infer_instance

private def separated (s : Finset (Fin 4)) : Prop :=
  s.card ≤ 2 ∧ ∀ i ∈ s, ∀ j ∈ s, j.val ≠ i.val+1
private instance (s : Finset (Fin 4)) : Decidable (separated s) := by
  unfold separated; infer_instance

/-- At the four last columns of three rows, two distinct usable positions
can be chosen on different rows. A position at the right edge only uses
the last column. -/
private theorem two_features (s : Fin 3 → Finset (Fin 4))
    (h : ∀ r, separated (s r))
    (hdiff : ∀ r t, r ≠ t → (s r).card = 2 → s r ≠ s t) :
    ∃ r t, ∃ i j : Fin 4, r ≠ t ∧ i ≠ j ∧ feature (s r) i ∧ feature (s t) j := by
  let disj (a b : Finset (Fin 4)) := ∃ i j : Fin 4, i ≠ j ∧ feature a i ∧ feature b j
  have none (a : Finset (Fin 4)) (ha : separated a) (hna : ¬∃ i, feature a i) :
      a = {1,3} := by
    have hh : ∀ a : Finset (Fin 4), separated a → (¬∃ i, feature a i) → a={1,3} := by decide
    exact hh a ha hna
  have pair (a b : Finset (Fin 4)) (ha : separated a) (hb : separated b)
      (ha' : ∃ i, feature a i) (hb' : ∃ i, feature b i)
      (hne : a.card = 2 → a ≠ b) : disj a b := by
    have hh : ∀ a b : Finset (Fin 4), separated a → separated b →
        (∃ i, feature a i) → (∃ i, feature b i) → (a.card = 2 → a ≠ b) →
        ∃ i j, i ≠ j ∧ feature a i ∧ feature b j := by decide
    exact hh a b ha hb ha' hb' hne
  have atMostOne {r t : Fin 3} (hrt : r ≠ t) (h₁ : ¬∃ i, feature (s r) i) :
      ∃ i, feature (s t) i := by
    by_contra h₂
    have he₁ := none _ (h r) h₁
    have he₂ := none _ (h t) h₂
    exact hdiff r t hrt (by rw [he₁]; decide) (he₁.trans he₂.symm)
  have ex (r t : Fin 3) (hrt : r ≠ t) (hr : ∃ i, feature (s r) i) (ht : ∃ i, feature (s t) i) :
      ∃ r t, ∃ i j : Fin 4, r ≠ t ∧ i ≠ j ∧ feature (s r) i ∧ feature (s t) j := by
    obtain ⟨i,j,hij,hi,hj⟩ := pair _ _ (h r) (h t) hr ht (hdiff r t hrt)
    exact ⟨r,t,i,j,hrt,hij,hi,hj⟩
  by_cases h₀ : ∃ i, feature (s 0) i
  · by_cases h₁ : ∃ i, feature (s 1) i
    · exact ex 0 1 (by decide) h₀ h₁
    · exact ex 0 2 (by decide) h₀ (atMostOne (by decide : (1:Fin 3) ≠ 2) h₁)
  · exact ex 1 2 (by decide) (atMostOne (by decide : (0:Fin 3) ≠ 1) h₀)
      (atMostOne (by decide : (0:Fin 3) ≠ 2) h₀)

variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

omit [DecidableEq V] in
/-- Three stalled rows supply usable contact sites at distinct positions
among the last four columns of the path. -/
private theorem end_features {d : ℕ} (P : Chain G (2*d+1)) (c : G.Coloring (Fin 2))
    (h4 : NoFourCycle G) (hd : 4 ≤ d) (x : Fin 3 ↪ V) (hx : ∀ r, Good P (x r))
    (hdeg : ∀ r, d ≤ G.degree (x r)) (sat : ∀ r z, ¬Good (grow P (x r) (hx r)) z) :
    ∃ r t : Fin 3, ∃ i j : ℕ, r ≠ t ∧ i < j ∧ 3 ≤ i ∧ j ≤ 2*d+1 ∧ i+2 ≤ j ∧
      (∃ a, G.Adj (x r) a ∧ Off P a (· = i)) ∧
      (∃ b, G.Adj (x r) b ∧ Off P b (· = i+2)) ∧
      (∃ p, G.Adj (x t) p ∧ Off P p (· = j)) ∧
      (j=2*d+1 ∨ (j+2 ≤ 2*d+1 ∧ ∃ q, G.Adj (x t) q ∧ Off P q (· = j+2))) := by
  classical
  let R (r : Fin 3) := grow P (x r) (hx r)
  choose A B hw hpriv using fun r : Fin 3 =>
    near_saturation_with_witness (R r) c h4 (by omega)
      (by have := hdeg r; change (2*d+1+1)/2 ≤ G.degree (x r)+1; omega) (sat r)
  let idx (i : Fin 4) : Fin ((2*d+1+1)/2) := ⟨d-3+i.val,by have := i.isLt; omega⟩
  let site (i : Fin 4) := 2*(idx i).val+1
  have idx_inj : Function.Injective idx := by
    intro i j e
    exact Fin.ext (Nat.add_left_cancel (congrArg Fin.val e))
  have site_inj : Function.Injective site := by
    intro i j e
    apply idx_inj
    apply Fin.ext
    dsimp [site] at e
    omega
  have bounds (i : Fin 4) : 3 ≤ site i ∧ site i ≤ 2*d+1 := by
    have := i.isLt
    dsimp [site,idx]
    omega
  let bad (r : Fin 3) := Finset.univ.filter (fun i : Fin 4 => idx i=A r ∨ idx i=B r)
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
  have goodRows (r : Fin 3) : separated (bad r) := by
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
        ((P.edges (bounds i).2 (show site i+1 ≤ 2*d+1 by have := bounds j; omega)).2 (Or.inl rfl))
        ((P.edges (bounds j).2 (show site i+1 ≤ 2*d+1 by have := bounds j; omega)).2 (Or.inr hs))
      exact (hx r).2.2 _ (by have := bounds j; omega) (by omega) (e ▸ hr)
  have diff (r t : Fin 3) (hrt : r ≠ t) (hc : (bad r).card=2) (e : bad r=bad t) : False := by
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
  obtain ⟨r,t,i,j,hrt,hij,hi,hj⟩ := two_features bad goodRows diff
  have ordered (r t : Fin 3) (i j : Fin 4) (hrt : r ≠ t) (hij : i.val < j.val)
      (hi : feature (bad r) i) (hj : feature (bad t) j) :
      ∃ r t : Fin 3, ∃ i j : ℕ, r ≠ t ∧ i < j ∧ 3 ≤ i ∧ j ≤ 2*d+1 ∧ i+2 ≤ j ∧
      (∃ a, G.Adj (x r) a ∧ Off P a (· = i)) ∧
      (∃ b, G.Adj (x r) b ∧ Off P b (· = i+2)) ∧
      (∃ p, G.Adj (x t) p ∧ Off P p (· = j)) ∧
      (j=2*d+1 ∨ (j+2 ≤ 2*d+1 ∧ ∃ q, G.Adj (x t) q ∧ Off P q (· = j+2))) := by
    have hs : site i+2 ≤ site j := by dsimp [site,idx]; omega
    let next : Fin 4 := ⟨i.val+1, by have := j.isLt; omega⟩
    have he : site next = site i+2 := by dsimp [site,idx,next]; omega
    refine ⟨r,t,site i,site j,hrt,by omega,(bounds i).1,(bounds j).2,hs,contact hi.1,
      he ▸ contact (hi.2 next rfl),contact hj.1,?_⟩
    by_cases hlast : j.val = 3
    · left; dsimp [site,idx]; omega
    · let k : Fin 4 := ⟨j.val+1,by have := j.isLt; omega⟩
      have he' : site k = site j+2 := by dsimp [site,idx,k]; omega
      exact Or.inr ⟨he' ▸ (bounds k).2,he' ▸ contact (hj.2 k rfl)⟩
  have hval := Fin.val_ne_of_ne hij
  rcases lt_or_gt_of_ne hval with h | h
  · exact ordered r t i j hrt h hi hj
  · exact ordered t r j i hrt.symm h hj hi

/-- Three unsuccessful extensions at a vertex of degree at least `d+3`
give a path on `2*d+5` vertices even at the first threshold `d=4`. -/
theorem three_row_stalls {d : ℕ} (P : Chain G (2*d+1)) (c : G.Coloring (Fin 2))
    (h4 : NoFourCycle G) (hd : 4 ≤ d) (hmin : ∀ u, d ≤ G.degree u)
    (hdeg : d+3 ≤ G.degree (P.vertex 0))
    (sat : ∀ x (hx : Good P x) z, ¬Good (grow P x hx) z) :
    2*d+5 ≤ G.path := by
  classical
  let N := (G.neighborFinset (P.vertex 0)).filter (Good P)
  have hcount := good_card P c h4 (by omega)
  change G.degree (P.vertex 0) ≤ N.card+(2*d+1)/2 at hcount
  have hN : 3 ≤ Fintype.card N := by rw [Fintype.card_coe]; omega
  let x := ((Fin.castLEEmb hN).trans (Fintype.equivFin N).symm.toEmbedding).trans
    (Function.Embedding.subtype (· ∈ N))
  have hx (r : Fin 3) : Good P (x r) :=
    (Finset.mem_filter.mp ((Fintype.equivFin N).symm (Fin.castLE hN r)).property).2
  obtain ⟨r,t,i,j,hrt,_,hi,hj,hij,w₁,w₂,w₃,he⟩ :=
    end_features P c h4 hd x hx (fun r => hmin _) (fun r => sat _ (hx r))
  have hxy := fun h => hrt (x.injective h)
  rcases he with rfl | ⟨hjn,w₄⟩
  · exact detour_and_append P c h4 (by omega) hij (hx r) (hx t) hxy w₁ w₂ w₃
  · obtain ⟨Q,_⟩ := twoDetours P c h4 (by omega) hij hjn (hx r) (hx t) hxy w₁ w₂ w₃ w₄
    exact Q.length_le

theorem small_odd_double_stalls {d : ℕ} (P : Chain G (2*d+1)) (c : G.Coloring (Fin 2))
    (h4 : NoFourCycle G) (hd : 4 ≤ d) (hmin : ∀ u, d ≤ G.degree u)
    (hdeg : 2*d-1 ≤ G.degree (P.vertex 0))
    (sat : ∀ x (hx : Good P x) z, ¬Good (grow P x hx) z) :
    2*d+5 ≤ G.path :=
  three_row_stalls P c h4 hd hmin (by omega) sat

end Wall133
