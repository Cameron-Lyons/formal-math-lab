module

public import Wall133.RadiusFive

@[expose] public section

/-!
# The degree-three endpoint switch
Two unsuccessful extensions of a six-edge path yield alternative eight-edge
paths. Saturation of both at their common endpoint would give a four-cycle.
-/
namespace Wall133
open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj]

private theorem private_contact (P : Chain G 6) (c : G.Coloring (Fin 2))
    (h4 : NoFourCycle G) {x : V} (hx : Good P x) (hd : 3 ≤ G.degree x)
    (sat : ∀ z, ¬Good (grow P x hx) z) (j : Fin 3) :
    ∃ z, G.Adj x z ∧ ∀ i ≤ 6, (G.Adj (P.vertex i) z ↔ i = 2*j.val+1) := by
  obtain ⟨z,hz,hs,hu⟩ := saturated_witness (grow P x hx) c h4 (by decide) hd sat j
  refine ⟨z,hz,fun i hi => ⟨fun h => ?_, fun e => ?_⟩⟩
  · have hh := hu (i+1) (by omega) (by omega) h
    omega
  · have he : 2*j.val+2 = (2*j.val+1)+1 := by omega
    rw [he] at hs
    exact e ▸ hs

private def switchVert (P : Chain G 6) (x y z w : V) : ℕ → V
  | 0 => P.vertex 6
  | 1 => P.vertex 5
  | 2 => w
  | 3 => y
  | 4 => P.vertex 0
  | 5 => x
  | 6 => z
  | 7 => P.vertex 3
  | _ => P.vertex 2

omit [Fintype V] [DecidableRel G.Adj] in
private theorem nonadj_of_common (c : G.Coloring (Fin 2)) {x y z : V}
    (hx : G.Adj z x) (hy : G.Adj z y) : ¬G.Adj x y := by
  intro h
  have := Fin.val_ne_of_ne (c.valid hx)
  have := Fin.val_ne_of_ne (c.valid hy)
  have := Fin.val_ne_of_ne (c.valid h)
  have := (c x).isLt
  have := (c y).isLt
  have := (c z).isLt
  omega

private def switchChain (P : Chain G 6) (c : G.Coloring (Fin 2)) (h4 : NoFourCycle G)
    {x y z w : V} (hx : Good P x) (hy : Good P y) (hxy : x ≠ y)
    (hxz : G.Adj x z) (hyw : G.Adj y w)
    (hz : ∀ i ≤ 6, G.Adj (P.vertex i) z ↔ i = 3)
    (hw : ∀ i ≤ 6, G.Adj (P.vertex i) w ↔ i = 5) : Chain G 8 := by
  let f := switchVert P x y z w
  have hxe (i : ℕ) (hi : i ≤ 6) : G.Adj (P.vertex i) x ↔ i = 0 :=
    ⟨fun h => by by_contra hh; exact hx.2.2 i hi hh h.symm, fun e => e ▸ hx.1⟩
  have hye (i : ℕ) (hi : i ≤ 6) : G.Adj (P.vertex i) y ↔ i = 0 :=
    ⟨fun h => by by_contra hh; exact hy.2.2 i hi hh h.symm, fun e => e ▸ hy.1⟩
  have hxe' i hi := (G.adj_comm x (P.vertex i)).trans (hxe i hi)
  have hye' i hi := (G.adj_comm y (P.vertex i)).trans (hye i hi)
  have hz' i hi := (G.adj_comm z (P.vertex i)).trans (hz i hi)
  have hw' i hi := (G.adj_comm w (P.vertex i)).trans (hw i hi)
  have hcross {s : V} {i : ℕ} (hi : i = 3 ∨ i = 5) (hs : G.Adj (P.vertex i) s) :
      ¬ (G.Adj x s ∧ G.Adj y s) := by
    rintro ⟨h₁,h₂⟩
    have he := h4 hxy hx.1.symm hy.1.symm h₁ h₂
    rw [← he] at hs
    have := (P.edges (by omega) (Nat.zero_le _)).1 hs
    omega
  have hxw : ¬G.Adj x w := fun h => hcross (Or.inr rfl) ((hw 5 (by decide)).2 rfl) ⟨h,hyw⟩
  have hyz : ¬G.Adj y z := fun h => hcross (Or.inl rfl) ((hz 3 (by decide)).2 rfl) ⟨hxz,h⟩
  have hxy' := nonadj_of_common c hx.1 hy.1
  have hzw : ¬G.Adj z w := by
    intro h
    have h₁ := Fin.val_ne_of_ne (c.valid hx.1)
    have h₂ := Fin.val_ne_of_ne (c.valid hy.1)
    have h₃ := Fin.val_ne_of_ne (c.valid hxz)
    have h₄ := Fin.val_ne_of_ne (c.valid hyw)
    have h₅ := Fin.val_ne_of_ne (c.valid h)
    have := (c x).isLt
    have := (c y).isLt
    have := (c z).isLt
    have := (c w).isLt
    have := (c (P.vertex 0)).isLt
    omega
  have edges {i j} (hi : i ≤ 8) (hj : j ≤ 8) :
      G.Adj (f i) (f j) ↔ i+1=j ∨ j+1=i := by
    interval_cases i <;> interval_cases j <;>
      simp (disch := decide) [f, switchVert, P.edges, hxe, hye, hz, hw, hxe', hye', hz', hw',
        hxz, hxz.symm, hyw, hyw.symm, hxw, mt Adj.symm hxw, hyz, mt Adj.symm hyz,
        hxy', mt Adj.symm hxy', hzw, mt Adj.symm hzw]
  refine ⟨f,?_,edges⟩
  intro i j hi hj h
  have twins : ∀ i j : Fin 9, (∀ k : Fin 9,
      (i.val+1=k.val ∨ k.val+1=i.val) ↔ (j.val+1=k.val ∨ k.val+1=j.val)) → i=j := by decide
  apply congrArg Fin.val (twins ⟨i,by omega⟩ ⟨j,by omega⟩ ?_)
  intro k
  have hk : k.val ≤ 8 := by omega
  exact (edges hi hk).symm.trans ((congrArg (fun v => G.Adj v (f k.val)) h).to_iff.trans (edges hj hk))

/-- The two alternative extensions at the low-degree threshold already force
a ten-vertex induced path. -/
theorem ten_le_path_of_two_stalls [DecidableEq V] (P : Chain G 6) (c : G.Coloring (Fin 2))
    (h4 : NoFourCycle G) {x y : V} (hx : Good P x) (hy : Good P y) (hxy : x ≠ y)
    (hdx : 3 ≤ G.degree x) (hdy : 3 ≤ G.degree y) (hd6 : 4 ≤ G.degree (P.vertex 6))
    (sx : ∀ z, ¬Good (grow P x hx) z) (sy : ∀ z, ¬Good (grow P y hy) z) :
    10 ≤ G.path := by
  obtain ⟨a,hxa,ha⟩ := private_contact P c h4 hx hdx sx 1
  obtain ⟨b,hxb,hb⟩ := private_contact P c h4 hx hdx sx 2
  obtain ⟨a',hya,ha'⟩ := private_contact P c h4 hy hdy sy 1
  obtain ⟨b',hyb,hb'⟩ := private_contact P c h4 hy hdy sy 2
  let Q := switchChain P c h4 hx hy hxy hxa hyb ha hb'
  let R := switchChain P c h4 hy hx hxy.symm hya hxb ha' hb
  by_contra! hshort
  have sat (T : Chain G 8) (z : V) : ¬Good T z := fun h => by
    have := (grow T z h).length_le
    omega
  obtain ⟨z,he,haz,only⟩ := saturated_witness Q c h4 (by decide) hd6 (sat Q) 2
  change G.Adj (P.vertex 6) z at he
  change G.Adj a z at haz
  have hnot (i : ℕ) (hi : i ≤ 8) (hi' : i ≠ 0) (hi'' : i ≠ 6) : ¬G.Adj (Q.vertex i) z :=
    fun h => hi'' (only i hi hi' h)
  have hdiff : P.vertex 5 ≠ z := by
    intro e
    have := (ha 5 (by decide)).1 (e ▸ haz.symm)
    norm_num at this
  obtain ⟨z',he',hc',only'⟩ := saturated_witness R c h4 (by decide) hd6 (sat R) 2
  have hz' : z = z' := by
    by_contra hne
    obtain ⟨j,hj⟩ := blocker R c (by decide) he (sat R z)
    fin_cases j
    · change G.Adj b z at hj
      have hbne : P.vertex 6 ≠ b := by
        intro e
        have := hx.2.2 6 (by decide) (by decide) (e ▸ hxb)
        contradiction
      exact hdiff (h4 hbne ((P.edges (by decide) (by decide)).2 (Or.inr rfl))
        ((hb 5 (by decide)).2 rfl).symm he hj)
    · exact hnot 4 (by decide) (by decide) (by decide) hj
    · exact hne (unique_at_site R h4 2 he hj he' hc')
    · exact hnot 8 (by decide) (by decide) (by decide) hj
  have h3 : P.vertex 3 ≠ z := by
    intro h
    rw [← h] at he
    have := (P.edges (by decide) (by decide)).1 he
    omega
  have heq := h4 h3 ((ha 3 (by decide)).2 rfl) haz.symm ((ha' 3 (by decide)).2 rfl)
    (show G.Adj z a' from hz' ▸ hc'.symm)
  have h0 : P.vertex 0 ≠ a := by
    intro h
    have he := (ha 3 (by decide)).2 rfl
    rw [← h] at he
    have := (P.edges (by decide) (by decide)).1 he
    omega
  exact hxy (h4 h0 hx.1 hxa.symm hy.1 (heq ▸ hya.symm))

end Wall133
