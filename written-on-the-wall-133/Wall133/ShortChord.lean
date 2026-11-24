import Wall133.OddRadiusFive

namespace Wall133
open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

set_option maxHeartbeats 1800000 in
/-- Replace a four-edge section using a shared contact and two private
contacts. Reversing two of the old edges gives a net gain of two edges. -/
theorem short_chord_detour (P : Chain G 14) (c : G.Coloring (Fin 2)) {t : ℕ}
    (ht : 2 ≤ t) (hu : t+4 ≤ 14) {z a b g : V}
    (hz : Off P z (fun _ => False)) (ha : Off P a (·=t-2))
    (hb : Off P b (·=t+2)) (hg : Off P g (fun i => i=t ∨ i=t+4))
    (hza : G.Adj z a) (hzb : G.Adj z b) (hzg : ¬G.Adj z g) :
    ∃ Q : Chain G 16, Q.vertex 0=P.vertex 0 := by
  let f (i : ℕ) := if i ≤ t-2 then P.vertex i else if i=t-1 then a else if i=t then z
    else if i=t+1 then b else if i=t+2 then P.vertex (t+2) else if i=t+3 then P.vertex (t+1)
    else if i=t+4 then P.vertex t else if i=t+5 then g else P.vertex (i-2)
  have hab : c a=c b := color_common c hza.symm hzb.symm
  have hag : c a=c g := by
    apply Fin.ext
    have h₁ := Fin.val_ne_of_ne (c.valid ((ha.contact (t-2) (by omega)).2 rfl))
    have h₂ := Fin.val_ne_of_ne (c.valid ((hg.contact t (by omega)).2 (Or.inl rfl)))
    have := P.color_val c (t-2) (by omega)
    have := P.color_val c t (by omega)
    have := (c a).isLt; have := (c g).isLt
    omega
  have hc₁ : ¬G.Adj a b := fun h => c.valid h hab
  have hc₂ : ¬G.Adj a g := fun h => c.valid h hag
  have hc₃ : ¬G.Adj b g := fun h => c.valid h (hab.symm.trans hag)
  have back {s : ℕ → Prop} {v : V} (hv : Off P v s) (i : ℕ) (hi : i≤14) :
      G.Adj (P.vertex i) v ↔ s i := (G.adj_comm _ _).trans (hv.contact i hi)
  have edges {i j : ℕ} (hi : i≤16) (hj : j≤16) :
      G.Adj (f i) (f j) ↔ i+1=j ∨ j+1=i := by
    dsimp [f]; split_ifs
    all_goals first
      | rw [P.edges (by omega) (by omega)] <;> omega
      | rw [ha.contact _ (by omega)]; omega
      | rw [hb.contact _ (by omega)]; omega
      | rw [hz.contact _ (by omega)] <;> simp only [false_iff] <;> omega
      | rw [hg.contact _ (by omega)]; omega
      | rw [back ha _ (by omega)]; omega
      | rw [back hb _ (by omega)]; omega
      | rw [back hz _ (by omega)] <;> simp only [false_iff] <;> omega
      | rw [back hg _ (by omega)]; omega
      | simp only [SimpleGraph.irrefl,hza,hza.symm,hzb,hzb.symm,hzg,mt Adj.symm hzg,
          hc₁,mt Adj.symm hc₁,hc₂,mt Adj.symm hc₂,hc₃,mt Adj.symm hc₃,true_iff,false_iff]; omega

  have inj {i j : ℕ} (hi : i≤16) (hj : j≤16) (h : f i=f j) : i=j := by
    have twins : ∀ a b : Fin 17, (∀ k : Fin 17,
        (a.val+1=k.val ∨ k.val+1=a.val) ↔ (b.val+1=k.val ∨ k.val+1=b.val)) → a=b := by decide
    apply congrArg Fin.val (twins ⟨i,by omega⟩ ⟨j,by omega⟩ ?_)
    intro k
    have hk : k.val ≤ 16 := by omega
    exact (edges hi hk).symm.trans ((congrArg (fun v => G.Adj v (f k.val)) h).to_iff.trans (edges hj hk))
  exact ⟨⟨f,inj,edges⟩,by simp [f]⟩

end Wall133
