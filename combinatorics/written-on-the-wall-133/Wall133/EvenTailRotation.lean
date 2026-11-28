module

public import Wall133.GeodesicRotation

@[expose] public section

namespace Wall133
open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {n : ℕ}

/-- At the tight even tail length, three saturated geodesic slots occupy
an interval of width four and lie between t and t+6. One is t+2.
Rotating at its private contact returns the active endpoint to the anchor. -/
theorem rotate_even_geodesic_tail (P : Chain G n) (hc : G.Connected) (c : G.Coloring (Fin 2))
    (h4 : NoFourCycle G) (S : Finset V) (a : S) {v : V} (q : G.Walk a.val v)
    (hq : q.length=G.dist a.val v) (hl : 5 ≤ q.length)
    {d t : ℕ} (hd : 4 ≤ d) (ht : t=2*d-4) (hL : n=t+q.length)
    (hsuf : ∀ j ≤ q.length, P.vertex (t+j)=q.getVert j)
    (allCore : ∀ i ≤ t, P.vertex i∈S) (hsMetric : P.metricSuffix t)
    (N : Finset V) (hN : ∀ w ∈ N,G.Adj (P.vertex 0) w) (hin : ∀w∈N,w∈S)
    (hsat : ∀w∈N,¬Good P w) (hdN : d ≤ N.card) :
    ∃ R : Chain G n, R.vertex 0=a.val ∧
      (∀ j, 2 ≤ j → j ≤ q.length → R.vertex (t+j)=q.getVert j) ∧
      (∀ i, i < t+2 → R.vertex i ∈ S) ∧ ∀ i, R.Blocks i → i ≤ t+2 := by
  have anchor : P.vertex t = a.val := by simpa using hsuf 0 (Nat.zero_le _)
  obtain ⟨w,hw,hadj⟩ := previous_site P hc c h4 (by omega) (by omega) hsMetric N hN hsat (by omega)
  rw [show 2*((t-1)/2)=t-2 by omega] at hadj
  have hnear : G.dist a.val (P.vertex 0) ≤ 4 := by
    have h₁ := hc.dist_triangle (u := P.vertex (t-2)) (v := w) (w := P.vertex 0)
    rw [dist_eq_one_iff_adj.mpr hadj,dist_eq_one_iff_adj.mpr (hN _ hw).symm] at h₁
    have h₂ := P.dist_le_sub hc (i := t-2) (j := t) (by omega) (by omega)
    rw [G.dist_comm,anchor] at h₂
    have h₃ := hc.dist_triangle (u := a.val) (v := P.vertex (t-2)) (w := P.vertex 0)
    omega
  let base := n-(G.dist (P.vertex 0) (P.vertex n)+2)
  let delta := (t-1)/2
  have window (i) (hi : P.Blocks i) (hs : t ≤ i) : base ≤ i ∧ i ≤ base+4 := by
    have h₁ := hc.dist_triangle (u := P.vertex 0) (v := P.vertex i) (w := P.vertex n)
    have h₂ := hc.dist_triangle (u := P.vertex i) (v := P.vertex 0) (w := P.vertex n)
    rw [G.dist_comm (u := P.vertex i) (v := P.vertex 0)] at h₂
    rw [hsMetric _ hs hi.1] at h₁ h₂
    have := hi.2.2.2
    have := hi.1
    dsimp [base]; omega
  let Witness (i : ℕ) := ∃ z ∈ N, G.Adj (P.vertex i) z ∧
    ∀ j ≤ n, j ≠ 0 → G.Adj (P.vertex j) z → j=i
  have code := P.suffixCode hc hsMetric
  have get (r : Fin 3) : ∃ i, t ≤ i ∧ i ≤ t+6 ∧ base ≤ i ∧ i ≤ base+4 ∧ i%2=0 ∧
      (i-base)/2=r.val ∧ Witness i := by
    let slot : Fin (delta+3) := ⟨delta+r.val,by have := r.isLt; omega⟩
    obtain ⟨z,hz,i,hi,hcode,hadj,priv⟩ := P.private_of_code hc c h4 (by omega) N hN hsat _
      (show delta+3 ≤ N.card by dsimp [delta]; omega) code.1 code.2 slot
    change (if i<t then i/2-1 else delta+(i-base)/2) = delta+r.val at hcode
    have hti : t ≤ i := by
      by_contra! small
      rw [ite_eq_left small] at hcode
      have := hi.2.1; have := hi.2.2.1
      dsimp [delta] at hcode
      omega
    rw [ite_eq_right (by omega)] at hcode
    obtain ⟨hlo,hhi⟩ := window i hi hti
    refine ⟨i,hti,?_,hlo,hhi,hi.2.2.1,by omega,z,hz,hadj,priv⟩
    exact P.block_limit hc q hq t 0 4 hL (fun j _ hj => hsuf j hj) (by decide) hnear hi
  obtain ⟨i₀,hl₀,hh₀,hb₀,hm₀,he₀,hs₀,hw₀⟩ := get 0
  obtain ⟨i₁,hl₁,hh₁,hb₁,hm₁,he₁,hs₁,hw₁⟩ := get 1
  obtain ⟨i₂,hl₂,hh₂,hb₂,hm₂,he₂,hs₂,hw₂⟩ := get 2
  change (i₀-base)/2=0 at hs₀
  change (i₁-base)/2=1 at hs₁
  change (i₂-base)/2=2 at hs₂
  have atTwo : Witness (t+2) := by
    have which : i₀=t+2 ∨ i₁=t+2 ∨ i₂=t+2 := by omega
    rcases which with h|h|h
    · exact h ▸ hw₀
    · exact h ▸ hw₁
    · exact h ▸ hw₂
  obtain ⟨z,hz,hiz,hpriv⟩ := atTwo
  let R := P.rotateAt (t+2) (by omega) (by omega) (hN z hz) hiz hpriv
  have hr : R.vertex 0 = a.val := by
    simpa [R,Chain.rotateAt,show ¬t+2≤0 by omega,show 1≠t+2 by omega] using anchor
  have suf (j) (hj : 2 ≤ j) (hjq : j ≤ q.length) : R.vertex (t+j)=q.getVert j := by
    simpa [R,Chain.rotateAt, show t+2≤t+j by omega] using hsuf j hjq
  refine ⟨R,hr,suf,?_,fun i hi => ?_⟩
  · intro i hi
    dsimp [R,Chain.rotateAt]
    split_ifs
    · omega
    · exact hin z hz
    · exact allCore _ (by omega)
  · apply R.block_limit hc q hq t 2 0 hL suf (by decide) _ hi
    rw [hr,G.dist_self]

end Wall133
