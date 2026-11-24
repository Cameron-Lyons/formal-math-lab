import Wall133.GirthSixSharp

/-! # Extending both ends at girth six

Build the longer induced tail first. When the other end grows by j edges,
every contact lies either among its first 2j+2 indices or beyond index
2D−2, where D is the length of the original geodesic. -/

namespace Wall133
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V} [DecidableEq V] [DecidableRel G.Adj]

private theorem first_tail (hg : 6 ≤ G.egirth) (hc : G.Connected)
    (S : Finset V) {d : ℕ} (hd : 5 ≤ d) (hmin : ∀ z : S,d ≤ (G.induce (S : Set V)).degree z)
    {w a : V} (q : G.Walk w a) (hq : q.length=G.dist w a) (hl : 5 ≤ q.length)
    {s : ℕ} (P₀ : Chain G (q.length+s)) (hs : P₀.vertex 0∈S)
    (suf : ∀ i ≤ q.length,P₀.vertex (s+i)=q.getVert i) {t : ℕ}
    (hst : s ≤ t) (ht : t ≤ 2*d-5) :
    ∃ P : Chain G (q.length+t), P.vertex 0∈S ∧ ∀ i ≤ q.length,P.vertex (t+i)=q.getVert i := by
  induction t, hst using Nat.le_induction with
  | base => exact ⟨P₀,hs,suf⟩
  | succ j _ ih =>
    obtain ⟨P,hu,ps⟩ := ih (by omega)
    let u : S := ⟨P.vertex 0,hu⟩
    have metric : P.metricSuffix j := by
      intro i hi hin
      have eq := ps (i-j) (by omega)
      rw [Nat.add_sub_of_le hi] at eq
      have last : P.vertex (q.length+j)=a := by
        exact (congrArg P.vertex (Nat.add_comm q.length j)).trans ((ps _ le_rfl).trans q.getVert_length)
      have hh := dist_getVert_eq_sub_of_le_of_length_eq_dist q hq (i:=i-j) (j:=q.length)
        (by omega) le_rfl
      rw [Walk.getVert_length] at hh
      rw [eq,last,hh]; omega
    obtain ⟨z,hz,g⟩ := girth_six_grow_metric_suffix hg hc P S u rfl (by omega) metric
      (by have := hmin u; omega)
    refine ⟨grow P z g,hz,fun i hi => ?_⟩
    rw [show j+1+i=(j+i)+1 by omega]
    exact ps i hi

private theorem other_tail (hg : 6 ≤ G.egirth) (hc : G.Connected)
    (S : Finset V) {d : ℕ} (hd : 5 ≤ d) (hmin : ∀ z : S,d ≤ (G.induce (S : Set V)).degree z)
    {w a : V} (q : G.Walk w a) (hq : q.length=G.dist w a) (hl : 5 ≤ q.length) (ha : a∈S)
    (tail : ∃ P : Chain G (q.length+(2*d-5)), P.vertex 0∈S ∧
      ∀ i ≤ q.length,P.vertex ((2*d-5)+i)=q.getVert i)
    {j : ℕ} (hj : j ≤ d-1) (hfar : 3*j ≤ q.length+1) :
    ∃ P : Chain G (q.length+(2*d-5)+j), P.vertex 0∈S ∧
      ∀ i ≤ q.length,P.vertex (j+i)=q.getVert (q.length-i) := by
  induction j with
  | zero =>
    obtain ⟨P,_,hp⟩ := tail
    refine ⟨P.reverse,?_,fun i hi => ?_⟩
    · change P.vertex (q.length+(2*d-5)-0)∈S
      have eq := (congrArg P.vertex (Nat.add_comm q.length (2*d-5))).trans ((hp _ le_rfl).trans q.getVert_length)
      simpa only [Nat.sub_zero,eq] using ha
    · change P.vertex (q.length+(2*d-5)-(0+i))=_
      rw [show q.length+(2*d-5)-(0+i)=(2*d-5)+(q.length-i) by omega]
      exact hp _ (Nat.sub_le _ _)
  | succ j ih =>
    obtain ⟨P,hu,ps⟩ := ih (by omega) (by omega)
    let u : S := ⟨P.vertex 0,hu⟩
    have left : P.vertex j=a := by simpa using ps 0 (Nat.zero_le _)
    have right : P.vertex (j+q.length)=w := by simpa using ps _ le_rfl
    have near := P.dist_le_sub hc (i:=0) (j:=j) (by omega) (by omega)
    rw [left,Nat.sub_zero,G.dist_comm] at near
    have ranges (i) (hi : i ≤ q.length+(2*d-5)+j) (hdist : G.dist (P.vertex 0) (P.vertex i) ≤ 2) :
        i ≤ 2*j+2 ∨ 2*q.length-2 ≤ i := by
      have tr := hc.dist_triangle (u:=a) (v:=P.vertex 0) (w:=P.vertex i)
      by_cases e : i ≤ j+q.length
      · left
        by_cases ij : j ≤ i
        · have eq := ps (i-j) (by omega)
          rw [Nat.add_sub_of_le ij] at eq
          have hh := dist_getVert_eq_sub_of_le_of_length_eq_dist q hq (i:=q.length-(i-j))
            (j:=q.length) (Nat.sub_le _ _) le_rfl
          rw [Walk.getVert_length,←eq,G.dist_comm] at hh
          omega
        · omega
      · right
        have far := P.dist_le_sub hc (i:=j+q.length) (j:=i) (by omega) hi
        rw [right,G.dist_comm] at far
        have tri := hc.dist_triangle (u:=a) (v:=P.vertex i) (w:=w)
        rw [G.dist_comm (u:=a) (v:=w),←hq] at tri
        omega
    obtain ⟨z,hz,g⟩ := girth_six_grow_two_intervals hg hc P S u rfl (by omega) ranges
      (by have := hmin u; omega)
    refine ⟨grow P z g,hz,fun i hi => ?_⟩
    rw [show j+1+i=(j+i)+1 by omega]
    exact ps i hi

variable [Fintype V]

/-- Geodesic growth may start after at most 2d−5 steps have returned
from the first endpoint into the core. The original other endpoint lies
in the core. -/
theorem girth_six_path_of_core_return (hg : 6 ≤ G.egirth) (hc : G.Connected)
    (S : Finset V) {d : ℕ} (hd : 5 ≤ d) (hmin : ∀ z : S,d ≤ (G.induce (S : Set V)).degree z)
    {w a : V} (q : G.Walk w a) (hq : q.length=G.dist w a) (hl : 5 ≤ q.length) (ha : a∈S)
    {s : ℕ} (P₀ : Chain G (q.length+s)) (hin : P₀.vertex 0∈S)
    (suf : ∀ i ≤ q.length,P₀.vertex (s+i)=q.getVert i) (hs : s ≤ 2*d-5)
    {j : ℕ} (hj : j ≤ d-1) (hfar : 3*j ≤ q.length+1) :
    q.length+2*d+j ≤ G.path+4 := by
  have tail := first_tail hg hc S hd hmin q hq hl P₀ hin suf hs (Nat.le_refl _)
  obtain ⟨P,_,_⟩ := other_tail hg hc S hd hmin q hq hl ha tail hj hfar
  have := P.length_le
  omega

/-- Two vertices of the same d-core at distance D furnish an induced
path on D+2d+j−4 vertices whenever j≤d−1 and 3j≤D+1. -/
theorem girth_six_distance_between_core_vertices (hg : 6 ≤ G.egirth) (hc : G.Connected)
    (S : Finset V) {d : ℕ} (hd : 5 ≤ d) (hmin : ∀ z : S,d ≤ (G.induce (S : Set V)).degree z)
    (a b : S) (hl : 5 ≤ G.dist a.val b.val) {j : ℕ} (hj : j ≤ d-1)
    (hfar : 3*j ≤ G.dist a.val b.val+1) : G.dist a.val b.val+2*d+j ≤ G.path+4 := by
  obtain ⟨q,_,hq⟩ := hc.exists_path_of_dist a.val b.val
  let P := Chain.ofGeodesic q hq
  have hin : P.vertex 0∈S := by simp [P,Chain.ofGeodesic]
  have h := girth_six_path_of_core_return hg hc S hd hmin q hq (by omega) b.property (s:=0)
    P hin (by simp [P,Chain.ofGeodesic]) (by omega) hj (by omega)
  omega

/-- A core covering the graph within distance s gives the exact odd
threshold once the radius is at least 4s+8. -/
theorem girth_six_odd_of_core_cover (hg : 6 ≤ G.egirth) (hc : G.Connected)
    (S : Finset V) (hS : S.Nonempty) {d s : ℕ} (hd : 5 ≤ d)
    (hmin : ∀ z : S,d ≤ (G.induce (S : Set V)).degree z)
    (cover : ∀ v,∃ b : S,G.dist v b.val ≤ s) (hr : 4*s+8 ≤ G.radius.toNat) :
    G.radius.toNat+2*d-1 ≤ G.path := by
  have : Nonempty V := hc.nonempty
  by_cases full : 2*d-1 < G.radius.toNat
  · have := chung_bound_nat G hc; omega
  obtain ⟨a,ha⟩ := hS
  obtain ⟨v,q,hq,hv⟩ := exists_geodesic_ge_radius G hc a
  obtain ⟨b,hb⟩ := cover v
  have tri := hc.dist_triangle (u:=a) (v:=b.val) (w:=v)
  rw [G.dist_comm (u:=b.val) (v:=v)] at tri
  have h := girth_six_distance_between_core_vertices hg hc S hd hmin ⟨a,ha⟩ b (by
    change 5 ≤ G.dist a b.val; omega) (j:=s+3) (by omega) (by change _ ≤ G.dist a b.val+1; omega)
  change G.dist a b.val+2*d+(s+3) ≤ G.path+4 at h
  omega

end Wall133
