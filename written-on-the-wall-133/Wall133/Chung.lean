/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.VertexDistance
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Diam
public import Mathlib.Tactic.Linarith

@[expose] public section

-- Adapted from KitaKen1/wowii-graph-conjecture-31-lean, commit
-- a948e9fc07e11b786aee8dadb1376b4d938454d6, to use the upstream definitions.
/-!
# WOWII Graph Conjecture 31

This file gives a complete Lean proof of the Erdős--Saks--Sós / Fan Chung
induced-path theorem: every finite connected graph contains an induced path
on at least twice its radius minus one vertices.

*Reference:* P. Erdős, M. Saks and V. T. Sós,
[*Maximum Induced Trees in Graphs*](https://real.mtak.hu/110576/1/1-s2.0-0095895686900286-main.pdf),
J. Combin. Theory Ser. B 41 (1986), Theorem 2.2.
-/

open Classical

universe u

namespace SimpleGraph

variable {α : Type u} [Fintype α] [DecidableEq α]
variable {G : SimpleGraph α} {u v : α}

omit [Fintype α] [DecidableEq α] in
/-- The support list of a shortest walk is an induced path. -/
lemma isInducedPath_support_of_length_eq_dist (p : G.Walk u v)
    (hp : p.length = G.dist u v) :
    isInducedPath G p.support := by
  have hpath : p.IsPath := p.isPath_of_length_eq_dist hp
  refine ⟨hpath.support_nodup, ?_⟩
  intro i j
  have hi : p.support.get i = p.getVert i.val := by
    exact (congrFun p.getVert_comp_val_eq_get_support i).symm
  have hj : p.support.get j = p.getVert j.val := by
    exact (congrFun p.getVert_comp_val_eq_get_support j).symm
  rw [hi, hj]
  constructor
  · intro hadj
    have hne : i.val ≠ j.val := by
      intro hij
      exact hadj.ne (congrArg p.getVert hij)
    rcases Nat.lt_or_gt_of_ne hne with hij | hji
    · let q₀ := (p.drop i.val).take (j.val - i.val)
      have hjle : j.val ≤ p.length := by
        have hjlt : j.val < p.support.length := j.isLt
        have hlen : p.support.length = p.length + 1 := Walk.length_support p
        omega
      have hqend : (p.drop i.val).getVert (j.val - i.val) = p.getVert j.val := by
        simp [Nat.add_sub_of_le hij.le]
      have hsub : q₀.IsSubwalk p :=
        (Walk.isSubwalk_take (p.drop i.val) (j.val - i.val)).trans
          (Walk.isSubwalk_drop p i.val)
      have hqlen : q₀.length = j.val - i.val := by
        simp only [q₀, Walk.take_length, Walk.drop_length]
        omega
      have hshort := length_eq_dist_of_subwalk hp hsub
      have hadjdist : G.dist (p.getVert i.val) (p.getVert j.val) = 1 :=
        dist_eq_one_iff_adj.mpr hadj
      rw [hqlen, hqend, hadjdist] at hshort
      exact Or.inl (by omega)
    · let q₀ := (p.drop j.val).take (i.val - j.val)
      have hile : i.val ≤ p.length := by
        have hilt : i.val < p.support.length := i.isLt
        have hlen : p.support.length = p.length + 1 := Walk.length_support p
        omega
      have hqend : (p.drop j.val).getVert (i.val - j.val) = p.getVert i.val := by
        simp [Nat.add_sub_of_le hji.le]
      have hsub : q₀.IsSubwalk p :=
        (Walk.isSubwalk_take (p.drop j.val) (i.val - j.val)).trans
          (Walk.isSubwalk_drop p j.val)
      have hqlen : q₀.length = i.val - j.val := by
        simp only [q₀, Walk.take_length, Walk.drop_length]
        omega
      have hshort := length_eq_dist_of_subwalk hp hsub
      have hadjdist : G.dist (p.getVert j.val) (p.getVert i.val) = 1 :=
        dist_eq_one_iff_adj.mpr hadj.symm
      rw [hqlen, hqend, hadjdist] at hshort
      exact Or.inr (by omega)
  · rintro (hij | hji)
    · rw [← hij]
      exact p.adj_getVert_succ (i := i.val) (by
        have hjlt : j.val < p.support.length := j.isLt
        have hlen : p.support.length = p.length + 1 := Walk.length_support p
        omega)
    · rw [← hji]
      exact (p.adj_getVert_succ (i := j.val) (by
        have hilt : i.val < p.support.length := i.isLt
        have hlen : p.support.length = p.length + 1 := Walk.length_support p
        omega)).symm

omit [Fintype α] [DecidableEq α] in
/-- Along a geodesic, the distance between ordered indexed vertices is the
difference of their indices. -/
lemma dist_getVert_eq_sub_of_le_of_length_eq_dist
    (p : G.Walk u v) (hp : p.length = G.dist u v)
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ p.length) :
    G.dist (p.getVert i) (p.getVert j) = j - i := by
  let q := (p.drop i).take (j - i)
  have hqend : (p.drop i).getVert (j - i) = p.getVert j := by
    simp [Nat.add_sub_of_le hij]
  have hsub : q.IsSubwalk p :=
    (Walk.isSubwalk_take (p.drop i) (j - i)).trans
      (Walk.isSubwalk_drop p i)
  have hqlen : q.length = j - i := by
    simp only [q, Walk.take_length, Walk.drop_length]
    omega
  have hshort := length_eq_dist_of_subwalk hp hsub
  rw [hqlen, hqend] at hshort
  exact hshort.symm

omit [Fintype α] [DecidableEq α] in
/-- Two indexed vertices of a geodesic are adjacent exactly when their
indices are consecutive. -/
lemma adj_getVert_iff_consecutive_of_length_eq_dist
    (p : G.Walk u v) (hp : p.length = G.dist u v)
    {i j : ℕ} (hi : i ≤ p.length) (hj : j ≤ p.length) :
    G.Adj (p.getVert i) (p.getVert j) ↔
      i + 1 = j ∨ j + 1 = i := by
  constructor
  · intro hadj
    have hne : i ≠ j := by
      intro hij
      subst j
      exact hadj.ne rfl
    rcases Nat.lt_or_gt_of_ne hne with hij | hji
    · have hd := dist_getVert_eq_sub_of_le_of_length_eq_dist p hp hij.le hj
      have hone := dist_eq_one_iff_adj.mpr hadj
      rw [hone] at hd
      exact Or.inl (by omega)
    · have hd := dist_getVert_eq_sub_of_le_of_length_eq_dist p hp hji.le hi
      have hone := dist_eq_one_iff_adj.mpr hadj.symm
      rw [hone] at hd
      exact Or.inr (by omega)
  · rintro (hij | hji)
    · rw [← hij]
      exact p.adj_getVert_succ (by omega)
    · rw [← hji]
      exact (p.adj_getVert_succ (by omega)).symm

omit [Fintype α] [DecidableEq α] in
/-- A path with no nonconsecutive adjacent indexed vertices has induced
support. -/
lemma isInducedPath_support_of_isPath_of_adj_getVert
    (p : G.Walk u v) (hp : p.IsPath)
    (hchord :
      ∀ i j : ℕ, i ≤ p.length → j ≤ p.length →
        G.Adj (p.getVert i) (p.getVert j) →
          i + 1 = j ∨ j + 1 = i) :
    isInducedPath G p.support := by
  constructor
  · exact hp.support_nodup
  · intro i j
    have hi : i.val ≤ p.length := by
      have := i.isLt
      have hlen : p.support.length = p.length + 1 := Walk.length_support p
      omega
    have hj : j.val ≤ p.length := by
      have := j.isLt
      have hlen : p.support.length = p.length + 1 := Walk.length_support p
      omega
    have hgeti : p.support.get i = p.getVert i.val :=
      (congrFun p.getVert_comp_val_eq_get_support i).symm
    have hgetj : p.support.get j = p.getVert j.val :=
      (congrFun p.getVert_comp_val_eq_get_support j).symm
    rw [hgeti, hgetj]
    constructor
    · exact hchord i.val j.val hi hj
    · rintro (hij | hji)
      · rw [← hij]
        exact p.adj_getVert_succ (by omega)
      · rw [← hji]
        exact (p.adj_getVert_succ (by omega)).symm

omit [Fintype α] [DecidableEq α] in
/-- Injectivity of indexed vertices up to the walk length proves that the
walk is a path. -/
lemma isPath_of_injective_getVert_le
    (p : G.Walk u v)
    (hinj :
      ∀ i j : ℕ, i ≤ p.length → j ≤ p.length →
        p.getVert i = p.getVert j → i = j) :
    p.IsPath := by
  rw [Walk.isPath_iff_injective_get_support]
  intro i j hij
  have hi : i.val ≤ p.length := by
    have hil := i.isLt
    have hlen : p.support.length = p.length + 1 := Walk.length_support p
    omega
  have hj : j.val ≤ p.length := by
    have hjl := j.isLt
    have hlen : p.support.length = p.length + 1 := Walk.length_support p
    omega
  apply Fin.ext
  apply hinj i.val j.val hi hj
  have hgeti : p.getVert i.val = p.support.get i :=
    congrFun p.getVert_comp_val_eq_get_support i
  have hgetj : p.getVert j.val = p.support.get j :=
    congrFun p.getVert_comp_val_eq_get_support j
  rw [hgeti, hgetj]
  exact hij

/-- Every witnessed induced path has at most `path G` vertices. -/
lemma length_le_path_of_isInducedPath' (l : List α) (hl : isInducedPath G l) :
    l.length ≤ path G := by
  let paths := Finset.univ.filter (fun s : Finset α =>
    ∃ l : List α, l.toFinset = s ∧ isInducedPath G l)
  let cards := paths.image Finset.card
  have hs : l.toFinset ∈ paths := by
    simp only [paths, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨l, rfl, hl⟩
  have hc : l.toFinset.card ∈ cards :=
    Finset.mem_image.mpr ⟨l.toFinset, hs, rfl⟩
  have hne : cards.Nonempty := ⟨l.toFinset.card, hc⟩
  have hle : l.toFinset.card ≤ cards.max' hne := Finset.le_max' cards _ hc
  rw [List.toFinset_card_of_nodup hl.1] at hle
  change l.length ≤ cards.max.getD 0
  rw [← Finset.coe_max' hne]
  exact hle

omit [Fintype α] [DecidableEq α] in
/-- An induced path in `G.induce s` remains induced in `G`. -/
lemma isInducedPath_map_val_of_induce (s : Set α) (l : List s)
    (hl : isInducedPath (G.induce s) l) :
    isInducedPath G (l.map (fun v => v.1)) := by
  constructor
  · exact hl.1.map Subtype.val_injective
  · intro i j
    let i' : Fin l.length := ⟨i.val, by simpa using i.isLt⟩
    let j' : Fin l.length := ⟨j.val, by simpa using j.isLt⟩
    simpa [i', j'] using hl.2 i' j'

/-- The maximum induced-path size is monotone under induced subgraphs. -/
lemma path_induce_le (s : Set α) [Fintype s] [DecidableEq s] :
    path (G.induce s) ≤ path G := by
  let paths := Finset.univ.filter (fun t : Finset s =>
    ∃ l : List s, l.toFinset = t ∧ isInducedPath (G.induce s) l)
  let cards := paths.image Finset.card
  change cards.max.getD 0 ≤ path G
  by_cases hcards : cards.Nonempty
  · rw [← Finset.coe_max' hcards]
    change cards.max' hcards ≤ path G
    rw [Finset.max'_le_iff]
    intro n hn
    rcases Finset.mem_image.mp hn with ⟨t, ht, rfl⟩
    rw [Finset.mem_filter] at ht
    rcases ht.2 with ⟨l, rfl, hl⟩
    rw [List.toFinset_card_of_nodup hl.1]
    have hlift := isInducedPath_map_val_of_induce s l hl
    simpa using length_le_path_of_isInducedPath' (l.map (fun v => v.1)) hlift
  · have hempty : cards = ∅ := Finset.not_nonempty_iff_eq_empty.mp hcards
    rw [hempty]
    exact Nat.zero_le _

omit [Fintype α] [DecidableEq α] in
/-- Distances can only increase when vertices outside `s` are forbidden. -/
lemma dist_val_le_dist_induce (s : Set α) (hconn : (G.induce s).Connected)
    (u v : s) :
    G.dist u.1 v.1 ≤ (G.induce s).dist u v := by
  obtain ⟨p, -, hp⟩ := hconn.exists_path_of_dist u v
  calc
    G.dist u.1 v.1 ≤ (p.map (Embedding.induce s).toHom).length := dist_le _
    _ = p.length := p.length_map (Embedding.induce s).toHom
    _ = (G.induce s).dist u v := hp

/-- A radius-preserving proper induced subgraph closes the induction step. -/
lemma chung_bound_of_induce_radius_ge
    (s : Set α) [Fintype s] [DecidableEq s]
    (hind : 2 * ((G.induce s).radius.toNat : ℤ) - 1
      ≤ (path (G.induce s) : ℤ))
    (hradius : G.radius.toNat ≤ (G.induce s).radius.toNat) :
    2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ) := by
  have hpath : (path (G.induce s) : ℤ) ≤ (path G : ℤ) := by
    exact_mod_cast path_induce_le (G := G) s
  have hradius' :
      (G.radius.toNat : ℤ) ≤ ((G.induce s).radius.toNat : ℤ) := by
    exact_mod_cast hradius
  linarith

/-- A nonempty finite graph has an induced path with one vertex. -/
lemma one_le_path [Nonempty α] : 1 ≤ path G := by
  let x : α := Classical.ofNonempty
  have hx : isInducedPath G [x] := by
    simp [isInducedPath]
  simpa using length_le_path_of_isInducedPath' (G := G) [x] hx

omit [DecidableEq α] in
/-- Distances from a center of a finite connected graph are bounded by its
natural-valued radius. -/
lemma dist_le_radius_toNat_of_eccent_eq_radius
    (hconn : G.Connected) {c : α} (hc : G.eccent c = G.radius) (x : α) :
    G.dist c x ≤ G.radius.toNat := by
  let : Nonempty α := hconn.nonempty
  change (G.edist c x).toNat ≤ G.radius.toNat
  apply ENat.toNat_le_toNat
  · rw [← hc]
    exact G.edist_le_eccent
  · exact G.radius_ne_top_iff.mpr hconn

/-- Deleting a suitable vertex preserves connectedness and strictly lowers
the cardinality of the vertex type. -/
lemma exists_connected_deletion_with_card_lt [Nontrivial α]
    (hconn : G.Connected) :
    ∃ vr : α, (G.induce {vr}ᶜ).Connected ∧
      Fintype.card {x : α // x ∈ ({vr}ᶜ : Set α)} < Fintype.card α := by
  obtain ⟨vr, hdel⟩ :=
    hconn.exists_connected_induce_compl_singleton_of_finite_nontrivial
  refine ⟨vr, hdel, ?_⟩
  change Fintype.card {x : α // ¬x = vr} < Fintype.card α
  rw [Fintype.card_subtype_compl]
  simp
  exact Fintype.card_pos

/--
If deleting `vr` lowers the radius and `v0` is a center of the deletion
graph, then `v0` is exactly `radius G` away from `vr` in the ambient graph.
-/
lemma dist_center_deleted_eq_radius [Nontrivial α]
    (hconn : G.Connected) (vr : α)
    (hdel : (G.induce {vr}ᶜ).Connected)
    (hradius : (G.induce {vr}ᶜ).radius.toNat < G.radius.toNat)
    (v0 : {x : α // x ∈ ({vr}ᶜ : Set α)})
    (hv0 : (G.induce {vr}ᶜ).eccent v0 = (G.induce {vr}ᶜ).radius) :
    G.dist v0.1 vr = G.radius.toNat := by
  let H := G.induce ({vr}ᶜ : Set α)
  have hradiusH : H.radius.toNat < G.radius.toNat := by
    simpa only [H] using hradius
  have hbound (x : {x : α // x ∈ ({vr}ᶜ : Set α)}) :
      G.dist v0.1 x.1 ≤ H.radius.toNat := by
    calc
      G.dist v0.1 x.1 ≤ H.dist v0 x :=
        dist_val_le_dist_induce (G := G) {vr}ᶜ hdel v0 x
      _ ≤ H.radius.toNat :=
        dist_le_radius_toNat_of_eccent_eq_radius hdel hv0 x
  obtain ⟨y, hry⟩ := hconn.preconnected.exists_adj_of_nontrivial vr
  have hyne : y ≠ vr := hry.ne.symm
  let ys : {x : α // x ∈ ({vr}ᶜ : Set α)} :=
    ⟨y, by simp [hyne]⟩
  have hybound : G.dist v0.1 y ≤ H.radius.toNat := by
    simpa only [ys] using hbound ys
  have hupp : G.dist v0.1 vr ≤ G.radius.toNat := by
    calc
      G.dist v0.1 vr ≤ G.dist v0.1 y + G.dist y vr :=
        hconn.dist_triangle
      _ = G.dist v0.1 y + 1 := by
        rw [dist_eq_one_iff_adj.mpr hry.symm]
      _ ≤ H.radius.toNat + 1 := Nat.add_le_add_right hybound 1
      _ ≤ G.radius.toNat := hradiusH
  obtain ⟨z, hz⟩ := G.exists_edist_eq_eccent_of_finite v0.1
  have hrad_le_edist : G.radius ≤ G.edist v0.1 z := by
    rw [hz]
    exact G.radius_le_eccent
  have hlow_far : G.radius.toNat ≤ G.dist v0.1 z := by
    change G.radius.toNat ≤ (G.edist v0.1 z).toNat
    exact ENat.toNat_le_toNat hrad_le_edist
      (edist_ne_top_iff_reachable.mpr (hconn v0.1 z))
  have hz : z = vr := by
    by_contra hzvr
    let zs : {x : α // x ∈ ({vr}ᶜ : Set α)} :=
      ⟨z, by simp [hzvr]⟩
    have hzbound : G.dist v0.1 z ≤ H.radius.toNat := by
      simpa only [zs] using hbound zs
    omega
  subst z
  omega

/--
The metric data used in Chung's proof: a center `v0` of the vertex-deleted
graph, a geodesic from `v0` to the deleted vertex `vr`, a vertex `w` far from
the second vertex of that geodesic, and a second geodesic from `v0` to `w`.
-/
lemma exists_chung_geodesic_data [Nontrivial α]
    (hconn : G.Connected) (vr : α)
    (hdel : (G.induce {vr}ᶜ).Connected)
    (hradius : (G.induce {vr}ᶜ).radius.toNat < G.radius.toNat)
    (hrtwo : 2 ≤ G.radius.toNat) :
    ∃ (v0 : {x : α // x ∈ ({vr}ᶜ : Set α)})
      (q : G.Walk v0.1 vr) (w : α) (p : G.Walk v0.1 w),
      (G.induce {vr}ᶜ).eccent v0 = (G.induce {vr}ᶜ).radius ∧
      q.length = G.dist v0.1 vr ∧
      q.length = G.radius.toNat ∧
      p.length = G.dist v0.1 w ∧
      w ≠ vr ∧
      G.radius.toNat ≤ G.dist (q.getVert 2) w ∧
      G.radius.toNat - 2 ≤ p.length ∧
      p.length ≤ G.radius.toNat - 1 := by
  let H := G.induce ({vr}ᶜ : Set α)
  let : Nonempty {x : α // x ∈ ({vr}ᶜ : Set α)} := hdel.nonempty
  obtain ⟨v0, hv0⟩ := H.exists_eccent_eq_radius
  have hv0' :
      (G.induce {vr}ᶜ).eccent v0 = (G.induce {vr}ᶜ).radius := by
    simpa only [H] using hv0
  have hd0r : G.dist v0.1 vr = G.radius.toNat :=
    dist_center_deleted_eq_radius hconn vr hdel hradius v0 hv0'
  obtain ⟨q, -, hqdist⟩ := hconn.exists_path_of_dist v0.1 vr
  have hqrad : q.length = G.radius.toNat := hqdist.trans hd0r
  obtain ⟨w, hw⟩ := G.exists_edist_eq_eccent_of_finite (q.getVert 2)
  have hfar : G.radius.toNat ≤ G.dist (q.getVert 2) w := by
    change G.radius.toNat ≤ (G.edist (q.getVert 2) w).toNat
    apply ENat.toNat_le_toNat
    · rw [hw]
      exact G.radius_le_eccent
    · exact edist_ne_top_iff_reachable.mpr (hconn (q.getVert 2) w)
  have hv2r : G.dist (q.getVert 2) vr ≤ q.length - 2 := by
    simpa only [Walk.drop_length] using dist_le (q.drop 2)
  have hwne : w ≠ vr := by
    intro hwr
    subst w
    omega
  let ws : {x : α // x ∈ ({vr}ᶜ : Set α)} :=
    ⟨w, by simp [hwne]⟩
  have hupper0 : G.dist v0.1 w ≤ H.radius.toNat := by
    calc
      G.dist v0.1 w ≤ H.dist v0 ws :=
        dist_val_le_dist_induce (G := G) {vr}ᶜ hdel v0 ws
      _ ≤ H.radius.toNat :=
        dist_le_radius_toNat_of_eccent_eq_radius hdel hv0 ws
  have hradiusH : H.radius.toNat < G.radius.toNat := by
    simpa only [H] using hradius
  have hpupper : G.dist v0.1 w ≤ G.radius.toNat - 1 := by
    omega
  have hv0v2 : G.dist v0.1 (q.getVert 2) ≤ 2 := by
    exact (dist_le (q.take 2)).trans (by simp [Walk.take_length])
  have hv2v0 : G.dist (q.getVert 2) v0.1 ≤ 2 := by
    rw [dist_comm]
    exact hv0v2
  have htriangle :
      G.dist (q.getVert 2) w ≤
        G.dist (q.getVert 2) v0.1 + G.dist v0.1 w :=
    hconn.dist_triangle
  have hplower : G.radius.toNat - 2 ≤ G.dist v0.1 w := by
    omega
  obtain ⟨p, -, hpdist⟩ := hconn.exists_path_of_dist v0.1 w
  exact ⟨v0, q, w, p, hv0', hqdist, hqrad, hpdist, hwne, hfar,
    by omega, by omega⟩

omit [Fintype α] [DecidableEq α] in
/-- Apart from their common initial vertex, the two geodesics in Chung's
construction have disjoint supports. -/
lemma chung_geodesics_cross_ne [Nontrivial α]
    (hconn : G.Connected) {v0 vr w : α}
    (q : G.Walk v0 vr) (p : G.Walk v0 w)
    (hqdist : q.length = G.dist v0 vr)
    (hqrad : q.length = G.radius.toNat)
    (hpdist : p.length = G.dist v0 w)
    (hfar : G.radius.toNat ≤ G.dist (q.getVert 2) w)
    (hpupper : p.length ≤ G.radius.toNat - 1)
    (hrtwo : 2 ≤ G.radius.toNat)
    {j k : ℕ} (hj : j ≤ q.length)
    (hkpos : 1 ≤ k) (hk : k ≤ p.length) :
    q.getVert j ≠ p.getVert k := by
  intro heq
  have hq0j : G.dist v0 (q.getVert j) = j := by
    simpa only [Walk.getVert_zero, Nat.sub_zero] using
      dist_getVert_eq_sub_of_le_of_length_eq_dist q hqdist
        (i := 0) (j := j) (Nat.zero_le _) hj
  have hp0k : G.dist v0 (p.getVert k) = k := by
    simpa only [Walk.getVert_zero, Nat.sub_zero] using
      dist_getVert_eq_sub_of_le_of_length_eq_dist p hpdist
        (i := 0) (j := k) (Nat.zero_le _) hk
  have hjk : j = k := by
    rw [heq] at hq0j
    omega
  have hpkw : G.dist (p.getVert k) w = p.length - k := by
    simpa only [Walk.getVert_length] using
      dist_getVert_eq_sub_of_le_of_length_eq_dist p hpdist
        (i := k) (j := p.length) hk (le_refl _)
  by_cases hjone : j = 1
  · have hq12 : G.dist (q.getVert 1) (q.getVert 2) = 1 := by
      have htwo : 2 ≤ q.length := by omega
      simpa only [Nat.reduceSubDiff] using
        dist_getVert_eq_sub_of_le_of_length_eq_dist q hqdist
          (i := 1) (j := 2) (by omega) htwo
    have hq21 : G.dist (q.getVert 2) (q.getVert 1) = 1 := by
      rw [dist_comm]
      exact hq12
    have htriangle :
        G.dist (q.getVert 2) w ≤
          G.dist (q.getVert 2) (q.getVert 1) +
            G.dist (q.getVert 1) w :=
      hconn.dist_triangle
    have heq1 : q.getVert 1 = p.getVert k := by
      simpa only [hjone] using heq
    rw [hq21, heq1, hpkw] at htriangle
    omega
  · have hjtwo : 2 ≤ j := by omega
    have hq2j : G.dist (q.getVert 2) (q.getVert j) = j - 2 :=
      dist_getVert_eq_sub_of_le_of_length_eq_dist q hqdist
        (i := 2) (j := j) hjtwo hj
    have htriangle :
        G.dist (q.getVert 2) w ≤
          G.dist (q.getVert 2) (q.getVert j) +
            G.dist (q.getVert j) w :=
      hconn.dist_triangle
    rw [hq2j, heq, hpkw] at htriangle
    omega

omit [Fintype α] [DecidableEq α] in
/--
The only possible edge between the positive-index parts of Chung's two
geodesics is the boundary edge from `q[1]` to `p[1]`; if it exists, the second
geodesic has the maximal possible length `radius - 1`.
-/
lemma chung_geodesics_cross_adj_boundary [Nontrivial α]
    (hconn : G.Connected) {v0 vr w : α}
    (q : G.Walk v0 vr) (p : G.Walk v0 w)
    (hqdist : q.length = G.dist v0 vr)
    (hqrad : q.length = G.radius.toNat)
    (hpdist : p.length = G.dist v0 w)
    (hfar : G.radius.toNat ≤ G.dist (q.getVert 2) w)
    (hpupper : p.length ≤ G.radius.toNat - 1)
    (hrtwo : 2 ≤ G.radius.toNat)
    {j k : ℕ} (hjpos : 1 ≤ j) (hj : j ≤ q.length)
    (hkpos : 1 ≤ k) (hk : k ≤ p.length)
    (hadj : G.Adj (q.getVert j) (p.getVert k)) :
    j = 1 ∧ k = 1 ∧ p.length = G.radius.toNat - 1 := by
  have hq0j : G.dist v0 (q.getVert j) = j := by
    simpa only [Walk.getVert_zero, Nat.sub_zero] using
      dist_getVert_eq_sub_of_le_of_length_eq_dist q hqdist
        (i := 0) (j := j) (Nat.zero_le _) hj
  have hp0k : G.dist v0 (p.getVert k) = k := by
    simpa only [Walk.getVert_zero, Nat.sub_zero] using
      dist_getVert_eq_sub_of_le_of_length_eq_dist p hpdist
        (i := 0) (j := k) (Nat.zero_le _) hk
  have hpkw : G.dist (p.getVert k) w = p.length - k := by
    simpa only [Walk.getVert_length] using
      dist_getVert_eq_sub_of_le_of_length_eq_dist p hpdist
        (i := k) (j := p.length) hk (le_refl _)
  have hqp : G.dist (q.getVert j) (p.getVert k) = 1 :=
    dist_eq_one_iff_adj.mpr hadj
  have hpq : G.dist (p.getVert k) (q.getVert j) = 1 := by
    rw [dist_comm]
    exact hqp
  have hjle : j ≤ k + 1 := by
    have htriangle :
        G.dist v0 (q.getVert j) ≤
          G.dist v0 (p.getVert k) +
            G.dist (p.getVert k) (q.getVert j) :=
      hconn.dist_triangle
    rw [hq0j, hp0k, hpq] at htriangle
    exact htriangle
  by_cases hjone : j = 1
  · have hq12 : G.dist (q.getVert 1) (q.getVert 2) = 1 := by
      have htwo : 2 ≤ q.length := by omega
      simpa only [Nat.reduceSubDiff] using
        dist_getVert_eq_sub_of_le_of_length_eq_dist q hqdist
          (i := 1) (j := 2) (by omega) htwo
    have hq21 : G.dist (q.getVert 2) (q.getVert 1) = 1 := by
      rw [dist_comm]
      exact hq12
    have htri1 :
        G.dist (q.getVert 2) w ≤
          G.dist (q.getVert 2) (q.getVert 1) +
            G.dist (q.getVert 1) w :=
      hconn.dist_triangle
    have hadj1 : G.Adj (q.getVert 1) (p.getVert k) := by
      simpa only [hjone] using hadj
    have h1p : G.dist (q.getVert 1) (p.getVert k) = 1 :=
      dist_eq_one_iff_adj.mpr hadj1
    have htri2 :
        G.dist (q.getVert 1) w ≤
          G.dist (q.getVert 1) (p.getVert k) +
            G.dist (p.getVert k) w :=
      hconn.dist_triangle
    rw [hq21] at htri1
    rw [h1p, hpkw] at htri2
    constructor
    · exact hjone
    constructor <;> omega
  · have hjtwo : 2 ≤ j := by omega
    have hq2j : G.dist (q.getVert 2) (q.getVert j) = j - 2 :=
      dist_getVert_eq_sub_of_le_of_length_eq_dist q hqdist
        (i := 2) (j := j) hjtwo hj
    have hqjw :
        G.dist (q.getVert j) w ≤ 1 + (p.length - k) := by
      have htriangle :
          G.dist (q.getVert j) w ≤
            G.dist (q.getVert j) (p.getVert k) +
              G.dist (p.getVert k) w :=
        hconn.dist_triangle
      rw [hqp, hpkw] at htriangle
      exact htriangle
    have htriangle :
        G.dist (q.getVert 2) w ≤
          G.dist (q.getVert 2) (q.getVert j) +
            G.dist (q.getVert j) w :=
      hconn.dist_triangle
    omega

omit [Fintype α] [DecidableEq α] in
/-- Two geodesics from a common initial vertex concatenate in reverse order
to an induced path when their positive-index parts are disjoint and have no
edges between them. -/
lemma isInducedPath_reverse_append_of_geodesics
    {v0 vr w : α}
    (q : G.Walk v0 vr) (p : G.Walk v0 w)
    (hqdist : q.length = G.dist v0 vr)
    (hpdist : p.length = G.dist v0 w)
    (hcross_ne :
      ∀ {j k : ℕ}, 1 ≤ j → j ≤ q.length → 1 ≤ k → k ≤ p.length →
        q.getVert j ≠ p.getVert k)
    (hcross_not_adj :
      ∀ {j k : ℕ}, 1 ≤ j → j ≤ q.length → 1 ≤ k → k ≤ p.length →
        ¬G.Adj (q.getVert j) (p.getVert k)) :
    isInducedPath G (q.reverse.append p).support := by
  let c := q.reverse.append p
  have hcpath : c.IsPath := by
    apply isPath_of_injective_getVert_le c
    intro i j hi hj heq
    have hi' : i ≤ q.length + p.length := by
      simpa only [c, Walk.length_append, Walk.length_reverse] using hi
    have hj' : j ≤ q.length + p.length := by
      simpa only [c, Walk.length_append, Walk.length_reverse] using hj
    by_cases hiq : i < q.length <;> by_cases hjq : j < q.length
    · have heq' :
          q.getVert (q.length - i) = q.getVert (q.length - j) := by
        simpa only [c, Walk.getVert_append, Walk.length_reverse,
          Walk.getVert_reverse, ite_eq_left hiq, ite_eq_left hjq] using heq
      have hdi :
          G.dist v0 (q.getVert (q.length - i)) = q.length - i := by
        simpa only [Walk.getVert_zero, Nat.sub_zero] using
          dist_getVert_eq_sub_of_le_of_length_eq_dist q hqdist
            (i := 0) (j := q.length - i) (Nat.zero_le _) (Nat.sub_le _ _)
      have hdj :
          G.dist v0 (q.getVert (q.length - j)) = q.length - j := by
        simpa only [Walk.getVert_zero, Nat.sub_zero] using
          dist_getVert_eq_sub_of_le_of_length_eq_dist q hqdist
            (i := 0) (j := q.length - j) (Nat.zero_le _) (Nat.sub_le _ _)
      rw [heq'] at hdi
      omega
    · have heq' :
          q.getVert (q.length - i) =
            p.getVert (j - q.length) := by
        simpa only [c, Walk.getVert_append, Walk.length_reverse,
          Walk.getVert_reverse, ite_eq_left hiq, ite_eq_right hjq] using heq
      have ha : 1 ≤ q.length - i := by omega
      have haj : q.length - i ≤ q.length := Nat.sub_le _ _
      have hb : j - q.length ≤ p.length := by omega
      by_cases hbzero : j - q.length = 0
      · have hda :
            G.dist v0 (q.getVert (q.length - i)) = q.length - i := by
          simpa only [Walk.getVert_zero, Nat.sub_zero] using
            dist_getVert_eq_sub_of_le_of_length_eq_dist q hqdist
              (i := 0) (j := q.length - i) (Nat.zero_le _) haj
        have heq0 : q.getVert (q.length - i) = v0 := by
          simpa only [hbzero, Walk.getVert_zero] using heq'
        rw [heq0, dist_self] at hda
        omega
      · have hbpos : 1 ≤ j - q.length := by omega
        exact False.elim <|
          hcross_ne ha haj hbpos hb heq'
    · have heq' :
          q.getVert (q.length - j) =
            p.getVert (i - q.length) := by
        symm
        simpa only [c, Walk.getVert_append, Walk.length_reverse,
          Walk.getVert_reverse, ite_eq_right hiq, ite_eq_left hjq] using heq
      have ha : 1 ≤ q.length - j := by omega
      have haj : q.length - j ≤ q.length := Nat.sub_le _ _
      have hb : i - q.length ≤ p.length := by omega
      by_cases hbzero : i - q.length = 0
      · have hda :
            G.dist v0 (q.getVert (q.length - j)) = q.length - j := by
          simpa only [Walk.getVert_zero, Nat.sub_zero] using
            dist_getVert_eq_sub_of_le_of_length_eq_dist q hqdist
              (i := 0) (j := q.length - j) (Nat.zero_le _) haj
        have heq0 : q.getVert (q.length - j) = v0 := by
          simpa only [hbzero, Walk.getVert_zero] using heq'
        rw [heq0, dist_self] at hda
        omega
      · have hbpos : 1 ≤ i - q.length := by omega
        exact False.elim <|
          hcross_ne ha haj hbpos hb heq'
    · have heq' :
          p.getVert (i - q.length) =
            p.getVert (j - q.length) := by
        simpa only [c, Walk.getVert_append, Walk.length_reverse,
          ite_eq_right hiq, ite_eq_right hjq] using heq
      have hai : i - q.length ≤ p.length := by omega
      have haj : j - q.length ≤ p.length := by omega
      have hdi :
          G.dist v0 (p.getVert (i - q.length)) = i - q.length := by
        simpa only [Walk.getVert_zero, Nat.sub_zero] using
          dist_getVert_eq_sub_of_le_of_length_eq_dist p hpdist
            (i := 0) (j := i - q.length) (Nat.zero_le _) hai
      have hdj :
          G.dist v0 (p.getVert (j - q.length)) = j - q.length := by
        simpa only [Walk.getVert_zero, Nat.sub_zero] using
          dist_getVert_eq_sub_of_le_of_length_eq_dist p hpdist
            (i := 0) (j := j - q.length) (Nat.zero_le _) haj
      rw [heq'] at hdi
      omega
  apply isInducedPath_support_of_isPath_of_adj_getVert c hcpath
  intro i j hi hj hadj
  have hi' : i ≤ q.length + p.length := by
    simpa only [c, Walk.length_append, Walk.length_reverse] using hi
  have hj' : j ≤ q.length + p.length := by
    simpa only [c, Walk.length_append, Walk.length_reverse] using hj
  by_cases hiq : i < q.length <;> by_cases hjq : j < q.length
  · have hadj' :
        G.Adj (q.getVert (q.length - i))
          (q.getVert (q.length - j)) := by
      simpa only [c, Walk.getVert_append, Walk.length_reverse,
        Walk.getVert_reverse, ite_eq_left hiq, ite_eq_left hjq] using hadj
    have hqq :=
      (adj_getVert_iff_consecutive_of_length_eq_dist q hqdist
        (Nat.sub_le _ _) (Nat.sub_le _ _)).mp hadj'
    omega
  · have hadj' :
        G.Adj (q.getVert (q.length - i))
          (p.getVert (j - q.length)) := by
      simpa only [c, Walk.getVert_append, Walk.length_reverse,
        Walk.getVert_reverse, ite_eq_left hiq, ite_eq_right hjq] using hadj
    have ha : 1 ≤ q.length - i := by omega
    have haj : q.length - i ≤ q.length := Nat.sub_le _ _
    have hb : j - q.length ≤ p.length := by omega
    by_cases hbzero : j - q.length = 0
    · have hadj0 :
          G.Adj (q.getVert (q.length - i)) (q.getVert 0) := by
        simpa only [hbzero, Walk.getVert_zero] using hadj'
      have hqq :=
        (adj_getVert_iff_consecutive_of_length_eq_dist q hqdist
          haj (Nat.zero_le _)).mp hadj0
      omega
    · have hbpos : 1 ≤ j - q.length := by omega
      exact False.elim <| hcross_not_adj ha haj hbpos hb hadj'
  · have hadj' :
        G.Adj (q.getVert (q.length - j))
          (p.getVert (i - q.length)) := by
      symm
      simpa only [c, Walk.getVert_append, Walk.length_reverse,
        Walk.getVert_reverse, ite_eq_right hiq, ite_eq_left hjq] using hadj
    have ha : 1 ≤ q.length - j := by omega
    have haj : q.length - j ≤ q.length := Nat.sub_le _ _
    have hb : i - q.length ≤ p.length := by omega
    by_cases hbzero : i - q.length = 0
    · have hadj0 :
          G.Adj (q.getVert (q.length - j)) (q.getVert 0) := by
        simpa only [hbzero, Walk.getVert_zero] using hadj'
      have hqq :=
        (adj_getVert_iff_consecutive_of_length_eq_dist q hqdist
          haj (Nat.zero_le _)).mp hadj0
      omega
    · have hbpos : 1 ≤ i - q.length := by omega
      exact False.elim <| hcross_not_adj ha haj hbpos hb hadj'
  · have hadj' :
        G.Adj (p.getVert (i - q.length))
          (p.getVert (j - q.length)) := by
      simpa only [c, Walk.getVert_append, Walk.length_reverse,
        ite_eq_right hiq, ite_eq_right hjq] using hadj
    have hai : i - q.length ≤ p.length := by omega
    have haj : j - q.length ≤ p.length := by omega
    have hpp :=
      (adj_getVert_iff_consecutive_of_length_eq_dist p hpdist hai haj).mp hadj'
    omega

omit [Fintype α] [DecidableEq α] in
/--
If the exceptional boundary edge is absent, Chung's two geodesics satisfy
the generic reverse-append criterion.
-/
lemma isInducedPath_chung_append_of_not_boundary [Nontrivial α]
    (hconn : G.Connected) {v0 vr w : α}
    (q : G.Walk v0 vr) (p : G.Walk v0 w)
    (hqdist : q.length = G.dist v0 vr)
    (hqrad : q.length = G.radius.toNat)
    (hpdist : p.length = G.dist v0 w)
    (hfar : G.radius.toNat ≤ G.dist (q.getVert 2) w)
    (hpupper : p.length ≤ G.radius.toNat - 1)
    (hrtwo : 2 ≤ G.radius.toNat)
    (hboundary : ¬G.Adj (q.getVert 1) (p.getVert 1)) :
    isInducedPath G (q.reverse.append p).support := by
  apply isInducedPath_reverse_append_of_geodesics q p hqdist hpdist
  · intro j k hjpos hj hkpos hk
    exact chung_geodesics_cross_ne hconn q p hqdist hqrad hpdist hfar
      hpupper hrtwo hj hkpos hk
  · intro j k hjpos hj hkpos hk hadj
    obtain ⟨hjone, hkone, -⟩ :=
      chung_geodesics_cross_adj_boundary hconn q p hqdist hqrad hpdist
        hfar hpupper hrtwo hjpos hj hkpos hk hadj
    apply hboundary
    simpa only [hjone, hkone] using hadj

omit [Fintype α] [DecidableEq α] in
/--
When the exceptional edge `q[1]—p[1]` exists, delete the common center.
The remaining two walks are geodesics from `q[1]`, have no further cross
edges, and yield an induced path on exactly `2 * radius - 1` vertices.
-/
lemma exists_inducedPath_chung_boundary [Nontrivial α]
    (hconn : G.Connected) {v0 vr w : α}
    (q : G.Walk v0 vr) (p : G.Walk v0 w)
    (hqdist : q.length = G.dist v0 vr)
    (hqrad : q.length = G.radius.toNat)
    (hpdist : p.length = G.dist v0 w)
    (hfar : G.radius.toNat ≤ G.dist (q.getVert 2) w)
    (hpupper : p.length ≤ G.radius.toNat - 1)
    (hrtwo : 2 ≤ G.radius.toNat)
    (hppos : 1 ≤ p.length)
    (hboundary : G.Adj (q.getVert 1) (p.getVert 1)) :
    ∃ l : List α,
      isInducedPath G l ∧ l.length = 2 * G.radius.toNat - 1 := by
  obtain ⟨-, -, hplen⟩ :=
    chung_geodesics_cross_adj_boundary hconn q p hqdist hqrad hpdist
      hfar hpupper hrtwo (j := 1) (k := 1)
        (by omega) (by omega) (by omega) hppos hboundary
  have hpnotnil : ¬p.Nil := Walk.not_nil_iff_lt_length.mpr (by omega)
  let q' := q.drop 1
  have hq'dist : q'.length = G.dist (q.getVert 1) vr := by
    have hdist : G.dist (q.getVert 1) vr = q.length - 1 := by
      simpa only [Walk.getVert_length] using
        dist_getVert_eq_sub_of_le_of_length_eq_dist q hqdist
          (i := 1) (j := q.length) (by omega) (le_refl _)
    simp only [q', Walk.drop_length]
    exact hdist.symm
  let b := p.tail.cons hboundary
  have hblen : b.length = p.length := by
    simpa only [b, Walk.length_cons] using
      (Walk.length_tail_add_one hpnotnil)
  have hq12 : G.dist (q.getVert 1) (q.getVert 2) = 1 := by
    simpa only [Nat.reduceSubDiff] using
      dist_getVert_eq_sub_of_le_of_length_eq_dist q hqdist
        (i := 1) (j := 2) (by omega) (by omega)
  have hq21 : G.dist (q.getVert 2) (q.getVert 1) = 1 := by
    rw [dist_comm]
    exact hq12
  have htri :
      G.dist (q.getVert 2) w ≤
        G.dist (q.getVert 2) (q.getVert 1) +
          G.dist (q.getVert 1) w :=
    hconn.dist_triangle
  rw [hq21] at htri
  have hbdist : b.length = G.dist (q.getVert 1) w := by
    have hub : G.dist (q.getVert 1) w ≤ b.length := dist_le b
    omega
  have hcross_ne :
      ∀ {j k : ℕ}, 1 ≤ j → j ≤ q'.length → 1 ≤ k → k ≤ b.length →
        q'.getVert j ≠ b.getVert k := by
    intro j k hjpos hj hkpos hk
    have hj' : 1 + j ≤ q.length := by
      simp only [q', Walk.drop_length] at hj
      omega
    have hk' : k ≤ p.length := by omega
    have hqget : q'.getVert j = q.getVert (1 + j) := by
      simp only [q', Walk.drop_getVert]
    have hbget : b.getVert k = p.getVert k := by
      simp only [b]
      rw [Walk.getVert_cons p.tail hboundary (by omega)]
      simp only [Walk.getVert_tail, Nat.sub_add_cancel hkpos]
    rw [hqget, hbget]
    exact chung_geodesics_cross_ne hconn q p hqdist hqrad hpdist hfar hpupper
      hrtwo hj' hkpos hk'
  have hcross_not_adj :
      ∀ {j k : ℕ}, 1 ≤ j → j ≤ q'.length → 1 ≤ k → k ≤ b.length →
        ¬G.Adj (q'.getVert j) (b.getVert k) := by
    intro j k hjpos hj hkpos hk hadj
    have hj' : 1 + j ≤ q.length := by
      simp only [q', Walk.drop_length] at hj
      omega
    have hk' : k ≤ p.length := by omega
    have hqget : q'.getVert j = q.getVert (1 + j) := by
      simp only [q', Walk.drop_getVert]
    have hbget : b.getVert k = p.getVert k := by
      simp only [b]
      rw [Walk.getVert_cons p.tail hboundary (by omega)]
      simp only [Walk.getVert_tail, Nat.sub_add_cancel hkpos]
    rw [hqget, hbget] at hadj
    obtain ⟨hjone, -, -⟩ :=
      chung_geodesics_cross_adj_boundary hconn q p hqdist hqrad hpdist
        hfar hpupper hrtwo (by omega) hj' hkpos hk' hadj
    omega
  have hinduced :=
    isInducedPath_reverse_append_of_geodesics q' b hq'dist hbdist
      hcross_ne hcross_not_adj
  refine ⟨(q'.reverse.append b).support, hinduced, ?_⟩
  rw [Walk.length_support, Walk.length_append, Walk.length_reverse]
  simp only [q', Walk.drop_length, hblen]
  omega

/-- The radius-drop kernel in Chung's induction. -/
theorem chung_radius_drop_kernel [Nontrivial α]
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (hconn : G.Connected) (vr : α)
    (hdel : (G.induce {vr}ᶜ).Connected)
    (hradius : (G.induce {vr}ᶜ).radius.toNat < G.radius.toNat) :
    2 * G.radius.toNat ≤ path G + 1 := by
  by_cases hrtwo : 2 ≤ G.radius.toNat
  · obtain ⟨v0, q, w, p, -, hqdist, hqrad, hpdist, -, hfar,
        hplower, hpupper⟩ :=
      exists_chung_geodesic_data hconn vr hdel hradius hrtwo
    by_cases hpzero : p.length = 0
    · have hinduced := isInducedPath_support_of_length_eq_dist q hqdist
      have hpath :=
        length_le_path_of_isInducedPath' (G := G) q.support hinduced
      rw [Walk.length_support, hqrad] at hpath
      omega
    · have hppos : 1 ≤ p.length := by omega
      by_cases hboundary : G.Adj (q.getVert 1) (p.getVert 1)
      · obtain ⟨l, hl, hllen⟩ :=
          exists_inducedPath_chung_boundary hconn q p hqdist hqrad hpdist
            hfar hpupper hrtwo hppos hboundary
        have hpath := length_le_path_of_isInducedPath' (G := G) l hl
        omega
      · have hl :=
          isInducedPath_chung_append_of_not_boundary hconn q p hqdist hqrad
            hpdist hfar hpupper hrtwo hboundary
        have hpath :=
          length_le_path_of_isInducedPath' (G := G)
            (q.reverse.append p).support hl
        rw [Walk.length_support, Walk.length_append, Walk.length_reverse] at hpath
        omega
  · have hpath : 1 ≤ path G := one_le_path (G := G)
    omega

/--
Finite induction reduces Chung's theorem to the radius-drop kernel: whenever
deleting a non-cut vertex strictly lowers the radius, the two-geodesic
construction supplies the required induced path.
-/
theorem chung_bound_nat_of_radius_drop_kernel
    (kernel :
      ∀ {β : Type u} [Fintype β] [DecidableEq β] [Nontrivial β]
        (H : SimpleGraph β) [DecidableRel H.Adj],
        H.Connected →
        ∀ vr : β, (H.induce {vr}ᶜ).Connected →
          (H.induce {vr}ᶜ).radius.toNat < H.radius.toNat →
          2 * H.radius.toNat ≤ path H + 1)
    [Nonempty α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (hconn : G.Connected) :
    2 * G.radius.toNat ≤ path G + 1 := by
  induction hn : Fintype.card α using Nat.strong_induction_on generalizing α with
  | ind n ih =>
      by_cases hα : Nontrivial α
      · let : Nontrivial α := hα
        obtain ⟨vr, hdel, hcard⟩ :=
          exists_connected_deletion_with_card_lt (G := G) hconn
        let H := G.induce ({vr}ᶜ : Set α)
        let : Nonempty {x : α // x ∈ ({vr}ᶜ : Set α)} := hdel.nonempty
        have hind :
            2 * H.radius.toNat ≤ path H + 1 := by
          apply ih (Fintype.card {x : α // x ∈ ({vr}ᶜ : Set α)})
          · simpa only [hn] using hcard
          · simpa only [H] using hdel
          · rfl
        by_cases hradius : G.radius.toNat ≤ H.radius.toNat
        · have hpath : path H ≤ path G := path_induce_le (G := G) {vr}ᶜ
          omega
        · exact kernel (β := α) G hconn vr hdel (Nat.lt_of_not_ge hradius)
      · have : Subsingleton α := not_nontrivial_iff_subsingleton.mp hα
        have hradius : G.radius = 0 :=
          G.radius_eq_zero_iff.mpr ⟨inferInstance, inferInstance⟩
        simp [hradius]

/-- Natural-number form of the Erdős--Saks--Sós / Chung bound. -/
theorem chung_bound_nat [Nonempty α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (hconn : G.Connected) :
    2 * G.radius.toNat ≤ path G + 1 := by
  apply chung_bound_nat_of_radius_drop_kernel
  intro β _ _ _ H _ hH vr hdel hradius
  exact chung_radius_drop_kernel H hH vr hdel hradius
  exact hconn

end SimpleGraph
