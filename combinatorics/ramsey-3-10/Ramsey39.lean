import Std

namespace Ramsey310

/-- Exoo’s 39-vertex graph in the vertex order of his published matrix.
    An off-diagonal zero in the matrix is an edge. Bit j records adjacency to j.
    Source: https://cs.indstate.edu/ge/RAMSEY/r3.10.39 -/
def rows : Array Nat := #[
  0x204808452, 0x409010885, 0x205012110a, 0xa0242214, 0x5102084029,
  0x420221250, 0x10424420a1, 0x84884142, 0x4109008684, 0x2210110928,
  0x10a0484901, 0x102809602, 0x4205012824, 0x2408125048, 0x50242490,
  0x410290901, 0x1060429202, 0x82852024, 0x41050a4048, 0x208148490,
  0x4105282204, 0x120850c028, 0x6410a10440, 0x1061420881, 0x2082941102,
  0x225020850, 0x240a141081, 0x854282102, 0x10a840c204, 0x912810428,
  0x4488814044, 0x151020488, 0x22a0140910, 0xd02281201, 0x124440a022,
  0x7228000000, 0xc10a10450, 0x905402204, 0x840541110]

def adjacent (x y : Fin 39) : Bool := (rows[x.val]!).testBit y.val

/-- Count selected vertices in the canonical list of all vertices. -/
def orderOf {n : Nat} (selected : Fin n → Bool) : Nat :=
  ((List.finRange n).filter selected).length

/-- The graph is undirected and has no loops. -/
def Simple {n : Nat} (edge : Fin n → Fin n → Bool) : Prop :=
  (∀ v, edge v v = false) ∧ (∀ v w, edge v w = edge w v)

def TriangleFree {n : Nat} (edge : Fin n → Fin n → Bool) : Prop :=
  ∀ u v w, edge u v = true → edge v w = true → edge w u = false

def Independent {n : Nat} (edge : Fin n → Fin n → Bool)
    (selected : Fin n → Bool) : Prop :=
  ∀ v w, selected v = true → selected w = true → edge v w = false

private def nonneighbors {α : Type} (edge : α → α → Bool) (v : α) (vs : List α) :=
  vs.filter fun w => !edge v w

/-- An independent set either skips v or uses v and skips every neighbor of v. -/
private def excludes {α : Type} (edge : α → α → Bool) : Nat → List α → Bool
  | 0, _ => false
  | _ + 1, [] => true
  | k + 1, v :: vs =>
    if vs.length < k then true
    else excludes edge (k + 1) vs && excludes edge k (nonneighbors edge v vs)
termination_by _ vs => vs.length
decreasing_by
  · exact Nat.lt_succ_self _
  · exact Nat.lt_succ_of_le (List.length_filter_le _ _)

private theorem excludes_sound {α : Type} {edge : α → α → Bool}
    (s : α → Bool) (ind : ∀ x y, s x = true → s y = true → edge x y = false)
    (k : Nat) (vs : List α) (pass : excludes edge k vs = true) :
    (vs.filter s).length < k := by
  fun_induction excludes edge k vs with
  | case1 => contradiction
  | case2 => simp
  | case3 k v vs short =>
    exact Nat.lt_of_le_of_lt (List.length_filter_le s _) (Nat.succ_lt_succ short)
  | case4 k v vs _ skipV takeV =>
    obtain ⟨skip, take⟩ := Bool.and_eq_true_iff.mp pass
    cases hv : s v with
    | false => simpa [hv] using skipV skip
    | true =>
      have same : (nonneighbors edge v vs).filter s = vs.filter s := by
        rw [nonneighbors, List.filter_filter]
        apply List.filter_congr
        intro w _
        cases hw : s w <;> simp_all
      simpa [hv, same] using Nat.succ_lt_succ (takeV take)

/-- Run the independent-set check on every vertex of a supplied graph. -/
def excludesIndependentTen {n : Nat} (edge : Fin n → Fin n → Bool) : Bool :=
  excludes edge 10 (List.finRange n)

theorem excludesIndependentTen_sound {n : Nat} {edge : Fin n → Fin n → Bool}
    (pass : excludesIndependentTen edge = true) (s : Fin n → Bool)
    (ind : Independent edge s) : orderOf s < 10 :=
  excludes_sound s ind 10 (List.finRange n) pass

theorem exoo_simple : Simple adjacent := by
  unfold Simple
  decide +kernel

theorem exoo_triangleFree : TriangleFree adjacent := by
  unfold TriangleFree
  decide +kernel

private theorem exoo_excludes_ten : excludesIndependentTen adjacent = true := by
  decide +kernel

theorem exoo_independence_bound (s : Fin 39 → Bool) (ind : Independent adjacent s) :
    orderOf s < 10 :=
  excludesIndependentTen_sound exoo_excludes_ten s ind

/-- A counterexample to the Ramsey property on 39 vertices. -/
theorem lower_bound_witness :
    ∃ edge : Fin 39 → Fin 39 → Bool,
      Simple edge ∧ TriangleFree edge ∧
        ∀ s, Independent edge s → orderOf s < 10 :=
  ⟨adjacent, exoo_simple, exoo_triangleFree, exoo_independence_bound⟩

end Ramsey310
