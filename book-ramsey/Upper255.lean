import DegreeObstruction

namespace BookRamsey.Upper255
open DegreeObstruction (total total_const total_add total_indicator total_congr total_swap walks split_count)

/-! Suppose both books are absent. A red edge has at most 62 common red neighbors.
On a blue edge uv, inclusion-exclusion gives at most d(u) + d(v) − 190,
where d is red degree.

Count ordered red two-step walks with distinct endpoints. Counting by the
middle vertex gives ∑ d(d−1). Applying the two edge bounds at the endpoints
gives at most 62 ∑ d + ∑ (254−d)(2d−190). Rearranging yields

    ∑ (d−127)(3d−380) ≤ 0.

Every term is nonnegative for integer d, with equality only at 127.
But 255 vertices of degree 127 would have an odd degree sum. -/

private abbrev vertices := List.finRange 255

private theorem total_mul (xs : List α) (k : Nat) (f : α → Nat) :
    total xs (fun x => k * f x) = k * total xs f := by
  induction k with
  | zero => simp [total_const]
  | succ k ih => simp [Nat.succ_mul, total_add, ih]

private theorem total_le (xs : List α) {f h : α → Nat} (le : ∀ x, f x ≤ h x) :
    total xs f ≤ total xs h := by
  induction xs with
  | nil => exact Nat.le_refl 0
  | cons x xs ih => exact Nat.add_le_add (le x) ih

/-- Number of red two-step walks starting at u. -/
private def walksFrom (g : Graph 255) (u : Fin 255) :=
  total vertices (fun v => if g.adj u v then g.degree v else 0)

private theorem walk_total (g : Graph 255) :
    total vertices (walksFrom g) = total vertices (fun v => g.degree v * g.degree v) := by
  unfold walksFrom
  rw [total_swap]
  apply total_congr
  intro v _
  have sym (x : Fin 255) : g.adj x v = g.adj v x := g.symm ..
  simp only [sym, total_indicator]
  rfl

/-- A red spine has at most 62 red pages. On a blue spine the bound of 63
blue pages gives at most d(u) + d(v) − 190 common red neighbors. -/
private theorem spine_bound (g : Graph 255) (hr : ¬g.HasBook 63) (hb : ¬g.complement.HasBook 64)
    (u v : Fin 255) :
    g.commonCount u v + (if g.adj u v then g.degree v else 0) +
        (if g.complement.adj u v then 190 else 0) ≤
      g.degree v + (if g.adj u v then 62 else 0) +
        (if g.complement.adj u v then g.degree u else 0) := by
  by_cases same : u = v
  · subst v
    simp [g.loopless, g.complement.loopless, Graph.commonCount, Graph.degree]
  · have red := (g.not_hasBook_iff 63).mp hr u v
    have blue := (g.complement.not_hasBook_iff 64).mp hb u v
    have nonedge := g.nonedge_commonCount u v same
    cases edge : g.adj u v <;> simp_all [Graph.complement] <;> omega

private theorem row_bound (g : Graph 255) (hr : ¬g.HasBook 63) (hb : ¬g.complement.HasBook 64)
    (u : Fin 255) :
    2 * walksFrom g u + 190 * g.complement.degree u ≤
      total vertices g.degree + 62 * g.degree u + g.complement.degree u * g.degree u := by
  have bound := total_le vertices (spine_bound g hr hb u)
  have walks_eq : total vertices (g.commonCount u) = walksFrom g u := walks g u vertices vertices
  simp only [total_add, total_indicator, walks_eq] at bound
  change walksFrom g u + walksFrom g u + g.complement.degree u * 190 ≤
    total vertices g.degree + g.degree u * 62 + g.complement.degree u * g.degree u at bound
  simpa only [Nat.two_mul, Nat.mul_comm 190, Nat.mul_comm 62] using bound

private theorem degree_split (g : Graph 255) (u : Fin 255) :
    g.degree u + g.complement.degree u = 254 := by
  have split := split_count g u vertices
  have self : vertices.count u = 1 := (List.nodup_finRange 255).count_of_mem (List.mem_finRange u)
  rw [self, List.length_finRange] at split
  change 1 + g.degree u + g.complement.degree u = 255 at split
  omega

/-- The difference between the book bounds is (d − 127)(3d − 380). -/
private theorem degree_cost (d b : Nat) (split : d + b = 254) :
    317 * d + b * d + (if d != 127 then 1 else 0) ≤ 2 * (d * d) + 190 * b := by
  have arithmetic : ∀ d : Fin 255, let b := 254 - d.val
      317 * d.val + b * d.val + (if d.val != 127 then 1 else 0) ≤
        2 * (d.val * d.val) + 190 * b := by decide +kernel
  simpa only [show 254 - d = b by omega] using arithmetic ⟨d, by omega⟩

private theorem handshake (g : Graph n) (xs : List (Fin n)) :
    2 ∣ total xs (fun u => xs.countP (g.adj u)) := by
  induction xs with
  | nil => simp [total]
  | cons u xs ih =>
    change 2 ∣ (u :: xs).countP (g.adj u) + total xs (fun v => (u :: xs).countP (g.adj v))
    simp only [List.countP_cons, g.loopless, Bool.false_eq_true, ite_false, Nat.add_zero, total_add]
    simp only [g.symm _ u, total_indicator, Nat.mul_one]
    omega

/-- Every 255-vertex graph contains a red 63-book or a blue 64-book. -/
theorem upper (g : Graph 255) : g.HasBook 63 ∨ g.complement.HasBook 64 := by
  apply Classical.byContradiction
  intro neither
  have bound := total_le vertices (row_bound g (fun h => neither (.inl h)) (fun h => neither (.inr h)))
  simp only [total_add, total_mul, total_const, walk_total, List.length_finRange] at bound

  have costs := total_le vertices (fun u => degree_cost _ _ (degree_split g u))
  simp only [total_add, total_mul, total_indicator, Nat.mul_one] at costs
  have zero : vertices.countP (fun u => g.degree u != 127) = 0 := by omega
  have regular : ∀ u, g.degree u = 127 := by simpa using List.countP_eq_zero.mp zero

  have even : 2 ∣ total vertices g.degree := handshake g vertices
  rw [show g.degree = fun _ => 127 from funext regular, total_const, List.length_finRange] at even
  exact (by decide : ¬2 ∣ 255 * 127) even

end BookRamsey.Upper255
