import DegreeObstruction

namespace BookRamsey.DegreeObstruction

/-- When all cross-block codegrees are even, the
nonedge bound with constant 189 improves by one. -/
abbrev evenAcrossBound (a b : Nat) : Prop :=
  2 * a * b + (127 - b) * 190 ≤ 62 * b + (127 - b) * (2 * (a + b))

/-- Counting two-step walks from a vertex within its layer and across to
the other layer gives incompatible bounds on the internal degree. In integer
coordinates `s = a - 63` and `t = (a+b) - 126`, the bounds simplify to
`2*s²+s ≤ 63+t-t²` and `2*s² ≥ 64+2*t²-2*t`. -/
private theorem even_sweep : ∀ a : Fin 127, ∀ b : Fin 128,
    ¬ (insideBound a.val b.val ∧ evenAcrossBound a.val b.val) := by decide +kernel

theorem no_even_cross {g : Graph 254} (p : Blocks g a a b)
    (even : ∀ u ∈ p.left, ∀ v ∈ p.right, 2 ∣ g.commonCount u v) :
    g.check 63 64 = false := by
  apply Bool.eq_false_iff.mpr
  intro ok
  have across := across_walk_bound_of_nonedge ok p 190 (by
    intro u hu v hv h
    have blue := (g.codegree_bounds ok u v (p.separate hu hv)).2 h
    rw [p.leftDegree u hu, p.swap.leftDegree v hv] at blue
    have parity := even u hu v hv
    omega)
  obtain ⟨ha, hb⟩ := p.degreeBounds
  apply even_sweep ⟨a, by omega⟩ ⟨b, by omega⟩
  refine ⟨inside_walk_bound ok p, ?_⟩
  simpa only [evenAcrossBound, ← Nat.two_mul, Nat.mul_add] using across

abbrev Residue := Fin 127

private abbrev residues := List.finRange 127

/-- Relabeling the residues by a bijection preserves the number that satisfy a predicate. -/
private theorem count_bijection (f inv : Residue → Residue) (left : Function.LeftInverse inv f)
    (right : Function.RightInverse inv f) (p : Residue → Bool) :
    residues.countP (fun z => p (f z)) = residues.countP p := by
  have distinct : (residues.map f).Nodup :=
    (List.nodup_finRange 127).map f (fun _ _ h eq => h (left.injective eq))
  have perm : (residues.map f).Perm residues :=
    (List.perm_ext_iff_of_nodup distinct (List.nodup_finRange 127)).mpr (fun z => by
      simp only [List.mem_map, List.mem_finRange, true_and, iff_true, residues]
      exact ⟨inv z, right z⟩)
  simpa [List.countP_map, Function.comp_def] using perm.countP_eq p

private theorem count_shift (k : Residue) (p : Residue → Bool) :
    residues.countP (fun z => p (z-k)) = residues.countP p :=
  count_bijection _ (· + k) (fun _ => by grind) (fun _ => by grind) p

private theorem count_reflect (k : Residue) (p : Residue → Bool) :
    residues.countP (fun z => p (k-z)) = residues.countP p :=
  count_bijection _ (k - ·) (fun _ => by grind) (fun _ => by grind) p

/-- Two copies of the same undirected circulant, with arbitrary circulant
cross adjacency. This includes all cyclic and dihedral Cayley graphs of order
254 after labeling each of the two rotation cosets by the residues modulo 127. -/
structure IdenticalCirculantLayers (g : Graph 254) where
  left : Residue → Vert
  right : Residue → Vert
  partition : (((List.finRange 127).map left) ++ ((List.finRange 127).map right)).Perm
    (List.finRange 254)
  inner : Residue → Bool
  cross : Residue → Bool
  ll : ∀ i j, g.adj (left i) (left j) = inner (j-i)
  rr : ∀ i j, g.adj (right i) (right j) = inner (j-i)
  lr : ∀ i j, g.adj (left i) (right j) = cross (j-i)

private theorem IdenticalCirculantLayers.rl {g : Graph 254} (t : IdenticalCirculantLayers g)
    (i j : Residue) : g.adj (t.right i) (t.left j) = t.cross (i-j) :=
  (g.symm ..).trans (t.lr j i)

private def IdenticalCirculantLayers.blocks {g : Graph 254} (t : IdenticalCirculantLayers g) :
    Blocks g (residues.countP t.inner) (residues.countP t.inner) (residues.countP t.cross) where
  left := residues.map t.left
  right := residues.map t.right
  partition := t.partition
  leftSize := by simp [residues]
  rightSize := by simp [residues]
  degreesLeft u hu := by
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hu
    simp only [List.countP_map, Function.comp_def, t.ll, t.lr, count_shift, and_self]
  degreesRight u hu := by
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hu
    simp only [List.countP_map, Function.comp_def, t.rl, t.rr, count_reflect, count_shift, and_self]

/-- For the cross pair (left i, right j), the common neighbor left z is
paired with right (i+j-z). Reflection is a bijection between the two counts. -/
private theorem IdenticalCirculantLayers.crossEven {g : Graph 254}
    (t : IdenticalCirculantLayers g) (i j : Residue) :
    2 ∣ g.commonCount (t.left i) (t.right j) := by
  let common z := g.adj (t.left i) z && g.adj (t.right j) z
  let right z := common (t.right z)
  have pair (z : Residue) : common (t.left z) = right (i+j-z) := by
    simp only [right, common, t.ll, t.rl, t.lr]
    rw [g.symm (t.right j), t.rr, Bool.and_comm]
    congr 2 <;> grind
  change 2 ∣ (List.finRange 254).countP common
  rw [← t.partition.countP_eq, List.countP_append]
  change 2 ∣ residues.countP (fun z => common (t.left z)) + residues.countP right
  simp only [pair, count_reflect]
  omega

/-- Identical internal circulants with an arbitrary circulant cross block
cannot witness the requested book Ramsey lower bound. -/
theorem no_identical_circulant_layers {g : Graph 254} (t : IdenticalCirculantLayers g) :
    g.check 63 64 = false := by
  apply no_even_cross t.blocks
  intro u hu v hv
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hu
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hv
  exact t.crossEven i j

end BookRamsey.DegreeObstruction
