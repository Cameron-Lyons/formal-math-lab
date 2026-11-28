import Erdos64.PathFreeSearch

namespace Erdos64

/-- Two neighbors of the next vertex cannot already be adjacent in a
triangle-free graph. Intersect this restriction with the cycle masks. -/
private def withoutEdges (allowed : Nat → Nat) (nbrs : Array Nat) (i : Nat) : Nat :=
  let candidates := allowed i
  candidates ^^^ (candidates &&& nbrs.getD i 0)

private theorem triangleThroughFresh {V : Type u} {G : Graph V} {rows : Array Nat}
    {i j m : Nat} (hi : i < rows.size) (hj : j < rows.size) (ne : i ≠ j)
    (bi : m.testBit i = true) (bj : m.testBit j = true) (edge : adjAt rows i j = true)
    (c : Copy G (rows.size+1) (extendAdj rows.size (adjAt rows) m)) :
    HasCycle G 3 := by
  let f (t : Nat) := if t = 0 then i else j
  apply cycleThroughFresh c (k := 1) f
  · intro t ht
    simp only [f]
    split <;> assumption
  · intro a ha b hb eq
    by_cases az : a = 0 <;> by_cases bz : b = 0 <;>
      simp [f, az, bz, ne, Ne.symm ne] at eq <;> omega
  · intro a ha
    have : a = 0 := by omega
    simpa [f, this] using edge
  · simpa [f] using bi
  · simpa [f] using bj

private theorem withoutEdges_sound {V : Type u} {G : Graph V} {rows : Array Nat}
    {i j m : Nat} (hi : i < rows.size) (hj : j < rows.size) (ne : i ≠ j)
    (bi : m.testBit i = true) (bj : m.testBit j = true) (tri : ¬ HasCycle G 3)
    (none : ¬ (HasCycle G 4 ∨ HasCycle G 8 ∨ HasCycle G 16))
    (c : Copy G (rows.size+1) (extendAdj rows.size (adjAt rows) m)) :
    (withoutEdges (allowedAt (allowedRows rows (neighborMasks rows)))
      (neighborMasks rows) i).testBit j = true := by
  have noEdge : adjAt rows i j = false := Bool.eq_false_iff.mpr (fun edge =>
    tri (triangleThroughFresh hi hj ne bi bj edge c))
  rw [withoutEdges, Nat.testBit_xor, Nat.testBit_and, neighborMasks_bit hi hj, noEdge,
    allowedRows_sound (nbrs := neighborMasks rows) hi hj ne bi bj none c]
  rfl

private def hintsFor (r : Nat) (dominating : Bool) (nbrs : Array Nat) : PathHints :=
  if dominating then default else pathHints nbrs r

private def anchorFor (r : Nat) (dominating : Bool) (nbrs : Array Nat) (allowed : Nat → Nat)
    (hints : PathHints) : Option Anchor :=
  if dominating then pickAnchor r nbrs allowed else pathAnchor r nbrs allowed hints

/-- In longest-path mode the search forbids a longer induced path. In
dominating-path mode every new vertex must meet the fixed seed. -/
def closesTriangleFree (r : Nat) (dominating : Bool) : Nat → Array Nat → Bool
  | 0, _ => false
  | fuel+1, rows =>
    let nbrs := neighborMasks rows
    let hints := hintsFor r dominating nbrs
    if !dominating && longPath rows r hints then true else
    let allowed := withoutEdges (allowedAt (allowedRows rows nbrs)) nbrs
    match anchorFor r dominating nbrs allowed hints with
    | none => false
    | some a =>
      decide (a.vertex < rows.size ∧ ∀ i : Fin rows.size,
        adjAt rows a.vertex i.val = true → i.val = a.p ∨ i.val = a.q) &&
      allMasks rows.size a.vertex allowed (fun m =>
        (dominating && !decide (∃ i : Fin r, m.testBit i.val = true)) ||
          closesTriangleFree r dominating fuel (rows.push m))

theorem closesTriangleFree_sound {V : Type u} {G : Graph V} {r : Nat} {dominating : Bool}
    (degree : MinDegreeThree G) (tri : ¬ HasCycle G 3)
    (none : ¬ (HasCycle G 4 ∨ HasCycle G 8 ∨ HasCycle G 16))
    (noLong : dominating = false → ¬ HasInducedPath G (r+1))
    (fuel : Nat) (rows : Array Nat) (len : r ≤ rows.size)
    (c : Copy G rows.size (adjAt rows)) (dom : dominating = true → DominatesFirst r c)
    (checked : closesTriangleFree r dominating fuel rows = true) : False := by
  induction fuel generalizing rows with
  | zero => simp [closesTriangleFree] at checked
  | succ fuel ih =>
    rw [closesTriangleFree] at checked
    split at checked
    next h =>
      obtain ⟨off, found⟩ := Bool.and_eq_true_iff.mp h
      exact noLong (by simpa using off) (longPath_sound found c)
    next =>
      dsimp only at checked
      split at checked
      · contradiction
      next a _ =>
        obtain ⟨cover, masks⟩ := Bool.and_eq_true_iff.mp checked
        obtain ⟨av, cover⟩ := of_decide_eq_true cover
        obtain ⟨m, bound, bit, cx, fixes⟩ := extendCopyFixing c degree av cover
        have domx (on : dominating = true) : DominatesFirst r cx :=
          (dom on).transfer (fun i hi => fixes i (by omega))
        have valid := allMasks_sound masks av bound bit
          (fun i j hi hj ne bi bj => withoutEdges_sound hi hj ne bi bj tri none cx)
        have skip : (dominating && !decide (∃ i : Fin r, m.testBit i.val = true)) = false := by
          cases on : dominating with
          | false => rfl
          | true => simp [maskMeetsDominatingSeed cx len (domx on)]
        obtain ⟨child, labels⟩ := pushCopyFixing cx
        exact ih _ (by simp; omega) child
          (fun on => (domx on).transfer (fun i _ => labels i))
          (by simpa only [skip, Bool.false_or] using valid)

end Erdos64
