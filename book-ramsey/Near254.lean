import BookRamsey

namespace BookRamsey.Near254

/-! A failed two-circulant candidate. The two explicit spines below show
exactly why it fails, without enumerating all 32,131 unordered pairs. -/

private def orbitMask (seeds : List Nat) (withNegatives : Bool) : Nat := Id.run do
  let mut mask := 0
  for s in seeds do
    for h in [1, 19, 107] do
      let r := (s * h) % 127
      mask := mask ||| (1 <<< r)
      if withNegatives then mask := mask ||| (1 <<< ((127 - r) % 127))
  return mask

private def within : Nat := orbitMask [1, 5, 6, 8, 12, 15, 16, 17, 30, 36] true
private def across : Nat := orbitMask
  [1, 9, 10, 11, 13, 15, 17, 22, 24, 26, 29, 32, 36, 45, 46, 51, 53, 58, 59, 71, 72] false

def graph : Graph 254 := Graph.ofUpper fun u v =>
  let t := (v.val % 127 + 127 - u.val % 127) % 127
  if v.val < 127 then within.testBit t
  else if u.val < 127 then across.testBit t
  else !(within.testBit t)

set_option maxRecDepth 8192 in
theorem red_spine : graph.adj 0 1 = true ∧ graph.commonCount 0 1 = 63 := by decide +kernel

set_option maxRecDepth 8192 in
theorem blue_spine :
    graph.complement.adj 127 128 = true ∧ graph.complement.commonCount 127 128 = 64 := by
  decide +kernel

theorem fails : graph.HasBook 63 ∧ graph.complement.HasBook 64 :=
  ⟨(Graph.hasBook_iff ..).mpr ⟨0, 1, red_spine.1, by simp [red_spine.2]⟩,
   (Graph.hasBook_iff ..).mpr ⟨127, 128, blue_spine.1, by simp [blue_spine.2]⟩⟩

end BookRamsey.Near254
