import SevenCycle.Basic

namespace SevenCycle
namespace LowerBound

private abbrev Part := Fin 4

/-- Part 0 is the apex, and parts 1, 2, and 3 are consecutive triples. -/
private def part (x : Fin 10) : Part :=
  if x = 0 then 0 else if x ≤ 3 then 1 else if x ≤ 6 then 2 else 3

/-- Each color joins the apex to one triple, fills that triple, and joins
the other two triples. The row and column indices are the part numbers. -/
private def template (a b : Part) : Color :=
  let table : Vector (Vector Color 4) 4 := #v[
    #v[0, 0, 1, 2],
    #v[0, 0, 2, 1],
    #v[1, 2, 1, 0],
    #v[2, 1, 0, 2]]
  (table.get a).get b

def coloring : Coloring 10 where
  edge x y := template (part x) (part y)
  symm x y := (by decide : ∀ a b, template a b = template b a) (part x) (part y)

private theorem allParts {p : Part → Prop}
    (h₀ : p 0) (h₁ : p 1) (h₂ : p 2) (h₃ : p 3) : ∀ x, p x
  | 0 => h₀
  | 1 => h₁
  | 2 => h₂
  | 3 => h₃

set_option maxHeartbeats 0 in
/-- Each word of seven part labels using at most the available vertices has
at least three cyclic changes. Lean's kernel checks all 4^7 words. -/
private theorem check : ∀ a b c d e f g : Part,
    let tags := [a, b, c, d, e, f, g]
    tags.count 0 ≤ 1 → tags.count 1 ≤ 3 → tags.count 2 ≤ 3 → tags.count 3 ≤ 3 →
    ¬ changes template tags ≤ 2 := by
  apply allParts <;> apply allParts <;> apply allParts <;> decide +kernel

private theorem capacity {xs : List (Fin 10)} (h : xs.Nodup) (t : Part) :
    (xs.map part).count t ≤ ((List.finRange 10).map part).count t := by
  simp only [List.count_eq_length_filter, List.filter_map, List.length_map]
  apply List.Nodup.length_le_of_subset (h.filter _)
  exact List.filter_subset _ (fun {_} _ => List.mem_finRange _)

theorem avoids : ¬ HasGoodSeven coloring := by
  rintro ⟨vs, hlen, hdistinct, hchanges⟩
  match vs, hlen with
  | [a, b, c, d, e, f, g], rfl =>
    have cap := capacity hdistinct
    exact check (part a) (part b) (part c) (part d) (part e) (part f) (part g)
      (cap 0) (cap 1) (cap 2) (cap 3) hchanges

end LowerBound

theorem ten_does_not_force : ¬ ForcesSeven 10 := fun h => LowerBound.avoids (h _)

end SevenCycle
