import Lean
import SevenCycle.Transfer

namespace SevenCycle

/-- The six edges between the leaves 1,2,3,4 of the distinguished star,
encoded in base three, with edge 12 as the least significant digit. -/
def packSeed (f : Fin 10 → Fin 10 → Color) : Nat :=
  (f 1 2).val + 3 * ((f 1 3).val + 3 * ((f 2 3).val +
    3 * ((f 1 4).val + 3 * ((f 2 4).val + 3 * (f 3 4).val))))

def seedCode (c : Coloring 10) : Nat := packSeed c.edge

/-- Minimum codes under the 24 permutations of the leaves and the two
permutations of colors that fix color 0. -/
def canonicalSeeds : List Nat :=
  [0, 1, 4, 5, 13, 14, 31, 32, 36, 37, 38, 40, 41, 44, 45, 46, 49, 50,
   53, 120, 121, 122, 123, 124, 125, 132, 133, 151, 156, 157, 364, 365,
   368, 377, 400, 401]

namespace Seed

private def swap (a b x : Fin 10) : Fin 10 :=
  if x = a then b else if x = b then a else x

/-- The first swap has four choices, the next has three, and the last has
two. These are the successive choices in a shuffle of the four leaves.
The low bit of `s` is reserved for the optional swap of colors 1 and 2. -/
private def vertex (s : Fin 48) : Fin 10 → Fin 10 :=
  swap 1 (Fin.ofNat 10 (1 + s.val / 12)) ∘
  swap 2 (Fin.ofNat 10 (2 + s.val / 4 % 3)) ∘
  swap 3 (Fin.ofNat 10 (3 + s.val / 2 % 2))

private def color (s : Fin 48) (a : Color) : Color :=
  if s.val % 2 = 0 ∨ a = 0 then a else if a = 1 then 2 else 1

private def Leaf (i : Fin 10) : Prop := i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4
private instance (i : Fin 10) : Decidable (Leaf i) := inferInstanceAs (Decidable (_ ∨ _))

set_option maxRecDepth 10000 in
private theorem vertex_injective : ∀ (s : Fin 48) (i j : Fin 10),
    vertex s i = vertex s j → i = j := by decide +kernel

private theorem color_injective : ∀ (s : Fin 48) (a b : Color),
    color s a = color s b → a = b := by decide +kernel

private theorem star_actions : ∀ s : Fin 48,
    vertex s 0 = 0 ∧ color s 0 = 0 ∧
    ∀ i : Fin 10, Leaf i → Leaf (vertex s i) := by decide +kernel

private def leafColor (a b c d e f : Color) (i j : Fin 10) : Color :=
  match min i.val j.val, max i.val j.val with
  | 1, 2 => a | 1, 3 => b | 2, 3 => c
  | 1, 4 => d | 2, 4 => e | 3, 4 => f
  | _, _ => 0

private def model (c : Coloring 10) : Fin 10 → Fin 10 → Color :=
  leafColor (c.edge 1 2) (c.edge 1 3) (c.edge 2 3) (c.edge 1 4) (c.edge 2 4) (c.edge 3 4)

private theorem model_agrees (c : Coloring 10) {i j : Fin 10}
    (hi : Leaf i) (hj : Leaf j) (hne : i ≠ j) : c.edge i j = model c i j := by
  rcases hi with rfl | rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl | rfl <;>
    first | contradiction | rfl | apply c.symm

private theorem allColors (P : Color → Prop) (h₀ : P 0) (h₁ : P 1) (h₂ : P 2) : ∀ x, P x := by
  intro x
  have hx := (by decide : ∀ y : Color, y = 0 ∨ y = 1 ∨ y = 2) x
  rcases hx with rfl | rfl | rfl <;> assumption

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem covers : ∀ a b c d e f : Color, ∃ s : Fin 48,
    packSeed (fun i j => color s (leafColor a b c d e f (vertex s i) (vertex s j))) ∈
      canonicalSeeds := by
  iterate 6 (all_goals apply allColors)
  -- Each goal fixes six colors. Select a witness by computation, then ask
  -- the kernel to check membership for that specific witness.
  run_tac
    let goals ← Lean.Elab.Tactic.getGoals
    for (g, index) in goals.zipIdx do
      let digit (i : Nat) := Fin.ofNat 3 (index / 3 ^ (5-i))
      let f := leafColor (digit 0) (digit 1) (digit 2) (digit 3) (digit 4) (digit 5)
      let good (s : Fin 48) := canonicalSeeds.contains
        (packSeed (fun i j => color s (f (vertex s i) (vertex s j))))
      let some s := (List.finRange 48).find? good | throwError "no canonical representative"
      Lean.Elab.Tactic.setGoals [g]
      let witness := Lean.Syntax.mkNumLit (toString s.val)
      Lean.Elab.Tactic.evalTactic (← `(tactic| exact ⟨$witness, by decide +kernel⟩))

private theorem seed_agrees (c : Coloring 10) (s : Fin 48) :
    seedCode (c.pullback (vertex s) (color s)) =
      packSeed (fun i j => color s (model c (vertex s i) (vertex s j))) := by
  have agree (i j : Fin 10) (hi : Leaf i) (hj : Leaf j) (h : i ≠ j) :
      c.edge (vertex s i) (vertex s j) = model c (vertex s i) (vertex s j) :=
    model_agrees c ((star_actions s).2.2 i hi) ((star_actions s).2.2 j hj)
      (fun heq => h (vertex_injective s i j heq))
  unfold seedCode packSeed Coloring.pullback
  simp (disch := decide) only [agree]

end Seed

/-- It suffices to check the listed leaf patterns in the four-edge star. -/
theorem normalizeSeed
    (canonical : ∀ c : Coloring 10, c.edge 0 1 = 0 → c.edge 0 2 = 0 →
      c.edge 0 3 = 0 → c.edge 0 4 = 0 → seedCode c ∈ canonicalSeeds → HasGoodSeven c)
    (c : Coloring 10) (h1 : c.edge 0 1 = 0) (h2 : c.edge 0 2 = 0)
    (h3 : c.edge 0 3 = 0) (h4 : c.edge 0 4 = 0) : HasGoodSeven c := by
  obtain ⟨s, hs⟩ := Seed.covers (c.edge 1 2) (c.edge 1 3) (c.edge 2 3)
    (c.edge 1 4) (c.edge 2 4) (c.edge 3 4)
  let d := c.pullback (Seed.vertex s) (Seed.color s)
  have star (i : Fin 10) (hi : Seed.Leaf i) : d.edge 0 i = 0 := by
    change Seed.color s (c.edge (Seed.vertex s 0) (Seed.vertex s i)) = 0
    rw [(Seed.star_actions s).1]
    rcases (Seed.star_actions s).2.2 i hi with h | h | h | h <;>
      simp only [h, h1, h2, h3, h4, (Seed.star_actions s).2.1]
  apply hasGoodSeven_of_pullback c (Seed.vertex s) (Seed.color s)
    (fun {_ _} h => Seed.vertex_injective _ _ _ h)
    (fun {_ _} h => Seed.color_injective _ _ _ h)
  apply canonical d (star 1 (by decide)) (star 2 (by decide))
    (star 3 (by decide)) (star 4 (by decide))
  rw [Seed.seed_agrees]
  exact hs

end SevenCycle
