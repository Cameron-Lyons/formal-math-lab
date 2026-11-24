import Marginal

/-! Fix a die. At a face let `a, b, c, e` count the higher labels on its
four opponents. If the counts agree modulo four, the factors in
`a * (b+1) * (c+2) * (e+3)` cover all four residues. Their product is
therefore divisible by eight. Under fair rankings the sum of these products
over the thirty faces has remainder four. -/
namespace FiveDice.EqualCuts

/-- All four opponents have congruent higher-label counts at every face of `d`. -/
def SynchronizedModFour (d : Die) (w : List Die) : Prop :=
  ∀ pre post : List Die, w = pre ++ d :: post →
    ∀ b c : Die, b ≠ d → c ≠ d → post.count b % 4 = post.count c % 4

private def score (d : Die) (post : List Die) : Nat :=
  let n := fun i => post.count (opponent d i)
  n 0 * (n 1 + 1) * (n 2 + 2) * (n 3 + 3)

/-- Expand the shifted product. Each bit of `m` selects one opponent in `term m`. -/
private def expansion (term : Fin 16 → Nat) : Nat :=
  term 15 + term 13 + 2 * (term 11 + term 9) + 3 * (term 7 + term 5) +
    6 * (term 3 + term 1)

private theorem expand_face (d : Die) (post : List Die) :
    score d post = expansion (fun m => productOfCounts (opponents d m) post) := by
  have indices : List.finRange 4 = [0, 1, 2, 3] := rfl
  simp +decide [score, expansion, productOfCounts, opponents, indices] <;> grind only

private theorem sum_scores (d : Die) (ss : List (List Die)) :
    (ss.map (score d)).sum = expansion (fun m => moment d m ss) := by
  induction ss with
  | nil => rfl
  | cons post ss ih =>
    simp only [List.map_cons, List.sum_cons, expand_face, ih, expansion, moment]
    omega

/-- Write `M k = 30^(k+1)/(k+1)`. The expansion sums to
`M 4 + 6 * M 3 + 11 * M 2 + 6 * M 1`. Its remainder modulo eight is four. -/
private theorem fair_remainder {w : List Die} (h : Fair 30 w) (d : Die) :
    ((suffixes d w).map (score d)).sum % 8 = 4 := by
  rw [sum_scores]
  simp only [fair_moment d _ w h, opponents, List.length_map]
  decide +kernel

/-- Two even numbers two apart modulo four contribute a factor of eight. -/
private theorem eight_dvd_pair (x y : Nat) (even : x % 2 = 0)
    (apart : y % 4 = (x + 2) % 4) : 8 ∣ x * y := by
  by_cases h : 4 ∣ x
  · exact Nat.mul_dvd_mul h (show 2 ∣ y by omega)
  · exact Nat.mul_dvd_mul (show 2 ∣ x by omega) (show 4 ∣ y by omega)

private theorem eight_dvd_face (a b c e : Nat) (hb : a % 4 = b % 4)
    (hc : a % 4 = c % 4) (he : a % 4 = e % 4) :
    8 ∣ a * (b + 1) * (c + 2) * (e + 3) := by
  have regroup : a * (b+1) * (c+2) * (e+3) = (a * (c+2)) * ((b+1) * (e+3)) := by ac_rfl
  rw [regroup]
  by_cases even : a % 2 = 0
  · exact Nat.dvd_mul_right_of_dvd (eight_dvd_pair a (c+2) even (by omega)) _
  · exact Nat.dvd_mul_left_of_dvd (eight_dvd_pair (b+1) (e+3) (by omega) (by omega)) _

private theorem eight_dvd_sum (d : Die) (w : List Die) (hs : SynchronizedModFour d w) :
    8 ∣ ((suffixes d w).map (score d)).sum := by
  induction w with
  | nil => simp [suffixes]
  | cons x w ih =>
    have tail := ih (fun pre post eq => hs (x :: pre) post (by simp [eq]))
    by_cases hx : d = x
    · subst x
      have ne : ∀ d : Die, ∀ i : Fin 4, opponent d i ≠ d := by decide
      have same := fun i => hs [] w rfl (opponent d 0) (opponent d i) (ne d 0) (ne d i)
      have face : 8 ∣ score d w := eight_dvd_face _ _ _ _ (same 1) (same 2) (same 3)
      simpa [suffixes] using Nat.dvd_add face tail
    · simpa [suffixes, hx] using tail

theorem not_fair_of_synchronized_mod_four {d : Die} {w : List Die}
    (hs : SynchronizedModFour d w) : ¬ Fair 30 w := by
  intro fair
  have zero := Nat.dvd_iff_mod_eq_zero.mp (eight_dvd_sum d w hs)
  have four := fair_remainder fair d
  omega

/-- Each die needs a face where two opponents' higher-label counts differ modulo four. -/
theorem needs_distinct_residues {w : List Die} (h : Fair 30 w) (d : Die) :
    ∃ (pre post : List Die) (b c : Die), w = pre ++ d :: post ∧
      b ≠ d ∧ c ≠ d ∧ post.count b % 4 ≠ post.count c % 4 := by
  have obstruction : ¬ SynchronizedModFour d w := fun hs => not_fair_of_synchronized_mod_four hs h
  grind [SynchronizedModFour]

end FiveDice.EqualCuts
