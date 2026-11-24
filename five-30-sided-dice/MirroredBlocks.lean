import FiveDice

namespace FiveDice.Mirrored

private def table : Array (List Die) := rankings.toArray

def perm (i : Fin 120) : List Die := table[i.val]'(by simp [table, rankings_length])
def block (i : Fin 120) : List Die := perm i ++ (perm i).reverse
def word (ps : List (Fin 120)) : List Die := ps.flatMap block

private theorem perm_mem (p : Fin 120) : perm p ∈ rankings := by
  simp [perm, table]

theorem perm_valid (p : Fin 120) : (perm p).length = 5 ∧ (perm p).Nodup :=
  (mem_rankings _).mp (perm_mem p)

/-- Every ordering of the five distinct dice occurs in the block table. -/
theorem exists_perm (r : List Die) (len : r.length = 5) (distinct : r.Nodup) :
    ∃ p : Fin 120, perm p = r := by
  obtain ⟨i, hi, eq⟩ := List.getElem_of_mem ((mem_rankings r).mpr ⟨len, distinct⟩)
  exact ⟨⟨i, by simpa [rankings_length] using hi⟩, by simpa [perm, table] using eq⟩

private def mix (front rest u v : List Die) : Nat :=
  ways front u * ways rest v + match rest with
    | [] => 0
    | a :: r => mix (front ++ [a]) r u v

private theorem mix_head (a x : Die) (s r u v : List Die) :
    mix (a :: s) r (x :: u) v = mix (a :: s) r u v +
      if a = x then mix s r u v else 0 := by
  induction r generalizing s with
  | nil => by_cases h : a = x <;> simp [mix, ways, h]
  | cons b r ih =>
    simp only [mix, ways, List.cons_append, ih]
    split <;> simp [Nat.add_mul] <;> omega

private theorem mix_empty (a : Die) (s r v : List Die) :
    mix (a :: s) r [] v = 0 := by
  induction r generalizing s <;> simp [mix, ways, *]

private theorem split_ways (r u v : List Die) : ways r (u ++ v) = mix [] r u v := by
  induction u generalizing r with
  | nil => cases r <;> simp [mix, mix_empty, ways]
  | cons x u ih =>
    cases r with
    | nil => simp [mix, ways]
    | cons a r =>
      simp only [List.cons_append, ways, ih]
      rw [mix, mix]
      simp only [ways, Nat.one_mul, List.nil_append, mix_head]
      split <;> omega


private theorem one_append (a : Die) (u v : List Die) :
    ways [a] (u ++ v) = ways [a] u + ways [a] v := by
  rw [split_ways]; simp [mix, ways, Nat.add_comm]

private theorem two_append (a b : Die) (u v : List Die) :
    ways [a,b] (u ++ v) = ways [a,b] u + ways [a] u * ways [b] v + ways [a,b] v := by
  rw [split_ways]; simp [mix, ways]; omega

private theorem one_count (a : Die) (w : List Die) : ways [a] w = w.count a := by
  induction w with
  | nil => simp [ways]
  | cons x w ih => by_cases h : a = x <;> simp_all [ways, Ne.symm]

private theorem perm_count (p : Fin 120) (a : Die) : (perm p).count a = 1 := by
  have all : rankings.all (fun r => (List.finRange 5).all (fun d => r.count d == 1)) = true := by
    set_option maxRecDepth 16000 in decide
  simpa [List.all_eq_true] using List.all_eq_true.mp (List.all_eq_true.mp all _ (perm_mem p)) a (by simp)

private theorem pal_two (a b : Die) (ab : a ≠ b) (p : List Die) :
    ways [a,b] (p ++ p.reverse) = 2 * p.count a * p.count b := by
  induction p with
  | nil => simp [ways]
  | cons x p ih =>
    rw [List.reverse_cons]
    simp only [List.cons_append, ← List.append_assoc (as := p), ways, two_append,
      one_count, List.count_append, List.count_reverse, ih]
    by_cases xa : a = x <;> by_cases xb : b = x <;>
      simp_all [Ne.symm] <;> grind

@[simp] private theorem block_one (a : Die) (p : Fin 120) : ways [a] (block p) = 2 := by
  simp [one_count, block, List.count_append, perm_count]

@[simp] private theorem block_two (a b : Die) (ab : a ≠ b) (p : Fin 120) :
    ways [a,b] (block p) = 2 := by simp [block, pal_two _ _ ab, perm_count]

@[simp] private theorem word_one (a : Die) (ps : List (Fin 120)) :
    ways [a] (word ps) = 2 * ps.length := by
  induction ps with
  | nil => simp [word, ways]
  | cons p ps ih => change ways [a] (block p ++ word ps) = _; simp [one_append, ih]; omega

@[simp] private theorem word_two (a b : Die) (ab : a ≠ b) (ps : List (Fin 120)) :
    ways [a,b] (word ps) = 2 * ps.length ^ 2 := by
  induction ps with
  | nil => simp [word, ways]
  | cons p ps ih =>
    change ways [a,b] (block p ++ word ps) = _
    simp [two_append, block_two _ _ ab, ih]
    grind


private def diff (p : Fin 120) (r : List Die) : Int :=
  (countRanking r (block p) : Int) - countRanking r (block 0)

private structure Terms where
  whole : Int
  bcde : Int
  abcd : Int
  cde : Int
  bcd : Int
  abc : Int
deriving Inhabited

private def terms (p r : Fin 120) : Terms :=
  match perm r with
  | [a,b,c,d,e] => ⟨diff p [a,b,c,d,e], diff p [b,c,d,e], diff p [a,b,c,d],
      diff p [c,d,e], diff p [b,c,d], diff p [a,b,c]⟩
  | _ => default

/-- Reuse the six local differences at every block position. -/
private def termTable : Array (Array Terms) :=
  Array.ofFn fun p : Fin 120 => Array.ofFn fun r : Fin 120 => terms p r

def delta (t : Nat) (p r : Fin 120) : Int :=
  let u : Int := (14 - t : Nat)
  let t : Int := t
  let q := termTable[p.val]![r.val]!
  q.whole + 2*t * q.bcde + 2*u * q.abcd + 2*t^2 * q.cde + 4*t*u * q.bcd + 2*u^2 * q.abc

def base (r : Fin 120) : Int :=
  countRanking (perm r) (word (List.replicate 15 0))

private theorem five_shape (l : List Die) (h : l.length = 5) :
    ∃ a b c d e, l = [a,b,c,d,e] := by
  match l with
  | [a,b,c,d,e] => exact ⟨_, _, _, _, _, rfl⟩
  | [] | [_] | [_,_] | [_,_,_] | [_,_,_,_] | _ :: _ :: _ :: _ :: _ :: _ :: _ => simp at h

private theorem replace_one (us vs : List (Fin 120)) (p r : Fin 120)
    (h : us.length + vs.length = 14) :
    (ways (perm r) ((word us ++ block p) ++ word vs) : Int) =
      (ways (perm r) ((word us ++ block 0) ++ word vs) : Int) + delta us.length p r := by
  obtain ⟨a,b,c,d,e,hr⟩ := five_shape _ (perm_valid r).1
  have nodup := (perm_valid r).2
  rw [hr] at nodup
  simp at nodup
  have ab : a ≠ b := by grind
  have bc : b ≠ c := by grind
  have cd : c ≠ d := by grind
  have de : d ≠ e := by grind
  have hu : 14 - us.length = vs.length := by omega
  simp [hr, delta, termTable, terms, diff, countRanking_correct, split_ways, mix, ways, block_two, word_two,
    ab, bc, cd, de, hu, Int.natCast_add, Int.natCast_mul, Int.natCast_pow]
  grind


private theorem replace_cons (us vs : List (Fin 120)) (p r : Fin 120)
    (h : us.length + vs.length = 14) :
    (ways (perm r) (word (us ++ p :: vs)) : Int) =
      (ways (perm r) (word (us ++ 0 :: vs)) : Int) + delta us.length p r := by
  simpa [word, List.flatMap_append, List.append_assoc] using replace_one us vs p r h

private theorem build (us vs : List (Fin 120)) (r : Fin 120)
    (h : us.length + vs.length = 15) :
    (ways (perm r) (word (us ++ vs)) : Int) =
      (ways (perm r) (word (us ++ List.replicate vs.length 0)) : Int) +
        ((vs.zipIdx us.length).map (fun pt => delta pt.2 pt.1 r)).sum := by
  induction vs generalizing us with
  | nil => simp
  | cons p vs ih =>
    have size : us.length + vs.length = 14 := by simp at h; omega
    have hrec := ih (us ++ [p]) (by simp; omega)
    have changeBlock := replace_cons us (List.replicate vs.length 0) p r (by simp [size])
    simp only [List.append_assoc, List.singleton_append, List.length_append, List.length_singleton]
      at hrec
    simp only [List.zipIdx_cons, List.map_cons, List.sum_cons, List.length_cons, List.replicate_succ]
    rw [hrec, changeBlock]
    omega

/-- For a concatenation of fifteen mirrored permutations, contributions from
replacing individual identity blocks add without cross terms. -/
theorem ways_blocks (ps : List (Fin 120)) (hlen : ps.length = 15) (r : Fin 120) :
    (ways (perm r) (word ps) : Int) = base r +
      ((ps.zipIdx).map (fun pt => delta pt.2 pt.1 r)).sum := by
  simpa [base, countRanking_correct, hlen] using build [] ps r (by simp [hlen])

end FiveDice.Mirrored
