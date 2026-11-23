import Covering
import Lean

/-!
Local obstructions for the published 27-group cover and the 26-group candidate.
The existence or nonexistence of an unrestricted 26-group cover is a separate question.
-/

namespace Covering61

private abbrev everyone := List.finRange 61

/-- Other people who occur with `x` in some triple still requiring coverage. -/
def requiredPeers (kept : List Nat) (x : Person) : List Person :=
  everyone.filter fun y =>
    x != y && (companions x y kept &&& fullMask) != fullMask

private theorem uncovered_third {x y : Person} {kept : List Nat}
    (h : companions x y kept &&& fullMask ≠ fullMask) :
    ∃ z : Person, ¬ ∃ g ∈ kept, x ∈ members g ∧ y ∈ members g ∧ z ∈ members g := by
  apply Classical.byContradiction
  intro hn
  apply h
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 61
  · have hall : ∃ g ∈ kept, x ∈ members g ∧ y ∈ members g ∧ (⟨i, hi⟩ : Person) ∈ members g := by
      apply Classical.byContradiction
      exact fun hz => hn ⟨⟨i, hi⟩, hz⟩
    have hb := (companions_spec x y ⟨i, hi⟩ kept).mpr hall
    simp_all [Nat.testBit_and, fullMask]
  · simp only [Nat.testBit_and, fullMask, Nat.testBit_two_pow_sub_one, decide_eq_false hi, Bool.and_false]

private theorem peer_covered {kept : List Nat} {A B : List Person}
    (h : ∀ x y z : Person, ∃ g ∈ A :: B :: kept.map members, x ∈ g ∧ y ∈ g ∧ z ∈ g)
    {x y : Person} (hy : y ∈ requiredPeers kept x) :
    (x ∈ A ∧ y ∈ A) ∨ (x ∈ B ∧ y ∈ B) := by
  obtain ⟨_, hxy⟩ := List.mem_filter.mp hy
  simp only [Bool.and_eq_true, bne_iff_ne] at hxy
  have hm : companions x y kept &&& fullMask ≠ fullMask := hxy.2
  obtain ⟨z, hz⟩ := uncovered_third hm
  obtain ⟨g, hg, hx, hy, hh⟩ := h x y z
  rcases List.mem_cons.mp hg with rfl | hg
  · exact Or.inl ⟨hx, hy⟩
  rcases List.mem_cons.mp hg with rfl | hg
  · exact Or.inr ⟨hx, hy⟩
  obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hg
  exact False.elim (hz ⟨m, hm, hx, hy, hh⟩)

/-- Minimum number of seats needed by `x` among two replacement groups of size at most 25. -/
def demand (kept : List Nat) (x : Person) : Nat :=
  let n := (requiredPeers kept x).length
  if n = 0 then 0 else if 24 < n then 2 else 1

private theorem closed_peers_nodup (kept : List Nat) (x : Person) :
    (x :: requiredPeers kept x).Nodup := by
  apply List.nodup_cons.mpr
  refine ⟨?_, (List.nodup_finRange 61).filter _⟩
  simp [requiredPeers]

private theorem demand_le_seats {kept : List Nat} {A B : List Person}
    (ha : A.length ≤ 25) (hb : B.length ≤ 25)
    (h : ∀ x y z : Person, ∃ g ∈ A :: B :: kept.map members, x ∈ g ∧ y ∈ g ∧ z ∈ g)
    (x : Person) :
    demand kept x ≤ (if x ∈ A then 1 else 0) + (if x ∈ B then 1 else 0) := by
  let ns := requiredPeers kept x
  have edge : ∀ y ∈ ns, (x ∈ A ∧ y ∈ A) ∨ (x ∈ B ∧ y ∈ B) := fun _ hy => peer_covered h hy
  change (if ns.length = 0 then 0 else if 24 < ns.length then 2 else 1) ≤ _
  by_cases hz : ns.length = 0
  · simp [hz]
  have ⟨y, hy⟩ := List.length_pos_iff_exists_mem.mp (Nat.pos_of_ne_zero hz)
  by_cases xa : x ∈ A <;> by_cases xb : x ∈ B
  · simp [xa, xb, hz]; split <;> decide
  · have sub : x :: ns ⊆ A := by
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact xa
      · exact ((edge _ hv).resolve_right (fun e => xb e.1)).2
    have len := (closed_peers_nodup kept x).length_le_of_subset sub
    change ns.length + 1 ≤ A.length at len
    have small : ¬ 24 < ns.length := by omega
    simp [hz, small, xa, xb]
  · have sub : x :: ns ⊆ B := by
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact xb
      · exact ((edge _ hv).resolve_left (fun e => xa e.1)).2
    have len := (closed_peers_nodup kept x).length_le_of_subset sub
    change ns.length + 1 ≤ B.length at len
    have small : ¬ 24 < ns.length := by omega
    simp [hz, small, xa, xb]
  · rcases edge y hy with h | h
    · exact False.elim (xa h.1)
    · exact False.elim (xb h.1)

private theorem total_seats {kept : List Nat} {A B : List Person}
    (ha : A.length ≤ 25) (hb : B.length ≤ 25)
    (h : ∀ x y z : Person, ∃ g ∈ A :: B :: kept.map members, x ∈ g ∧ y ∈ g ∧ z ∈ g) :
    (everyone.map (demand kept)).sum ≤ 50 := by
  have aux (xs : List Person) : (xs.map (demand kept)).sum ≤
      (xs.filter (fun x => decide (x ∈ A))).length + (xs.filter (fun x => decide (x ∈ B))).length := by
    induction xs with
    | nil => simp
    | cons x xs ih =>
      have hx := demand_le_seats ha hb h x
      by_cases xa : x ∈ A <;> by_cases xb : x ∈ B <;>
        simp_all only [List.map_cons, List.sum_cons, List.filter_cons, decide_true, decide_false,
          ite_true, ite_false, Bool.false_eq_true, List.length_cons] <;> omega
  have sub (g : List Person) : (everyone.filter (fun x => decide (x ∈ g))).length ≤ g.length :=
    List.Nodup.length_le_of_subset ((List.nodup_finRange 61).filter _) (fun _ hx => of_decide_eq_true (List.mem_filter.mp hx).2)
  have := aux everyone
  have := sub A
  have := sub B
  omega

/-- Keep the original groups except the two at the given zero-based positions. -/
def retained (i j : Fin 26) : List Nat :=
  (candidate.erase candidate[i.val]!).erase candidate[j.val]!

def neededSeats (i j : Fin 26) : Nat :=
  (everyone.map (demand (retained i j))).sum


private abbrev Kind := Fin 26
private abbrev Cut := Fin 28
set_option maxHeartbeats 800000
set_option maxRecDepth 16000

/-- People with the same incidence signature have identical group memberships. -/
private def incidence (x : Person) : Nat :=
  (List.finRange 26).foldl (fun m b =>
    if candidate[b.val]!.testBit x.val then m ||| (1 <<< b.val) else m) 0

private def signatures := everyone.map incidence
private def classes := signatures.eraseDups
private def sigTable : Array Nat := by_elab return Lean.toExpr classes.toArray
private def signature (a : Kind) := sigTable[a.val]!
private def tagArray : Array Kind := by_elab
  return Lean.toExpr <| signatures.toArray.map fun s => Fin.ofNat 26 (classes.idxOf s)
private def kind (x : Person) := tagArray[x.val]!
private def repArray : Array Person := by_elab
  return Lean.toExpr <| classes.toArray.map fun s => Fin.ofNat 61 (signatures.idxOf s)
private def repOf (a : Kind) := repArray[a.val]!

private def alive (d : Cut) : Nat :=
  let deleted := if d.val = 26 then (1 <<< 5) ||| (1 <<< 10)
    else if d.val = 27 then (1 <<< 7) ||| (1 <<< 21) else 1 <<< d.val
  (2^26 - 1) ^^^ deleted

/-- Materialize the peer masks once. Each proposed edge is checked separately by certEdges. -/
private def makeNeighbors (d : Cut) (a : Kind) : Nat :=
  (List.finRange 26).foldl (fun mask b =>
    if a != b && (List.finRange 26).any (fun z =>
        (signature a &&& signature b &&& signature z &&& alive d) == 0)
    then mask ||| (1 <<< b.val) else mask) 0
private def neighborTables : Array (Array Nat) := by_elab
  return Lean.toExpr <| Array.ofFn fun (d : Cut) => Array.ofFn (makeNeighbors d)
private def neighbors (d : Cut) (a : Kind) : Nat := neighborTables[d.val]![a.val]!

private theorem signature_spec (b : Fin 26) (x : Person) :
    candidate[b.val]!.testBit x.val = (signature (kind x)).testBit b.val := by
  have cert : ∀ a : Fin 26, ∀ y : Person, candidate[a.val]!.testBit y.val =
      (signature (kind y)).testBit a.val := by decide +kernel
  exact cert b x
private theorem rep_kind (a : Kind) : kind (repOf a) = a := by
  have cert : ∀ a : Kind, kind (repOf a) = a := by decide +kernel
  exact cert a
private def leftCut (i j : Fin 26) : Cut :=
  if i.val = 5 ∧ j.val = 10 then 26 else if i.val = 7 ∧ j.val = 21 then 27 else i.castLE (by decide)
private def rightCut (i j : Fin 26) : Cut :=
  if i.val = 5 ∧ j.val = 10 then 26 else if i.val = 7 ∧ j.val = 21 then 27 else j.castLE (by decide)

private def edgeOK (d : Cut) : Prop := ∀ a b : Kind,
    (neighbors d a).testBit b.val = true → a ≠ b ∧
      (List.finRange 26).any (fun z => (signature a &&& signature b &&& signature z &&& alive d) == 0) = true
private instance (d : Cut) : Decidable (edgeOK d) := by unfold edgeOK; infer_instance
private theorem certEdges : ∀ d : Cut, edgeOK d := by
  iterate 28 refine Fin.cases (by as_aux_lemma => decide +kernel) ?_
  exact fun i => i.elim0

private theorem code_alive (i j k : Fin 26) (ki : k ≠ i) (kj : k ≠ j) :
    (alive (leftCut i j)).testBit k.val = true ∧ (alive (rightCut i j)).testBit k.val = true := by
  have cert : ∀ i j k : Fin 26, k ≠ i → k ≠ j →
    (alive (leftCut i j)).testBit k.val = true ∧ (alive (rightCut i j)).testBit k.val = true := by decide +kernel
  exact cert i j k ki kj
private theorem group_index {g : Nat} (hg : g ∈ candidate) :
    ∃ k : Fin 26, candidate[k.val]! = g := by
  have cert : candidate.all (fun c => (List.finRange 26).any (fun k => candidate[k.val]! == c)) = true := by decide +kernel
  obtain ⟨k, _, eq⟩ := List.any_eq_true.mp (List.all_eq_true.mp cert g hg)
  exact ⟨k, eq_of_beq eq⟩
private def unionMask (i j : Fin 26) (a : Kind) : Nat :=
  neighbors (leftCut i j) a ||| neighbors (rightCut i j) a
private def peerList (mask : Nat) : List Person :=
  everyone.filter (fun y => mask.testBit (kind y).val)

private theorem peer_subset (i j : Fin 26) (x : Person) :
    peerList (unionMask i j (kind x)) ⊆ requiredPeers (retained i j) x := by
  intro y hy
  have he := (List.mem_filter.mp hy).2
  change (neighbors (leftCut i j) (kind x) ||| neighbors (rightCut i j) (kind x)).testBit (kind y).val = true at he
  simp only [Nat.testBit_or, Bool.or_eq_true] at he
  have locate (d : Cut) (h : (neighbors d (kind x)).testBit (kind y).val = true)
      (live : ∀ k : Fin 26, k ≠ i → k ≠ j → (alive d).testBit k.val = true) : y ∈ requiredPeers (retained i j) x := by
    have ⟨hne, existsZ⟩ := certEdges d (kind x) (kind y) h
    obtain ⟨z, _, hz⟩ := List.any_eq_true.mp existsZ
    apply List.mem_filter.mpr
    refine ⟨List.mem_finRange y, ?_⟩
    simp only [Bool.and_eq_true, bne_iff_ne]
    refine ⟨fun eq => hne (congrArg kind eq), ?_⟩
    intro heq
    have hbit := congrArg (fun n : Nat => n.testBit (repOf z).val) heq
    have fullBit : fullMask.testBit (repOf z).val = true := by
      change (2^61-1 : Nat).testBit (repOf z).val = true
      rw [Nat.testBit_two_pow_sub_one]
      exact decide_eq_true (repOf z).isLt
    simp only [Nat.testBit_and, fullBit, Bool.and_true] at hbit
    obtain ⟨g, hg, hx, hy, hh⟩ := (companions_spec x y (repOf z) (retained i j)).mp hbit
    have hd : candidate.Nodup := by decide +kernel
    obtain ⟨ngj, hfirst⟩ := (hd.erase candidate[i.val]!).mem_erase_iff.mp hg
    obtain ⟨ngi, hmem⟩ := hd.mem_erase_iff.mp hfirst
    obtain ⟨k, rfl⟩ := group_index hmem
    have ka : k ≠ i := by intro e; exact ngi (by rw [e])
    have kb : k ≠ j := by intro e; exact ngj (by rw [e])
    have bad := congrArg (fun n : Nat => n.testBit k.val) (eq_of_beq hz)
    have xx := (signature_spec k x).symm.trans ((mem_members _ _).mp hx)
    have yy := (signature_spec k y).symm.trans ((mem_members _ _).mp hy)
    have zz := (signature_spec k (repOf z)).symm.trans ((mem_members _ _).mp hh)
    rw [rep_kind] at zz
    simp [Nat.testBit_and, xx, yy, zz, live k ka kb] at bad
  rcases he with h | h
  · exact locate _ h (fun k hi hj => (code_alive i j k hi hj).1)
  · exact locate _ h (fun k hi hj => (code_alive i j k hi hj).2)

private def demandOf (n : Nat) := if n = 0 then 0 else if 24 < n then 2 else 1
private def estimate (i j : Fin 26) (x : Person) :=
  demandOf (peerList (unionMask i j (kind x))).length

private theorem estimate_le (i j : Fin 26) (x : Person) :
    estimate i j x ≤ demand (retained i j) x := by
  have le := List.Nodup.length_le_of_subset (l₁ := peerList (unionMask i j (kind x))) ((List.nodup_finRange 61).filter _) (peer_subset i j x)
  change demandOf _ ≤ demandOf _
  unfold demandOf
  repeat' split
  all_goals omega

private theorem sum_mono_nat (xs : List Person) (f g : Person → Nat) (h : ∀ x, f x ≤ g x) :
    (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons]; exact Nat.add_le_add (h x) ih

private def weighted (f : Kind → Nat) := (tagArray.toList.map f).sum

private theorem weighted_eq (f : Kind → Nat) :
    (everyone.map (fun x => f (kind x))).sum = weighted f := by
  have tags : everyone.map kind = tagArray.toList := by decide +kernel
  change (everyone.map (f ∘ kind)).sum = _
  rw [← List.map_map, tags]
  rfl

private theorem filtered_length (xs : List Person) (m : Nat) :
    (xs.filter (fun y => m.testBit (kind y).val)).length =
    (xs.map (fun y => if m.testBit (kind y).val then 1 else 0)).sum := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    cases e : m.testBit (kind y).val <;> simp [e, ih, Nat.add_comm]

private def degree (m : Nat) := weighted (fun b => if m.testBit b.val then 1 else 0)
private theorem peerCount (m : Nat) : (peerList m).length = degree m :=
  (filtered_length everyone m).trans (weighted_eq (fun b => if m.testBit b.val then 1 else 0))

private def lowerRow (i : Fin 26) : Prop := ∀ j : Fin 26, i < j →
    52 ≤ weighted (fun a => demandOf (degree (unionMask i j a)))
private instance (i : Fin 26) : Decidable (lowerRow i) := by unfold lowerRow; infer_instance
private theorem certRow : ∀ d : Fin 26, lowerRow d := by
  iterate 26 refine Fin.cases (by as_aux_lemma => decide +kernel) ?_
  exact fun i => i.elim0

private theorem estimated_lower (i j : Fin 26) (h : i < j) :
    52 ≤ (everyone.map (estimate i j)).sum := by
  have eq (x : Person) : estimate i j x = demandOf (degree (unionMask i j (kind x))) := by simp [estimate, peerCount]
  rw [List.map_congr_left (fun _ _ => eq _), weighted_eq (fun a => demandOf (degree (unionMask i j a)))]
  exact certRow i j h

theorem all_two_group_demands : ∀ i j : Fin 26, i < j → 52 ≤ neededSeats i j := by
  intro i j h
  exact Nat.le_trans (estimated_lower _ _ h) (sum_mono_nat _ _ _ (estimate_le i j))

theorem no_two_group_repair (i j : Fin 26) (hij : i < j) (A B : List Person)
    (ha : A.length ≤ 25) (hb : B.length ≤ 25) :
    ¬ ∀ a b c : Person, ∃ g ∈ A :: B :: (retained i j).map members, a ∈ g ∧ b ∈ g ∧ c ∈ g := by
  intro cover
  exact (by decide : ¬ 52 ≤ 50) (Nat.le_trans (all_two_group_demands i j hij) (total_seats ha hb cover))


/-- These are the 24 retained groups when three distinct published positions are removed. -/
def keptPublished (i j k : Fin 27) : List Nat :=
  ((published.erase published[i.val]!).erase published[j.val]!).erase published[k.val]!

private theorem published_two_seat_bound : ∀ i j k : Fin 27, i < j → j < k →
    50 < (List.map (demand (keptPublished i j k)) (List.finRange 61)).sum := by
  native_decide

/-- Keeping any 24 published groups and adjoining two arbitrary groups of at most 25 fails. -/
theorem no_published_three_for_two (i j k : Fin 27) (hij : i < j) (hjk : j < k)
    (A B : List Person) (ha : A.length ≤ 25) (hb : B.length ≤ 25) :
    ¬ ∀ a b c : Person, ∃ g ∈ A :: B :: (keptPublished i j k).map members,
      a ∈ g ∧ b ∈ g ∧ c ∈ g := by
  intro h
  exact (Nat.not_lt_of_ge (total_seats ha hb h)) (published_two_seat_bound i j k hij hjk)

/-- Exchange two people in a group. -/
def swapPeople (p q x : Person) : Person :=
  if x = p then q else if x = q then p else x

private theorem undoSwap (p q x : Person) : swapPeople p q (swapPeople p q x) = x := by
  by_cases hp : p = q
  · subst q
    by_cases hx : x = p <;> simp [swapPeople, hx]
  · by_cases hx : x = p
    · subst x
      simp [swapPeople, Ne.symm hp]
    · by_cases hy : x = q
      · subst x
        simp [swapPeople, Ne.symm hp]
      · simp [swapPeople, hx, hy]

private theorem memBeforeSwap {p q x : Person} {g : List Person}
    (hx : x ∈ g.map (swapPeople p q)) : swapPeople p q x ∈ g := by
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
  simpa [undoSwap] using ha

private abbrev Triple := Person × Person × Person

/-- The helper pairs have one-based labels (2,3), (31,42) and (8,20).
    Pairing each with 34 and 45 gives six of the 84 uncovered triples. -/
private def sixHoles : List Triple :=
  [(33, 1, 2), (44, 1, 2), (33, 30, 41), (44, 30, 41), (33, 7, 19), (44, 7, 19)]

private def swapTriple (p q : Person) (t : Triple) : Triple :=
  (swapPeople p q t.1, swapPeople p q t.2.1, swapPeople p q t.2.2)

private theorem holesAbsent {t : Triple} (ht : t ∈ sixHoles) {g : Nat} (hg : g ∈ candidate) :
    ¬ (t.1 ∈ members g ∧ t.2.1 ∈ members g ∧ t.2.2 ∈ members g) := by
  have cert : sixHoles.all (fun u => !(companions u.1 u.2.1 candidate).testBit u.2.2.val) = true := by
    decide +kernel
  intro covered
  have h := (companions_spec t.1 t.2.1 t.2.2 candidate).mpr ⟨g, hg, covered⟩
  have absent := List.all_eq_true.mp cert t ht
  simp [h] at absent

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem survivesSwap (p q : Person) :
    ∃ t ∈ sixHoles, swapTriple p q t ∈ sixHoles := by
  have h : ∀ a b : Person, sixHoles.any (fun t => decide (swapTriple a b t ∈ sixHoles)) = true := by
    decide +kernel
  obtain ⟨t, ht, h'⟩ := List.any_eq_true.mp (h p q)
  exact ⟨t, ht, of_decide_eq_true h'⟩

/-- For any fixed pair of people, independently exchanging those two labels in any
    choice of the candidate's groups leaves at least one triple uncovered. -/
theorem no_two_person_repair (p q : Person) (groups : List (List Person))
    (variants : ∀ g ∈ groups, ∃ mask ∈ candidate,
      g = members mask ∨ g = (members mask).map (swapPeople p q)) :
    ¬ IsCover 26 groups := by
  intro h
  obtain ⟨t, ht, hst⟩ := survivesSwap p q
  obtain ⟨g, hg, ha, hb, hc⟩ := h.2.2.2 t.1 t.2.1 t.2.2
  obtain ⟨mask, hm, hunchanged | hchanged⟩ := variants g hg
  · subst g
    exact holesAbsent ht hm ⟨ha, hb, hc⟩
  · subst g
    exact holesAbsent hst hm ⟨memBeforeSwap ha, memBeforeSwap hb, memBeforeSwap hc⟩


/-- Coverage of only triples of pairwise distinct people. -/
def CoversDistinct (groups : List (List Person)) : Prop :=
  ∀ a b c : Person, a ≠ b → a ≠ c → b ≠ c →
    ∃ g ∈ groups, a ∈ g ∧ b ∈ g ∧ c ∈ g

private def differentFrom (a b : Person) : Person :=
  if a != 0 && b != 0 then 0 else if a != 1 && b != 1 then 1 else 2

private theorem differentFrom_spec : ∀ a b : Person,
    a ≠ differentFrom a b ∧ b ≠ differentFrom a b := by decide +kernel

theorem coversDistinct_iff (groups : List (List Person)) :
    CoversDistinct groups ↔
      ∀ a b c : Person, ∃ g ∈ groups, a ∈ g ∧ b ∈ g ∧ c ∈ g := by
  constructor
  · intro h
    have pairNe (x y : Person) (hn : x ≠ y) : ∃ g ∈ groups, x ∈ g ∧ y ∈ g := by
      obtain ⟨g, hg, hx, hy, _⟩ := h x y _ hn (differentFrom_spec x y).1 (differentFrom_spec x y).2
      exact ⟨g, hg, hx, hy⟩
    have pair (x y : Person) : ∃ g ∈ groups, x ∈ g ∧ y ∈ g := by
      by_cases hxy : x = y
      · subst y
        obtain ⟨g, hg, hx, _⟩ := pairNe x _ (differentFrom_spec x x).1
        exact ⟨g, hg, hx, hx⟩
      · exact pairNe x y hxy
    intro a b c
    by_cases hab : a = b
    · subst b
      obtain ⟨g, hg, ha, hc⟩ := pair a c
      exact ⟨g, hg, ha, ha, hc⟩
    by_cases hac : a = c
    · subst c
      obtain ⟨g, hg, ha, hb⟩ := pair a b
      exact ⟨g, hg, ha, hb, ha⟩
    by_cases hbc : b = c
    · subst c
      obtain ⟨g, hg, ha, hb⟩ := pair a b
      exact ⟨g, hg, ha, hb, hb⟩
    exact h a b c hab hac hbc
  · exact fun h a b c _ _ _ => h a b c

theorem no_two_group_repair_distinct (i j : Fin 26) (hij : i < j) (A B : List Person)
    (ha : A.length ≤ 25) (hb : B.length ≤ 25) :
    ¬ CoversDistinct (A :: B :: (retained i j).map members) :=
  fun h => no_two_group_repair i j hij A B ha hb ((coversDistinct_iff _).mp h)

theorem no_published_three_for_two_distinct (i j k : Fin 27) (hij : i < j) (hjk : j < k)
    (A B : List Person) (ha : A.length ≤ 25) (hb : B.length ≤ 25) :
    ¬ CoversDistinct (A :: B :: (keptPublished i j k).map members) :=
  fun h => no_published_three_for_two i j k hij hjk A B ha hb ((coversDistinct_iff _).mp h)

end Covering61
