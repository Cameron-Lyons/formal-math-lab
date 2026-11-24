import MaxKey
import Simple.LeaderOfLaw
import Simple.Pack
import Moves
import SymmetryCore

namespace E1486.Simple
open Encoding Symmetry

private noncomputable def adj (m : Operation) (a b : V) : Bool :=
  (pack (arrows m)).getLsbD (15*a.val+b.val)

private theorem adj_pull (l : Label 15) (m : Operation) (a b : V) :
    adj (l.pull m) a b = adj m (l.old a) (l.old b) := by
  apply Bool.eq_iff_iff.mpr
  simp only [adj,pack_get,Test.arrows_pull]

private theorem len_score (k : Nat) (m n : Operation) :
    (score k (adj m)).length = (score k (adj n)).length := by
  simp [score,matrix,profile,List.length_flatMap]

private theorem range_sv (k : Nat) (h : k≤15) : (sv k).map Fin.val = List.range k := by
  have all : ∀ k : Fin 16, (sv k.val).map Fin.val = List.range k.val := by decide
  exact all ⟨k,by omega⟩

private theorem mx_congr {k : Nat} {r s : V → V → Bool}
    (hf : ∀ a b, a.val < k → b.val < k → r a b = s a b) : matrix k r = matrix k s := by
  unfold matrix
  simp only [List.flatMap_def]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro a ha
  apply List.map_congr_left
  intro b hb
  exact hf a b (of_decide_eq_true (List.mem_filter.mp ha).2) (of_decide_eq_true (List.mem_filter.mp hb).2)

private theorem prof_congr {k : Nat} {r s : V → V → Bool} {a b : V}
    (h₁ : ∀ q : V, q.val < k → r q a = s q b)
    (h₂ : ∀ q : V, q.val < k → r a q = s b q) : profile k r a = profile k s b := by
  unfold profile
  congr 1 <;> apply List.map_congr_left <;> intro q hq
  · exact h₁ q (of_decide_eq_true (List.mem_filter.mp hq).2)
  · exact h₂ q (of_decide_eq_true (List.mem_filter.mp hq).2)

private theorem ns_order {k j : Nat} {m : Operation} (law : Law m) (hn : DiagNormal m k j)
    (hm : ∀ m' : Operation, Law m' → DiagNormal m' k j → score k (adj m') ≤ score k (adj m))
    (a : V) (lo : k≤a.val) (hi : a.val+1<15) :
    Finite.geBits (pack (arrows m)) (Finite.nonSq k a.val) = true := by
  let p := nsLabel hn a lo hi
  have prior := hm (p.pull m) (p.law law) (nsLabel_normal hn a lo hi)
  have hb (v : V) (h : v.val < a.val) : p.old v = v := by
    change swap a (a+1) v = v
    have before : ∀ a v : V, a.val+1<15 → v.val<a.val → swap a (a+1) v=v := by decide
    exact before a v hi h
  have ha : p.old a = a+1 := by change swap a (a+1) a = _; simp [swap]
  have hp (v : V) : profile k (adj (p.pull m)) v = profile k (adj m) (p.old v) := by
    apply prof_congr <;> intro q hq <;> rw [adj_pull, hb q (by omega)]
  have he := swapped_profile_le (a := a) prior (mx_congr (by
    intro x y hx hy; rw [adj_pull, hb x (by omega), hb y (by omega)]))
    (fun v hv => (hp v).trans (by rw [hb v hv]))
  rw [hp,ha] at he
  apply Test.geBits_of_le
  have hav : (a+1 : V).val=a.val+1 := by rw [Fin.val_add];exact Nat.mod_eq_of_lt hi
  have adj_eta (u : V) : adj m u = fun x => (pack (arrows m)).getLsbD (15*u.val + x.val) := rfl
  simpa [adj_eta,Finite.nonSq, ← range_sv k hn.le_size, profile,adj,List.map_map,Function.comp_def, hav,Nat.add_assoc] using he

private def moveKind (j a b : Nat) : Nat := if b<j then 0 else if b=a+1 then 1 else 2
private def eligible (j a b : Nat) : Prop := b<j ∨ (j≤a ∧ (a-j)%2=0 ∧ (b=a+1 ∨ (b-j)%2=0))
private instance (j a b : Nat) : Decidable (eligible j a b) := by unfold eligible;infer_instance

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem bounded_moves : ∀ (k j : Fin 16) (a b : V), j.val≤k.val → a<b → b.val<k.val →
    eligible j.val a.val b.val → (moveKind j.val a.val b.val,a,b) ∈ sqMoves k.val j.val := by decide +kernel

private def moveNat (kind a b : Nat) := if kind=2 then fun x => Finite.swap a b (Finite.swap (a+1) (b+1) x)
  else Finite.swap a b

private theorem move_agrees (h : Nat × V × V) (he : h.2.1.val + 1 < 15 ∧ h.2.2.val + 1 < 15 ∨ h.1≠2) :
    ∀ x : V, (perm h.1 h.2.1 h.2.2 x).val = moveNat h.1 h.2.1.val h.2.2.val x.val := by
  obtain ⟨kind,a,b⟩ := h
  have sw (a b x : V) : (swap a b x).val = Finite.swap a.val b.val x.val := by
    simp [swap,Finite.swap,Fin.ext_iff]; split <;> (try split) <;> simp_all
  intro x
  by_cases m : kind = 2
  · have ⟨h₁,h₂⟩ := he.resolve_right (by simpa using m)
    simp only [perm,moveNat,m,ite_true,sw]
    change a.val+1<15 at h₁;change b.val+1<15 at h₂
    rw [Fin.val_add,Fin.val_add]; simp [Nat.mod_eq_of_lt h₁,Nat.mod_eq_of_lt h₂]
  · simp [perm,moveNat,m,sw]

private theorem sq_order {k j : Nat} {m : Operation} (law : Law m) (hn : DiagNormal m k j)
    (hm : ∀ m' : Operation, Law m' → DiagNormal m' k j → score k (adj m') ≤ score k (adj m))
    (a b : V) (hab : a<b) (hb : b.val<k) (ok : eligible j a.val b.val) :
    Finite.geBits (pack (arrows m)) (Finite.sqBits k (moveNat (moveKind j a.val b.val) a.val b.val)) = true := by
  let h := (moveKind j a.val b.val,a,b)
  have hh : h∈sqMoves k j := bounded_moves ⟨k,by have := hn.le_size;omega⟩
    ⟨j,by have := hn.le_size;have := hn.le_squares;omega⟩ a b hn.le_squares hab hb ok
  let p := sqLabel hn hh
  have eq : ∀ x : V, (p.old x).val = moveNat h.1 h.2.1.val h.2.2.val x.val := by
    apply move_agrees
    by_cases t : h.1=2
    · left; have hk := hn.le_size;have hp := hn.parity
      change (if b.val<j then 0 else if b.val=a.val+1 then 1 else 2)=2 at t
      have ja : j ≤ a.val := by unfold eligible at ok; split at t <;> grind
      have jb : j ≤ b.val := by change a.val<b.val at hab;omega
      have even : (b.val-j)%2=0 := by unfold eligible at ok; split at t <;> (try contradiction); split at t <;> grind
      have bound : b.val+1<15 := by omega
      change a.val+1<15 ∧ b.val+1<15; change a.val<b.val at hab;omega
    · exact Or.inr t
  have he := matrix_le (hm (p.pull m) (p.law law) (sqLabel_normal hn hh))
  have rel (x y : V) : adj (p.pull m) x y = (pack (arrows m)).getLsbD
      (15*moveNat (moveKind j a.val b.val) a.val b.val x.val + moveNat (moveKind j a.val b.val) a.val b.val y.val) := by
    rw [adj_pull]; change (pack (arrows m)).getLsbD (15*(p.old x).val+(p.old y).val) = _
    rw [eq x,eq y]
  apply Test.geBits_of_le
  simp only [Finite.sqBits, ← range_sv k hn.le_size, List.map_flatMap,List.flatMap_map,
    List.map_map,Function.comp_def]
  have fn := funext (fun x => funext (rel x))
  rw [fn] at he
  exact he

theorem exists_ordered {m : Operation} (h : Law m) :
    ∃ m' k j, Law m' ∧ DiagNormal m' k j ∧ Finite.ordered k j (pack (arrows m')) = true := by
  obtain ⟨m,k,j,hl,hn⟩ := normalize_diagonal h
  obtain ⟨m',⟨hl,hn⟩,hm⟩ := exists_max_key (fun u : Operation => Law u ∧ DiagNormal u k j)
    (fun u => score k (adj u)) _ (fun u => len_score k u m) ⟨m,hl,hn⟩
  let H := fun (u : Operation) (hu : Law u) (du : DiagNormal u k j) => hm u ⟨hu,du⟩
  refine ⟨m',k,j,hl,hn,?_⟩
  simp only [Finite.ordered, Bool.and_eq_true, List.all_eq_true, List.mem_range]
  constructor
  · intro i hi
    exact ns_order hl hn H ⟨k+i,by omega⟩ (by simp) (by simp;omega)
  · intro b hb a ha
    let A : V := ⟨a,by have := hn.le_size;omega⟩
    let B : V := ⟨b,by have := hn.le_size;omega⟩
    have run := sq_order hl hn H A B (show A<B from ha) hb
    change eligible j a b → _ at run
    split
    · rename_i h0
      have e : eligible j a b := by simp [eligible] at *; grind
      have use := run e
      have ne : moveKind j a b ≠2 := by simp [moveKind] at *;grind
      simpa [moveNat,ne,A,B] using use
    · split
      · rename_i h1
        have e : eligible j a b := by simp [eligible] at *;grind
        have use := run e
        have is : moveKind j a b = 2 := by simp [moveKind] at *;grind
        simpa [moveNat,is,A,B] using use
      · rfl

end E1486.Simple
