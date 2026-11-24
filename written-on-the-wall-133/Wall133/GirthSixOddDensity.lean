import Wall133.GirthSixSharp
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions

/-! # Induced paths through a shortest odd cycle -/
namespace Wall133
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

/-- Shortest odd closed walks also minimize among nonsimple closed walks.
This makes the parity of any shortcut available directly. -/
structure ShortestOddWalk (G : SimpleGraph V) where
  base : V
  walk : G.Walk base base
  odd : walk.length % 2 = 1
  minimal : ∀ v (p : G.Walk v v), p.length % 2 = 1 → walk.length ≤ p.length

theorem exists_shortestOddWalk (h : ¬ G.IsBipartite) : Nonempty (ShortestOddWalk G) := by
  classical
  have hex : ∃ n : ℕ, n % 2 = 1 ∧ ∃ v, ∃ p : G.Walk v v, p.length=n := by
    by_contra! hn
    apply h
    rw [IsBipartite, two_colorable_iff_forall_loop_even]
    intro v p
    exact Nat.even_iff.mpr (by by_contra! he; exact hn _ (by omega) v p rfl)
  let n := Nat.find hex
  obtain ⟨ho,v,p,he⟩ := Nat.find_spec hex
  exact ⟨⟨v,p,he ▸ ho,fun w q hq => he ▸ Nat.find_min' hex ⟨hq,w,q,rfl⟩⟩⟩

namespace ShortestOddWalk
variable (C : ShortestOddWalk G)

private theorem arc_parity {i j : ℕ} (hi : i ≤ j) (hj : j ≤ C.walk.length)
    (p : G.Walk (C.walk.getVert i) (C.walk.getVert j)) :
    ((j-i+p.length)%2=1 → C.walk.length ≤ j-i+p.length) ∧
    ((j-i+p.length)%2=0 → j-i ≤ p.length) := by
  let Q := C.walk
  change j ≤ Q.length at hj
  have ends : (Q.drop i).getVert (j-i) = Q.getVert j := by simp [Nat.add_sub_of_le hi]
  let a := ((Q.drop i).take (j-i)).copy rfl ends
  let b := (Q.take i).reverse.append (Q.drop j).reverse
  have la : a.length=j-i := by simp [a,Walk.take_length,Walk.drop_length]; omega
  have lb : b.length=Q.length-(j-i) := by
    simp only [b,Walk.length_append,Walk.length_reverse,Walk.take_length,Walk.drop_length]
    omega
  constructor
  · intro ho
    have := C.minimal _ (a.append p.reverse)
    simp only [Walk.length_append,Walk.length_reverse,la] at this
    exact this ho
  · intro he
    have hh := C.minimal _ (b.append p.reverse)
    simp only [Walk.length_append,Walk.length_reverse,lb] at hh
    have ho : Q.length%2=1 := C.odd
    change j ≤ Q.length at hj
    have := hh (by omega)
    change Q.length ≤ _ at this
    omega

theorem inj {i j : ℕ} (hi : i < C.walk.length) (hj : j < C.walk.length)
    (he : C.walk.getVert i=C.walk.getVert j) : i=j := by
  have test {i j : ℕ} (hle : i≤j) (hj : j < C.walk.length)
      (he : C.walk.getVert i=C.walk.getVert j) : i=j := by
    let p := (Walk.nil (G:=G) (u:=C.walk.getVert i)).copy rfl he
    have ⟨l,r⟩ := C.arc_parity hle hj.le p
    have len : p.length=0 := by simp [p]
    rw [len] at l r
    omega
  rcases le_total i j with h|h
  · exact test h hj he
  · exact (test h hi he.symm).symm

theorem isCycle : C.walk.IsCycle := by
  have len : 3≤C.walk.length := by
    by_contra! small
    have one : C.walk.length=1 := by have := C.odd; omega
    have a := C.walk.adj_getVert_succ (i:=0) (by omega)
    simp only [Nat.zero_add,←one,C.walk.getVert_length,C.walk.getVert_zero,SimpleGraph.irrefl] at a
  apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
  refine ⟨isPath_of_injective_getVert_le C.walk.tail ?_,len⟩
  intro i j hi hj eq
  rw [Walk.length_tail] at hi hj
  simp only [Walk.getVert_tail] at eq
  let ix (k : ℕ) := if k+1=C.walk.length then 0 else k+1
  have re (k : ℕ) : C.walk.getVert (ix k)=C.walk.getVert (k+1) := by
    dsimp [ix]; split_ifs with h <;> simp [h]
  have ii := C.inj (i:=ix i) (j:=ix j) (by dsimp [ix];split_ifs <;> omega)
    (by dsimp [ix];split_ifs <;> omega) ((re i).trans (eq.trans (re j).symm))
  dsimp [ix] at ii
  split_ifs at ii <;> omega

theorem edge {i j : ℕ} (hi : i≤j) (hj : j<C.walk.length)
    (h : G.Adj (C.walk.getVert i) (C.walk.getVert j)) :
    j=i+1 ∨ i=0 ∧ j+1=C.walk.length := by
  have ⟨l,r⟩ := C.arc_parity hi hj.le h.toWalk
  have len : h.toWalk.length=1 := rfl
  rw [len] at l r
  have ne : i ≠ j := fun e => h.ne (congrArg _ e)
  omega

/-- An outside vertex has at most one neighbor on a shortest odd cycle
in a four-cycle-free graph. -/
theorem private_neighbor (h4 : NoFourCycle G) {w : V}
    (outside : ∀ i<C.walk.length, w≠C.walk.getVert i) {i j : ℕ}
    (hi : i<C.walk.length) (hj : j<C.walk.length)
    (ha : G.Adj w (C.walk.getVert i)) (hb : G.Adj w (C.walk.getVert j)) : i=j := by
  have test {i j : ℕ} (hij : i<j) (hj : j<C.walk.length)
      (ha : G.Adj w (C.walk.getVert i)) (hb : G.Adj w (C.walk.getVert j)) : False := by
    let p := ha.symm.toWalk.append hb.toWalk
    have ⟨l,r⟩ := C.arc_parity hij.le hj.le p
    have len : p.length=2 := by simp [p]
    rw [len] at l r
    have far : j=i+2 ∨ j-i+2=C.walk.length := by have := C.odd; omega
    have middle (k : ℕ) (hk : k<C.walk.length) (hai : G.Adj (C.walk.getVert k) (C.walk.getVert i))
        (hbj : G.Adj (C.walk.getVert k) (C.walk.getVert j)) : False :=
      hij.ne (C.inj (by omega) hj (h4 (outside k hk) ha hai hb hbj))
    rcases far with far|far
    · exact middle (i+1) (by omega) (C.walk.adj_getVert_succ (by omega : i<C.walk.length)).symm
        (far ▸ C.walk.adj_getVert_succ (by omega : i+1<C.walk.length))
    · rcases (show (i=0 ∧ j+2=C.walk.length) ∨ (i=1 ∧ j+1=C.walk.length) by omega) with ⟨rfl,h⟩|⟨rfl,h⟩
      · apply middle (j+1) (by omega) _ (C.walk.adj_getVert_succ hj).symm
        simpa [show j+1+1=C.walk.length by omega] using C.walk.adj_getVert_succ (by omega : j+1<C.walk.length)
      · apply middle 0 (by omega) (C.walk.adj_getVert_succ (by omega : 0<C.walk.length))
        simpa [h] using (C.walk.adj_getVert_succ hj).symm
  rcases lt_trichotomy i j with h|h|h
  · exact (test h hj ha hb).elim
  · exact h
  · exact (test h hi hb ha).elim

variable [Fintype V] [DecidableRel G.Adj]

theorem off_neighbor {i : ℕ} (hi : i<C.walk.length) (hn : 5 ≤ C.walk.length)
    (hd : 3 ≤ G.degree (C.walk.getVert i)) :
    ∃ w, G.Adj w (C.walk.getVert i) ∧ ∀ j<C.walk.length,w≠C.walk.getVert j := by
  classical
  let left := if i=0 then C.walk.length-1 else i-1
  let right := if i+1=C.walk.length then 0 else i+1
  by_contra! hall
  let N := G.neighborFinset (C.walk.getVert i)
  have sub : N ⊆ {C.walk.getVert left,C.walk.getVert right} := by
    intro w hw
    have ha := (G.mem_neighborFinset _ _).1 hw
    obtain ⟨j,hj,rfl⟩ := hall w ha.symm
    have h : j=left ∨ j=right := by
      rcases le_total i j with h|h
      · have := C.edge h hj ha
        dsimp [left,right]
        split_ifs <;> omega
      · have := C.edge h hi ha.symm
        dsimp [left,right]
        split_ifs <;> omega
    rcases h with rfl|rfl <;> simp
  have cnt := Finset.card_le_card sub
  have two := Finset.card_insert_le (C.walk.getVert left) {C.walk.getVert right}
  simp only [Finset.card_singleton] at two
  change (G.neighborFinset (C.walk.getVert i)).card ≤ _ at cnt
  rw [G.card_neighborFinset_eq_degree] at cnt
  omega

variable [DecidableEq V]

/-- In minimum degree three, a shortest odd cycle with n ≥ 7 vertices
supplies an induced path with n+1 vertices. -/
theorem add_one_le_path (h4 : NoFourCycle G) (hn : 7 ≤ C.walk.length)
    (hmin : ∀ v,3 ≤ G.degree v) : C.walk.length+1 ≤ G.path := by
  let L := C.walk.length-2
  let P : Chain G L :=
    { vertex := C.walk.getVert
      inj := fun hi hj => C.inj (by dsimp [L] at *; omega) (by dsimp [L] at *; omega)
      edges := by
        intro i j hi hj
        have hi' : i<C.walk.length := by dsimp [L] at hi; omega
        have hj' : j<C.walk.length := by dsimp [L] at hj; omega
        constructor
        · intro ha
          rcases le_total i j with h|h
          · have := C.edge h hj' ha
            dsimp [L] at *; omega
          · have := C.edge h hi' ha.symm
            dsimp [L] at *; omega
        · rintro (e|e)
          · exact e ▸ C.walk.adj_getVert_succ hi'
          · exact e ▸ (C.walk.adj_getVert_succ hj').symm }
  obtain ⟨x,hx,ox⟩ := C.off_neighbor (i:=0) (by omega) (by omega) (hmin _)
  obtain ⟨y,hy,oy⟩ := C.off_neighbor (i:=L) (by dsimp [L];omega) (by omega) (hmin _)
  have privX {i} (hi : i<C.walk.length) (hw : G.Adj x (C.walk.getVert i)) : i=0 :=
    C.private_neighbor h4 ox hi (by omega) hw hx
  have privY {i} (hi : i<C.walk.length) (hw : G.Adj y (C.walk.getVert i)) : i=L :=
    C.private_neighbor h4 oy hi (by dsimp [L];omega) hw hy
  have xy : x≠y := fun h => by
    have := privY (i:=0) (by omega) (h ▸ hx)
    dsimp [L] at this; omega
  have nonadj : ¬G.Adj x y := by
    intro adj
    let q : G.Walk (C.walk.getVert 0) (C.walk.getVert L) :=
      .cons hx.symm (.cons adj (.cons hy .nil))
    have ⟨l,r⟩ := C.arc_parity (Nat.zero_le _) (show L≤C.walk.length from Nat.sub_le ..) q
    have len : q.length=3 := rfl
    rw [len] at l r
    have := C.odd
    dsimp [L] at *
    omega
  have gx : Good P x := ⟨hx.symm,fun i hi => ox i (by dsimp [L] at hi; omega),
    fun i hi hp he => hp (privX (by dsimp [L] at hi; omega) he)⟩
  let Q := (grow P x gx).reverse
  have gy : Good Q y := by
    have Qv (i) : Q.vertex i=(grow P x gx).vertex (L+1-i) := rfl
    have start : Q.vertex 0=C.walk.getVert L := by simp [Q,grow,Chain.reverse,Chain.prepend,P]
    refine ⟨start ▸ hy.symm,?_,?_⟩
    · intro i hi
      rw [Qv]
      by_cases e : i=L+1
      · simp [e,grow,Chain.prepend,Ne.symm xy]
      · have eq : L+1-i=(L-i)+1 := by omega
        rw [eq]
        exact oy _ (by dsimp [L];omega)
    · intro i hi hpos
      rw [Qv]
      by_cases e : i=L+1
      · simpa [e,grow,Chain.prepend] using (fun he => nonadj (Adj.symm he))
      · have eq : L+1-i=(L-i)+1 := by omega
        rw [eq]
        intro he
        have := privY (i:=L-i) (by dsimp [L];omega) he
        omega
  have := (grow Q y gy).length_le
  dsimp [L] at this
  omega

end ShortestOddWalk
end Wall133
