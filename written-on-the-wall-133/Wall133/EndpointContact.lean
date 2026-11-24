import Wall133.NearSaturation

namespace Wall133
open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {n : ℕ}

private structure Avoids (P : Chain G n) (x : V) : Prop where
  fresh : ∀ i ≤ n, x ≠ P.vertex i
  clean : ∀ i ≤ n, ¬ G.Adj x (P.vertex i)

private theorem avoids_grow {P : Chain G n} {x y : V} (hx : Good P x)
    (hy : Avoids P y) (hn : y ≠ x) (ha : ¬ G.Adj y x) : Avoids (grow P x hx) y := by
  constructor
  · rintro (_|i) hi
    · exact hn
    · exact hy.fresh i (by omega)
  · rintro (_|i) hi
    · exact ha
    · exact hy.clean i (by omega)

private theorem good_grow {P : Chain G n} {x y : V} (hx : Good P x)
    (hy : Avoids P y) (ha : G.Adj x y) : Good (grow P x hx) y := by
  refine ⟨ha, ?_, ?_⟩
  · rintro (_|i) hi
    · exact ha.ne.symm
    · exact hy.fresh i (by omega)
  · rintro (_|i) hi hne
    · contradiction
    · exact hy.clean i (by omega)

private def from_two (P : Chain G n) (hn : 2 ≤ n) : Chain G (n-2) where
  vertex i := P.vertex (i+2)
  inj := by
    intro i j hi hj he
    have := P.inj (by omega) (by omega) he
    omega
  edges := by intro i j hi hj; rw [P.edges (by omega) (by omega)]; omega

/-- A private contact at either end of the subpath from vertex 2 to vertex n
allows the other clean neighbor to begin a path on n+4 vertices. -/
theorem path_of_private_end [Fintype V] [DecidableEq V] (P : Chain G n)
    (c : G.Coloring (Fin 2)) (h4 : NoFourCycle G) (hn : 2 ≤ n) {x y z b : V}
    (hx : Good P x) (hy : Good P y) (hxy : x ≠ y) (hz : Good (grow P x hx) z)
    (hzb : G.Adj z b) (j : ℕ) (hj : j = 2 ∨ j = n)
    (hbf : ∀ i ≤ n, b ≠ P.vertex i) (hba : ∀ i ≤ n, G.Adj b (P.vertex i) ↔ i=j) :
    n+4 ≤ G.path := by
  let i₀ (i : ℕ) := if j=2 then i+2 else n-i
  let T := if j=2 then from_two P hn else (from_two P hn).reverse
  have hT (i : ℕ) (hi : i ≤ n-2) : T.vertex i = P.vertex (i₀ i) := by
    dsimp [T,i₀]
    split_ifs
    · rfl
    · change P.vertex (n-2-i+2) = P.vertex (n-i)
      congr 1; omega
  have bounds (i : ℕ) (hi : i ≤ n-2) : 2 ≤ i₀ i ∧ i₀ i ≤ n := by
    dsimp [i₀]; split_ifs <;> omega
  have root (i : ℕ) (hi : i ≤ n-2) : i₀ i=j ↔ i=0 := by
    dsimp [i₀]; split_ifs <;> omega
  have hb : Good T b := by
    refine ⟨?_, fun i hi => hT i hi ▸ hbf _ (bounds i hi).2, ?_⟩
    · rw [hT 0 (by omega)]
      exact ((hba _ (bounds 0 (by omega)).2).2 ((root 0 (by omega)).2 rfl)).symm
    · intro i hi hpos ha
      rw [hT i hi] at ha
      exact hpos ((root i hi).1 ((hba _ (bounds i hi).2).1 ha))
  have good_avoids {u : V} (hu : Good P u) : Avoids T u := by
    constructor
    · intro i hi; rw [hT i hi]; exact hu.2.1 _ (bounds i hi).2
    · intro i hi; rw [hT i hi]; exact hu.2.2 _ (bounds i hi).2 (by have := bounds i hi; omega)
  have zT : Avoids T z := by
    constructor
    · intro i hi; rw [hT i hi]; exact hz.2.1 (i₀ i+1) (by have := bounds i hi; omega)
    · intro i hi; rw [hT i hi]; exact hz.2.2 (i₀ i+1) (by have := bounds i hi; omega) (by omega)
  let a := P.vertex 0
  have aT : Avoids T a := by
    constructor
    · intro i hi he
      rw [hT i hi] at he
      have := P.inj (Nat.zero_le _) (bounds i hi).2 he
      have := bounds i hi
      omega
    · intro i hi he
      rw [hT i hi] at he
      have := (P.edges (Nat.zero_le _) (bounds i hi).2).1 he
      have := bounds i hi
      omega
  have hzx : G.Adj x z := hz.1
  have hza : z ≠ a := hz.2.1 1 (by omega)
  have hzya : ¬G.Adj z y := fun h => hza (h4 hxy hzx h.symm hx.1.symm hy.1.symm)
  have same {u v w : V} (h : G.Adj u w) (h' : G.Adj v w) : c u = c v := by
    apply Fin.ext
    have := Fin.val_ne_of_ne (c.valid h)
    have := Fin.val_ne_of_ne (c.valid h')
    have := (c u).isLt; have := (c v).isLt; have := (c w).isLt
    omega
  have cbx := same hzb.symm hzx
  have cyx := same hy.1.symm hx.1.symm
  have cza := same hzx.symm hx.1
  have xb : x ≠ b := by
    intro e
    have hjn : j ≤ n := by omega
    exact hx.2.2 j hjn (by omega) (e ▸ (hba j hjn).2 rfl)
  have yb : y ≠ b := fun e => hzya (e ▸ hzb)
  have yz : y ≠ z := fun e => c.valid hy.1 (cza.symm.trans ((congrArg c e).symm))
  have hab : ¬G.Adj a b := fun h => by have := (hba 0 (by omega)).1 h.symm; omega
  have haz : ¬G.Adj a z := fun h => c.valid h cza.symm
  have hZ := good_grow hb zT hzb.symm
  have xB := avoids_grow hb (good_avoids hx) xb (fun h => c.valid h cbx.symm)
  have hX := good_grow hZ xB hzx.symm
  have aB := avoids_grow hb aT (hbf 0 (by omega)).symm hab
  have aZ := avoids_grow hZ aB hza.symm haz
  have hA := good_grow hX aZ hx.1.symm
  have yB := avoids_grow hb (good_avoids hy) yb (fun h => c.valid h (cyx.trans cbx.symm))
  have yZ := avoids_grow hZ yB yz (fun h => hzya h.symm)
  have yX := avoids_grow hX yZ hxy.symm (fun h => c.valid h cyx)
  have hY := good_grow hA yX hy.1
  have hp := (grow _ y hY).length_le
  omega

end Wall133
