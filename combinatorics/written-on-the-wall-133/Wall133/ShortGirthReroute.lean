module

public import Wall133.ShortGirthGeodesic

@[expose] public section
namespace Wall133
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V} {n : ℕ}

/-- Reroute the beginning of the chain through a private neighbor of the
second vertex and two independent clean extensions at the original endpoint. -/
theorem independent_end_reroute [Fintype V] [DecidableEq V] (P : Chain G n) (hn : 2 ≤ n)
    (h4 : NoFourCycle G) {x y b : V} (hx : Good P x) (hy : Good P y)
    (hxy : x ≠ y) (nxy : ¬G.Adj x y) (hxb : G.Adj x b)
    (hbf : ∀ i ≤ n,b ≠ P.vertex i) (hba : ∀ i ≤ n,G.Adj b (P.vertex i) ↔ i=2) :
    n+3 ≤ G.path := by
  let T : Chain G (n-2) := ⟨fun j => P.vertex (j+2),
    fun {i j} hi hj e => by have := P.inj (by omega) (by omega) e; omega,
    fun {i j} hi hj => by rw [P.edges (by omega) (by omega)]; omega⟩
  have bg : Good T b := by
    refine ⟨((hba 2 hn).2 rfl).symm,fun i hi => hbf _ (by omega),?_⟩
    intro i hi hne bad
    have := (hba (i+2) (by omega)).1 bad
    omega
  let B := grow T b bg
  have xg : Good B x := by
    refine ⟨hxb.symm,?_,?_⟩
    · rintro (_|i) hi
      · exact hxb.ne
      · exact hx.2.1 (i+2) (by omega)
    · rintro (_|i) hi hn'
      · contradiction
      · exact hx.2.2 (i+2) (by omega) (by omega)
  let X := grow B x xg
  have pg : Good X (P.vertex 0) := by
    refine ⟨hx.1.symm,?_,?_⟩
    · rintro (_|(_|i)) hi
      · exact hx.1.ne
      · exact (hbf 0 (by omega)).symm
      · intro he
        have := P.inj (Nat.zero_le _) (show i+2 ≤ n by omega) he
        omega
    · rintro (_|(_|i)) hi hne ha
      · contradiction
      · have := (hba 0 (by omega)).1 ha.symm; omega
      · have := (P.edges (Nat.zero_le _) (show i+2 ≤ n by omega)).1 ha; omega
  let A := grow X (P.vertex 0) pg
  have nyb : ¬G.Adj y b := fun hyb =>
    hbf 0 (by omega) (h4 hxy hxb hyb hx.1.symm hy.1.symm)
  have yb : y ≠ b := fun e => nxy (e ▸ hxb)
  have yg : Good A y := by
    refine ⟨hy.1,?_,?_⟩
    · rintro (_|(_|(_|i))) hi
      · exact hy.1.ne.symm
      · exact hxy.symm
      · exact yb
      · exact hy.2.1 (i+2) (by omega)
    · rintro (_|(_|(_|i))) hi hn'
      · contradiction
      · exact fun h => nxy h.symm
      · exact nyb
      · exact hy.2.2 (i+2) (by omega) (by omega)
  have := (grow A y yg).length_le
  omega

/-- Reroute the beginning of the chain through a private neighbor of the
last vertex and two independent clean extensions at the original endpoint. -/
theorem independent_last_reroute [Fintype V] [DecidableEq V] (P : Chain G n) (hn : 2 ≤ n)
    (h4 : NoFourCycle G) {x y b : V} (hx : Good P x) (hy : Good P y)
    (hxy : x ≠ y) (nxy : ¬G.Adj x y) (hxb : G.Adj x b)
    (hbf : ∀ i ≤ n,b ≠ P.vertex i) (hba : ∀ i ≤ n,G.Adj b (P.vertex i) ↔ i=n) :
    n+3 ≤ G.path := by
  let T : Chain G (n-2) := ⟨fun j => P.vertex (n-j),
    fun {i j} hi hj e => by have := P.inj (by omega) (by omega) e; omega,
    fun {i j} hi hj => by rw [P.edges (by omega) (by omega)]; omega⟩
  have bg : Good T b := by
    refine ⟨by simpa [T] using ((hba n le_rfl).2 rfl).symm,fun i hi => hbf _ (by omega),?_⟩
    intro i hi hne bad
    have := (hba (n-i) (by omega)).1 bad
    omega
  let B := grow T b bg
  have xg : Good B x := by
    refine ⟨hxb.symm,?_,?_⟩
    · rintro (_|i) hi
      · exact hxb.ne
      · exact hx.2.1 (n-i) (by omega)
    · rintro (_|i) hi hn'
      · contradiction
      · exact hx.2.2 (n-i) (by omega) (by omega)
  let X := grow B x xg
  have pg : Good X (P.vertex 0) := by
    refine ⟨hx.1.symm,?_,?_⟩
    · rintro (_|(_|i)) hi
      · exact hx.1.ne
      · exact (hbf 0 (by omega)).symm
      · intro he
        have := P.inj (Nat.zero_le _) (show n-i ≤ n by omega) he
        omega
    · rintro (_|(_|i)) hi hne ha
      · contradiction
      · have := (hba 0 (by omega)).1 ha.symm; omega
      · have := (P.edges (Nat.zero_le _) (show n-i ≤ n by omega)).1 ha; omega
  let A := grow X (P.vertex 0) pg
  have nyb : ¬G.Adj y b := fun hyb =>
    hbf 0 (by omega) (h4 hxy hxb hyb hx.1.symm hy.1.symm)
  have yb : y ≠ b := fun e => nxy (e ▸ hxb)
  have yg : Good A y := by
    refine ⟨hy.1,?_,?_⟩
    · rintro (_|(_|(_|i))) hi
      · exact hy.1.ne.symm
      · exact hxy.symm
      · exact yb
      · exact hy.2.1 (n-i) (by omega)
    · rintro (_|(_|(_|i))) hi hn'
      · contradiction
      · exact fun h => nxy h.symm
      · exact nyb
      · exact hy.2.2 (n-i) (by omega) (by omega)
  have := (grow A y yg).length_le
  omega

end Wall133
