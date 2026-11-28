import Std

/-!
Every nonempty simple graph with minimum degree at least three contains a
four-cycle, an induced net, or an induced once-subdivided claw. The graph may
even be infinite. All edge lists in the two induced configurations are exact.
-/

namespace Erdos64.NetAndTripod

structure Graph (V : Type u) where
  adj : V → V → Prop
  symm : ∀ {a b}, adj a b → adj b a
  loopless : ∀ a, ¬ adj a a

variable {V : Type u} (G : Graph V)

def MinDegreeThree : Prop :=
  ∀ v, ∃ a b c, G.adj v a ∧ G.adj v b ∧ G.adj v c ∧
    a ≠ b ∧ a ≠ c ∧ b ≠ c

def HasFourCycle : Prop :=
  ∃ a b c d, [a,b,c,d].Nodup ∧ G.adj a b ∧ G.adj b c ∧
    G.adj c d ∧ G.adj d a

/-- On the selected vertices, the three leaves span an independent set and
meet the three interior vertices in exactly the indicated matching. -/
def PendantMatching (a b c x y z : V) : Prop :=
  G.adj a x ∧ G.adj b y ∧ G.adj c z ∧
  ¬ G.adj x y ∧ ¬ G.adj y z ∧ ¬ G.adj z x ∧
  ¬ G.adj a y ∧ ¬ G.adj a z ∧ ¬ G.adj b x ∧
  ¬ G.adj b z ∧ ¬ G.adj c x ∧ ¬ G.adj c y

def HasInducedNet : Prop :=
  ∃ a b c x y z, [a,b,c,x,y,z].Nodup ∧
    G.adj a b ∧ G.adj b c ∧ G.adj c a ∧ PendantMatching G a b c x y z

def HasInducedSubdividedClaw : Prop :=
  ∃ r a b c x y z, [r,a,b,c,x,y,z].Nodup ∧
    G.adj r a ∧ G.adj r b ∧ G.adj r c ∧
    ¬ G.adj a b ∧ ¬ G.adj b c ∧ ¬ G.adj c a ∧
    ¬ G.adj r x ∧ ¬ G.adj r y ∧ ¬ G.adj r z ∧
    PendantMatching G a b c x y z

private theorem extraNeighbor (deg : MinDegreeThree G) (v p q : V) :
    ∃ z, G.adj v z ∧ z ≠ p ∧ z ≠ q := by
  obtain ⟨a,b,c,ha,hb,hc,hab,hac,hbc⟩ := deg v
  by_cases h : a = p ∨ a = q
  · by_cases k : b = p ∨ b = q
    · exact ⟨c,hc,by grind,by grind⟩
    · exact ⟨b,hb,by grind,by grind⟩
  · exact ⟨a,ha,by grind,by grind⟩

private theorem twoOtherNeighbors (deg : MinDegreeThree G) (v p : V) :
    ∃ x y, G.adj v x ∧ G.adj v y ∧ x ≠ p ∧ y ≠ p ∧ x ≠ y := by
  obtain ⟨x,hx,hxp,_⟩ := extraNeighbor G deg v p p
  obtain ⟨y,hy,hyp,hyx⟩ := extraNeighbor G deg v p x
  exact ⟨x,y,hx,hy,hxp,hyp,Ne.symm hyx⟩

private def UniqueCommon : Prop :=
  ∀ a b x y, a ≠ b → G.adj a x → G.adj b x → G.adj a y → G.adj b y → x = y

private theorem uniqueCommon (h : ¬ HasFourCycle G) : UniqueCommon G := by
  intro a b x y hab hax hbx hay hby
  apply Classical.byContradiction
  intro hxy
  apply h
  exact ⟨a,x,b,y,by simp; grind [Graph.loopless],
    hax,G.symm hbx,hby,G.symm hay⟩

private def TriangleFree : Prop := ∀ a b c, G.adj a b → G.adj b c → ¬ G.adj c a

private theorem adjNe {a b : V} (h : G.adj a b) : a ≠ b := by
  intro eq
  subst b
  exact G.loopless a h

private theorem triangleLeaves (unique : UniqueCommon G)
    {a b c x y : V} (ab : G.adj a b) (bc : G.adj b c) (ca : G.adj c a)
    (ax : G.adj a x) (by' : G.adj b y)
    (xb : x ≠ b) (xc : x ≠ c) (ya : y ≠ a) (yc : y ≠ c) :
    x ≠ y ∧ ¬ G.adj x y ∧ ¬ G.adj a y ∧ ¬ G.adj b x := by
  have forbidX : ¬ G.adj b x := fun bx =>
    xc (unique a b x c (adjNe G ab) ax bx (G.symm ca) bc)
  have forbidY : ¬ G.adj a y := fun ay =>
    yc (unique a b y c (adjNe G ab) ay by' (G.symm ca) bc)
  refine ⟨?_, ?_, forbidY, forbidX⟩
  · intro eq
    exact forbidX (eq ▸ by')
  · intro xy
    exact xb (unique a y x b (Ne.symm ya) ax (G.symm xy) ab (G.symm by'))

private theorem triangleFree (deg : MinDegreeThree G) (unique : UniqueCommon G)
    (noNet : ¬ HasInducedNet G) : TriangleFree G := by
  intro a b c hab hbc hca
  obtain ⟨x,hax,hxb,hxc⟩ := extraNeighbor G deg a b c
  obtain ⟨y,hby,hya,hyc⟩ := extraNeighbor G deg b a c
  obtain ⟨z,hcz,hza,hzb⟩ := extraNeighbor G deg c a b
  apply noNet
  have first := triangleLeaves G unique hab hbc hca hax hby hxb hxc hya hyc
  have second := triangleLeaves G unique hbc hca hab hby hcz hyc hya hzb hza
  have third := triangleLeaves G unique hca hab hbc hcz hax hza hzb hxc hxb
  refine ⟨a,b,c,x,y,z,?_,hab,hbc,hca,?_⟩
  · simp
    grind [→ adjNe]
  · unfold PendantMatching
    grind [→ adjNe]

/-- Two children of one neighbor of the root. -/
private structure Arm (r p : V) where
  rootEdge : G.adj r p
  child : Bool → V
  edge : ∀ i, G.adj p (child i)
  away : ∀ i, child i ≠ r
  different : child false ≠ child true

private theorem getArm (deg : MinDegreeThree G) {r p : V} (rp : G.adj r p) :
    Nonempty (Arm G r p) := by
  obtain ⟨x,y,hx,hy,hxr,hyr,hxy⟩ := twoOtherNeighbors G deg p r
  exact ⟨⟨rp,(fun i => if i then y else x),
    by intro i; cases i <;> assumption,
    by intro i; cases i <;> assumption, hxy⟩⟩

private theorem separateArms (tri : TriangleFree G) (unique : UniqueCommon G)
    {r p q : V} (A : Arm G r p) (B : Arm G r q) (pq : p ≠ q) (i j : Bool) :
    ¬ G.adj p q ∧ A.child i ≠ q ∧ ¬ G.adj q (A.child i) ∧ A.child i ≠ B.child j := by
  have noPQ := tri q r p (G.symm B.rootEdge) A.rootEdge
  have noQX : ¬ G.adj q (A.child i) := fun qx =>
    A.away i (unique p q (A.child i) r pq (A.edge i) qx
      (G.symm A.rootEdge) (G.symm B.rootEdge))
  exact ⟨noPQ, (fun eq => noPQ (eq ▸ A.edge i)), noQX,
    fun eq => noQX (eq ▸ B.edge j)⟩

private def Matching (R : Bool → Bool → Prop) : Prop :=
  (∀ i, ¬(R i false ∧ R i true)) ∧ (∀ j, ¬(R false j ∧ R true j))

private theorem armMatching (tri : TriangleFree G) (unique : UniqueCommon G)
    {r p q : V} (A : Arm G r p) (B : Arm G r q) (pq : p ≠ q) :
    Matching (fun i j => G.adj (A.child i) (B.child j)) := by
  constructor
  · intro i ⟨h₀,h₁⟩
    have hxq := (separateArms G tri unique A B pq i false).2.1
    exact B.different (unique (A.child i) q _ _ hxq h₀ (B.edge false) h₁ (B.edge true))
  · intro j ⟨h₀,h₁⟩
    have hyp := (separateArms G tri unique B A (Ne.symm pq) j false).2.1
    exact A.different (unique (B.child j) p _ _ hyp
      (G.symm h₀) (A.edge false) (G.symm h₁) (A.edge true))

/-- The six-vertex choice: with three pairs of vertices, matchings between
pairs, and no triangle, some transversal of the pairs is independent. -/
private theorem independentTransversal (R S T : Bool → Bool → Prop)
    (hR : Matching R) (hS : Matching S) (hT : Matching T)
    (triangle : ∀ i j k, ¬(R i j ∧ S j k ∧ T k i)) :
    ∃ i j k, ¬R i j ∧ ¬S j k ∧ ¬T k i := by
  simp only [Matching, Bool.forall_bool, Bool.exists_bool] at *
  grind (splits := 20)

private theorem inducedClaw (deg : MinDegreeThree G) (unique : UniqueCommon G)
    (tri : TriangleFree G) (r : V) : HasInducedSubdividedClaw G := by
  obtain ⟨a,b,c,ra,rb,rc,ab,ac,bc⟩ := deg r
  obtain ⟨A⟩ := getArm G deg ra
  obtain ⟨B⟩ := getArm G deg rb
  obtain ⟨C⟩ := getArm G deg rc
  obtain ⟨i,j,k,hxy,hyz,hzx⟩ := independentTransversal _ _ _
    (armMatching G tri unique A B ab) (armMatching G tri unique B C bc)
    (armMatching G tri unique C A (Ne.symm ac))
    (fun i j k ⟨xy,yz,zx⟩ => tri (A.child i) (B.child j) (C.child k) xy yz zx)
  have ax := A.edge i
  have by' := B.edge j
  have cz := C.edge k
  have xr := A.away i
  have yr := B.away j
  have zr := C.away k
  have notRX := tri (A.child i) a r (G.symm ax) (G.symm ra)
  have notRY := tri (B.child j) b r (G.symm by') (G.symm rb)
  have notRZ := tri (C.child k) c r (G.symm cz) (G.symm rc)
  have fAB := separateArms G tri unique A B ab i j
  have fBC := separateArms G tri unique B C bc j k
  have fCA := separateArms G tri unique C A (Ne.symm ac) k i
  have fBA := separateArms G tri unique B A (Ne.symm ab) j i
  have fCB := separateArms G tri unique C B (Ne.symm bc) k j
  have fAC := separateArms G tri unique A C ac i k
  refine ⟨r,a,b,c,A.child i,B.child j,C.child k,?_,ra,rb,rc,?_,?_,?_,notRX,notRY,notRZ,?_⟩
  · simp
    grind [→ adjNe]
  · exact fAB.1
  · exact fBC.1
  · exact fCA.1
  · unfold PendantMatching
    grind

/-- The Erdős–Gyárfás conclusion for graphs forbidding both induced patterns,
with the stronger conclusion that the cycle has exactly four edges. -/
theorem fourCycle_of_netFree_subdividedClawFree [Nonempty V] (deg : MinDegreeThree G)
    (noNet : ¬ HasInducedNet G) (noClaw : ¬ HasInducedSubdividedClaw G) :
    HasFourCycle G := by
  apply Classical.byContradiction
  intro noFour
  have unique := uniqueCommon G noFour
  have tri := triangleFree G deg unique noNet
  exact noClaw (inducedClaw G deg unique tri (Classical.ofNonempty))

end Erdos64.NetAndTripod
