import Ramsey556.TwoVertex

namespace Ramsey556

/-- A red-independent set of vertices and seventeen other vertices in two groups.
Any two vertices of one group have at least four common red neighbors in that set. -/
structure AnchorSupport (c : Coloring 33) (size : Nat := 15) where
  anchor : Fin size → Fin 33
  outer : Fin 17 → Fin 33
  tag : Fin 17 → Fin 2
  anchorInj : Function.Injective anchor
  outerInj : Function.Injective outer
  disjoint : ∀ a i, anchor a ≠ outer i
  independent : ∀ a b, a ≠ b → c.edge (anchor a) (anchor b) ≠ 0
  common : ∀ i j, tag i = tag j → 4 ≤ ((List.finRange size).filter (fun a =>
    c.edge (outer i) (anchor a) == 0 && c.edge (outer j) (anchor a) == 0)).length

namespace AnchorSupport

variable {c : Coloring 33} {size : Nat}

def members (S : AnchorSupport c size) (s : Fin 2) : List (Fin 17) :=
  (List.finRange 17).filter (fun i => S.tag i == s)

def neighbors (S : AnchorSupport c size) (i j : Fin 17) : List (Fin size) :=
  (List.finRange size).filter (fun a => c.edge (S.outer i) (S.anchor a) == 0 &&
    c.edge (S.outer j) (S.anchor a) == 0)

private theorem fresh {α : Type} (xs used : List α) (nd : xs.Nodup) (room : used.length < xs.length) :
    ∃ a ∈ xs, a ∉ used := by
  have missing : ¬ xs ⊆ used := fun sub => (Nat.not_le_of_gt room) (nd.length_le_of_subset sub)
  change ¬ (∀ x, x ∈ xs → x ∈ used) at missing
  simpa using missing

theorem freshOuter (S : AnchorSupport c size) (s : Fin 2) (used : List (Fin 17))
    (room : used.length < (S.members s).length) : ∃ i, S.tag i = s ∧ i ∉ used := by
  obtain ⟨i,hi,ne⟩ := fresh (S.members s) used ((List.nodup_finRange 17).filter _) room
  exact ⟨i,by simpa [members] using hi,ne⟩

/-- The anchor `a` joins the two exterior vertices by a red path of length two. -/
abbrev Via (S : AnchorSupport c size) (x y : Fin 17) (a : Fin size) : Prop :=
  c.edge (S.outer x) (S.anchor a) = 0 ∧ c.edge (S.outer y) (S.anchor a) = 0

theorem freshAnchor (S : AnchorSupport c size) (i j : Fin 17) (same : S.tag i = S.tag j)
    (used : List (Fin size)) (room : used.length ≤ 3) :
    ∃ a, a ∉ used ∧ S.Via i j a := by
  have four : 4 ≤ (S.neighbors i j).length := S.common _ _ same
  obtain ⟨a,ha,ne⟩ := fresh (S.neighbors i j) used ((List.nodup_finRange size).filter _) (by omega)
  exact ⟨a,ne,by simpa [neighbors,Via] using ha⟩

theorem flip {a b : Fin 33} (e : c.edge a b = 0) : c.edge b a = 0 :=
  (c.symm _ _).trans e

theorem aa (S : AnchorSupport c size) {a b} : S.anchor a = S.anchor b ↔ a = b :=
  S.anchorInj.eq_iff

theorem oo (S : AnchorSupport c size) {a b} : S.outer a = S.outer b ↔ a = b :=
  S.outerInj.eq_iff

theorem oa (S : AnchorSupport c size) (i a) : S.outer i ≠ S.anchor a :=
  (S.disjoint _ _).symm

/-- Four two-edge paths through distinct anchors and one closing edge give a nine-cycle. -/
theorem alternatingCycle (S : AnchorSupport c size) {x y z u v : Fin 17} {a b d e : Fin size}
    (xy : S.Via x y a) (yz : S.Via y z b) (zu : S.Via z u d) (uv : S.Via u v e)
    (close : c.edge (S.outer x) (S.outer v) = 0)
    (outside : [x,y,z,u,v].Nodup) (anchors : [a,b,d,e].Nodup) : HasMonoC9 c := by
  apply SupportedOctets.cycle (S.outer x) (S.anchor a) (S.outer y) (S.anchor b) (S.outer z)
    (S.anchor d) (S.outer u) (S.anchor e) (S.outer v) _ xy.1 (flip xy.2) yz.1 (flip yz.2)
    zu.1 (flip zu.2) uv.1 (flip uv.2) (flip close)
  simp_all [oo, aa, disjoint, oa]

/-- Five vertices of one type allow a red edge of that type to close an eight-edge path. -/
theorem noEdge_large (S : AnchorSupport c size) (free : ¬ HasMonoC9 c)
    (s : Fin 2) (size : 5 ≤ (S.members s).length) {i j : Fin 17}
    (ne : i ≠ j) (hi : S.tag i = s) (hj : S.tag j = s) : c.edge (S.outer i) (S.outer j) ≠ 0 := by
  intro edge
  obtain ⟨u,hu,nu⟩ := S.freshOuter s [i,j] (by simp; omega)
  obtain ⟨v,hv,nv⟩ := S.freshOuter s [i,j,u] (by simp; omega)
  obtain ⟨w,hw,nw⟩ := S.freshOuter s [i,j,u,v] (by simp; omega)
  obtain ⟨a,_,iu⟩ := S.freshAnchor i u (hi.trans hu.symm) [] (by simp)
  obtain ⟨b,nb,uv⟩ := S.freshAnchor u v (hu.trans hv.symm) [a] (by simp)
  obtain ⟨d,nd,vw⟩ := S.freshAnchor v w (hv.trans hw.symm) [a,b] (by simp)
  obtain ⟨e,nf,wj⟩ := S.freshAnchor w j (hw.trans hj.symm) [a,b,d] (by simp)
  apply free
  apply S.alternatingCycle iu uv vw wj edge <;> simp_all <;> grind

end AnchorSupport
end Ramsey556
