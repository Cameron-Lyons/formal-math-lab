import Ramsey556.TwoVertexPaths
import Ramsey556.TwoVertexSetup
import Ramsey556.TwoVertexCounting
import Ramsey556.TwoVertexFinish

/-!
## An independent 16-set forces a monochromatic nine-cycle

Suppose the red graph is independent on a set of sixteen vertices. The
two-color classification splits these vertices into octets A and B. In a
coloring avoiding a monochromatic C₉, each of the seventeen exterior
vertices has at least seven red neighbors in A or at least seven in B.
Assign each exterior vertex to one such octet. Write X for the larger
type (say A), and Y for the other type.

Any five or more vertices of one type are red-independent. A red edge
between two of them would close an alternating path of length eight,
using three other vertices of that type and four distinct anchor neighbors.
In particular X is red-independent. If Y has at most four vertices,
then X has at least thirteen. Suppose uv is a red edge in Y. The vertices
u and v have at least six common red neighbors in B. There are two
disjoint red edges from X into those six vertices, since even after deleting
the endpoints of the first edge, the two sets together have at least
seventeen vertices. A set of seventeen avoiding red already contains a
monochromatic C₉ by the two-color Ramsey theorem. Between the X-endpoints
of the two edges take a red path of length four alternating through A.
It closes with the two edges, one spoke from each of u and v, and uv.
Thus Y is red-independent in both size ranges.

If all red edges between X and Y share a vertex, deleting it leaves a
red bipartition into the original anchors and the remaining exterior
vertices, giving the one-deletion case. Otherwise these cross edges
include a matching of size two. If an anchor has red neighbors i in X
and j in Y, take a matching edge pq with p in X distinct from i. When
q = j, join i and p by six alternating red edges through A. When q ≠ j,
join i and p by four alternating red edges through A and q and j by two
through B. In either case the paths, pq, and the two spokes at the
anchor give a red C₉. Hence each anchor has red neighbors in at most
one exterior type. Put it on the opposite side to those neighbors.
This gives a red bipartition and again the one-deletion theorem applies.
-/

namespace Ramsey556

/-- Every coloring with the two supporting octets has a monochromatic nine-cycle. -/
theorem hasMonoC9_of_supportedOctets (classify : TwoColorOctets16)
    {c : Coloring 33} (S : SupportedOctets c) : HasMonoC9 c := by
  apply Classical.byContradiction
  intro free
  have total : (S.members 0).length + (S.members 1).length = 17 := by
    have split (xs : List (Fin 17)) :
        (xs.filter (fun i => S.tag i == 0)).length +
        (xs.filter (fun i => S.tag i == 1)).length = xs.length := by
      induction xs with
      | nil => rfl
      | cons i xs ih =>
        have cases : S.tag i = 0 ∨ S.tag i = 1 := by omega
        rcases cases with h | h <;> simp [h] <;> omega
    simpa [SupportedOctets.members] using split (List.finRange 17)
  obtain ⟨big,small,hbs,size,total'⟩ : ∃ big small : Fin 2, big ≠ small ∧
      9 ≤ (S.members big).length ∧ (S.members big).length + (S.members small).length = 17 := by
    by_cases h : 9 ≤ (S.members 0).length
    · exact ⟨0,1,by decide,h,total⟩
    · exact ⟨1,0,by decide,by omega,by omega⟩
  have large (i j : Fin 17) := @SupportedOctets.noEdge_large_type c S free big
    (by omega : 5 ≤ (S.members big).length) i j
  have inner (i j : Fin 17) (ne : i ≠ j) (same : S.tag i = S.tag j) :
      c.edge (S.outer i) (S.outer j) ≠ 0 := by
    by_cases hi : S.tag i = big
    · exact large i j ne hi (same ▸ hi)
    have hu : S.tag i = small := by omega
    have hv : S.tag j = small := same ▸ hu
    by_cases enough : 5 ≤ (S.members small).length
    · exact S.noEdge_large_type free small enough ne hu hv
    obtain ⟨p,q,a,b,pq,ab,hp,hq,pa,qb,ua,vb⟩ := two_links_of_large_type S
      (noIndependent17_of_free classify free) big small hbs (by omega)
      large i j hu hv
    exact S.noEdge_of_two_links free big small hbs (by omega) ne hu hv pq ab hp hq pa qb ua vb
  exact free (finish_two_independent_types classify S big inner
    (S.no_mixed_anchor free big (by omega)))

/-- Every three-coloring of K₃₃ with a set of 16 vertices avoiding any
specified color contains a monochromatic nine-cycle. The sole external
input here is the two-color K₁₆ classification. -/
theorem hasMonoC9_of_independent16 (classify : TwoColorOctets16) (c : Coloring 33)
    (v : Fin 16 → Fin 33) (inj : ∀ ⦃i j⦄, v i = v j → i = j) (r : Fin 3)
    (absent : ∀ i j, i ≠ j → c.edge (v i) (v j) ≠ r) : HasMonoC9 c := by
  let swap (r x : Fin 3) : Fin 3 := if x = r then 0 else if x = 0 then r else x
  have perm : ∀ r i j, swap r i = swap r j → i = j := by decide
  let d := c.recolor (swap r)
  have omitRed (i j : Fin 16) (ne : i ≠ j) : d.edge (v i) (v j) ≠ 0 := by
    intro e
    apply absent i j ne (perm r _ r ?_)
    rwa [show swap r r = 0 by simp [swap]]
  apply hasMonoC9_of_copy c id (swap r) (fun {_ _} e => e) (fun {_ _} => perm r _ _)
  change HasMonoC9 d
  apply Classical.byContradiction
  intro free
  obtain ⟨S⟩ := supportedOctets_of_independent classify free v (@inj) omitRed
  exact free (hasMonoC9_of_supportedOctets classify S)

/-- The case in which deleting two vertices makes some color bipartite. -/
theorem hasMonoC9_of_one_bipartite_on_31 (classify : TwoColorOctets16)
    (c : Coloring 33) (v : Fin 31 → Fin 33) (hv : ∀ ⦃i j⦄, v i = v j → i = j)
    (r : Fin 3) (bip : IsBipartiteColor (c.induce v) r) : HasMonoC9 c := by
  obtain ⟨u,iu,absent⟩ := independent16_of_bipartite_on_31 c v (@hv) r bip
  exact hasMonoC9_of_independent16 classify c u (@iu) r absent

/-- Some color class has an independent set of size sixteen. -/
def HasIndependent16 (c : Coloring 33) : Prop :=
  ∃ (r : Fin 3) (v : Fin 16 → Fin 33), (∀ ⦃i j⦄, v i = v j → i = j) ∧
    ∀ i j, i ≠ j → c.edge (v i) (v j) ≠ r

/-- In any surviving counterexample each color graph has independence number at most 15. -/
theorem k33_iff_small_independence (classify : TwoColorOctets16) :
    K33Claim ↔ ∀ c : Coloring 33, (¬ HasIndependent16 c) → HasMonoC9 c := by
  refine ⟨fun h c _ => h c, ?_⟩
  intro h c
  by_cases hit : HasIndependent16 c
  · obtain ⟨r,v,hv,absent⟩ := hit
    exact hasMonoC9_of_independent16 classify c v (@hv) r absent
  · exact h c hit

end Ramsey556
