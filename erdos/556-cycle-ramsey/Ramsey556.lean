import Ramsey556.Certified16
import Ramsey556.Deletion
import Ramsey556.Distances
import Ramsey556.FifteenSupport
import Ramsey556.EdgeBound
import Ramsey556.Lower
import Ramsey556.OneBipartite
import Ramsey556.TwoVertex
import Ramsey556.Upper
import Ramsey556.Remaining33
import Ramsey556.SplitRamsey
import Ramsey556.TenFourteen
import Ramsey556.SixCliqueTriples

/-!
# Three-color cycle Ramsey number for C₉

`Ramsey556.K33Claim` is the unrestricted open upper bound.
`lowerColoring_no_monoC9` supplies the obstruction on 32 vertices.
`monoC9_of_independent16` proves the upper bound whenever sixteen vertices
avoid one color. In particular, `monoC9_of_bipartite_after_two_deletions`
covers every coloring in which removing two vertices makes one color
bipartite. The lower example already has two bipartite classes, so 33
is sharp under this deletion hypothesis.

The proof of `monoC9_of_independent15` uses one fact from the 14-vertex
classification. If 14 vertices miss a color in a counterexample, they
contain a monochromatic eight-clique. Suppose 15 vertices miss a color.
Any two distinct monochromatic eight-cliques among them must meet, and
cannot share two vertices. A shared edge would give both cliques the same
color, and a vertex of one clique could close a nine-cycle through the
other. Two such cliques therefore cover all 15 vertices. A third could
meet each in at most one vertex, so there are at most two. Delete a vertex
common to all the eight-cliques. The remaining 14 still miss the color but
contain no monochromatic eight-clique.

`k33_iff_final_two_cases` records the surviving eight-plus-six template
on a set of 14 missing one color and the case in which every 14 use all
three colors.

`splitForcesC9_iff` gives the exact threshold for the associated two-color
problem on a clique joined to an independent set. In particular a K₁₃
joined to four additional vertices already forces a monochromatic C₉,
using only edges incident to the K₁₃. Consequently every 13-set missing
a color in a counterexample has neighbors in that color at 17 or more of
the 20 exterior vertices.

## Proof of the deletion case

Call the deleted vertex x. Intersect the two bipartitions on the other 32
vertices. Each of the four cells is a clique in the third color, say red.
A cell with nine vertices already contains a red C₉, so assume all four
cells have size eight. Two red edges between the same two cells would
also give a red C₉. If they share an endpoint it closes a Hamiltonian path
in the opposite cell. If their endpoints are distinct, use seven vertices
of one cell and two of the other. Thus at most three vertices per cell
have red neighbors outside that cell among the original 32 vertices.

Keep five vertices per cell that avoid those exceptions. Edges between
these representatives along rows are blue and along columns are green.
Choose one diagonal edge. By symmetry suppose it is blue. Reserve its
endpoints, and mark two other representatives in each cell. The two marked
vertices in each cell are endpoints of a red seven-edge path through the cell,
so at least one of them has a nonred edge to x. Select one such vertex
in each cell.

Any two selected vertices in different columns are joined by a blue
seven-edge path. For a pair in one row, alternate between its cells. For
a pair in different rows, the diagonal edge joins the two blue rows, and
the five representatives provide the distinct vertices needed on either
side of the bridge. The explicit paths are in `SquarePaths.lean`. Thus
blue neighbors of x among the selected vertices can occupy only one column.
Both selected vertices in the other column must be green neighbors of x.
A green seven-edge path alternating inside that column closes through x.

`k33_iff_remaining_case` records the unconditional reduction.

## One bipartite color after deletion

The two-color classification `twoColorOctets16` gives two disjoint
eight-vertex cliques of the same color in any two-colored K₁₆ without
a monochromatic C₉. It follows from `denseC9Free16Bipartite`, which
checks that a C₉-free graph on 16 vertices with at least 60 edges is
bipartite. The finite verification uses minimum-degree deletion, lists
of graph representatives, and explicit paths, relabelings and final
bipartitions. Dzido, Kubale and Piwakowski, Theorem 9, give the stronger
bound of 57 edges for a nonbipartite example.

## Two deleted vertices

A bipartition on 31 vertices has a side of size at least 16. The proof
in `Ramsey556.TwoVertex` shows that these sixteen vertices alone suffice.
The other seventeen vertices have restricted neighborhoods in the two
eight-vertex cliques. The resulting paths either close a monochromatic
nine-cycle directly or reduce the coloring to the one-deletion theorem.
-/

namespace Ramsey556

/-- Removing some vertex makes two of the three color classes bipartite. -/
def TwoBipartiteAfterDeletion (c : Coloring 33) : Prop :=
  ∃ (v : Fin 32 → Fin 33), (∀ ⦃i j⦄, v i = v j → i = j) ∧
    ∃ (r s : Fin 3), r ≠ s ∧ IsBipartiteColor (c.induce v) r ∧ IsBipartiteColor (c.induce v) s

/-- It suffices to consider colorings in which every vertex deletion leaves
at most one bipartite color class. -/
theorem k33_iff_remaining_case :
    K33Claim ↔ ∀ c : Coloring 33, (¬ TwoBipartiteAfterDeletion c) → HasMonoC9 c := by
  refine ⟨fun h c _ => h c, ?_⟩
  intro h c
  by_cases pair : TwoBipartiteAfterDeletion c
  · obtain ⟨v, hv, r, s, hrs, hr, hs⟩ := pair
    exact hasMonoC9_of_two_bipartite_on_32 c v hv hrs hr hs
  · exact h c pair

/-- Isolate the single-color extremal input from the unrestricted open case. -/
theorem k33_iff_all_three_survive_of_edgeBound (bound : DenseC9Free16Bipartite) :
    K33Claim ↔ ∀ c : Coloring 33, (¬ OneBipartiteAfterDeletion c) → HasMonoC9 c :=
  k33_iff_all_three_survive (twoColorOctets16_of_edgeBound bound)

/-- Sixteen vertices avoiding any one color force a monochromatic C₉ in K₃₃. -/
theorem monoC9_of_independent16 (c : Coloring 33) (v : Fin 16 → Fin 33)
    (inj : ∀ ⦃i j⦄, v i = v j → i = j) (r : Fin 3)
    (absent : ∀ i j, i ≠ j → c.edge (v i) (v j) ≠ r) : HasMonoC9 c :=
  hasMonoC9_of_independent16 twoColorOctets16 c v (@inj) r absent

/-- If deleting two vertices makes one color bipartite, K₃₃ contains a monochromatic C₉. -/
theorem monoC9_of_bipartite_after_two_deletions (c : Coloring 33) (v : Fin 31 → Fin 33)
    (inj : ∀ ⦃i j⦄, v i = v j → i = j) (r : Fin 3)
    (bip : IsBipartiteColor (c.induce v) r) : HasMonoC9 c :=
  hasMonoC9_of_one_bipartite_on_31 twoColorOctets16 c v (@inj) r bip

/-- It suffices to consider colorings in which all three independence numbers are at most 15. -/
theorem k33_iff_independence_at_most_15 :
    K33Claim ↔ ∀ c : Coloring 33, (¬ HasIndependent16 c) → HasMonoC9 c :=
  k33_iff_small_independence twoColorOctets16

end Ramsey556
