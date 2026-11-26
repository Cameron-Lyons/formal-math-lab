# Can seven slabs tile a cube?

**No.** For each $k=1,\ldots,7$, choose positive integers $a_k,b_k$ and take one rectangular box of dimensions $k\times k a_k\times k b_k$. The theorem `SevenSlabs.no_seven_slab_tiling` proves that their union cannot be a closed real cube with pairwise disjoint interiors. Each box may be rotated and translated independently. [Main theorem](SevenSlabs.lean)

Erich Friedman asks which cubes can be tiled by one slab of each order through $n$. Vamshi Jandhyala excluded $n=4,5,6$ and explicitly identified $n=7$ as untested. [Friedman’s problem 6](https://erich-friedman.github.io/mathmagic/unsolved.html) · [Jandhyala, §6, p. 6](https://raw.githubusercontent.com/jvvk/mathematics/c6fecab25b6f821a7185bfdaa68c89bfaf54e4c7/math-magic-problems/paper/paper.pdf#page=6) · [Repository prior-art note](../PRIOR_ART.md#seven-slabs-tiling-a-cube)

## Proof

Every face normal in a finite tiling of a cube by cuboids must be parallel to a cube axis. Sampling the aligned tiling at integer coordinates then gives a unit-cell tiling with the same slab dimensions. [Alignment proof](SevenSlabs/Alignment.lean) · [Reduction to unit cells](SevenSlabs/RealBoxes.lean)

For a unit-cell cube of side $s$, each order-$k$ slab has volume at most $ks^2$, so $s\le 1+\cdots+7=28$. For each choice of shapes with total volume $s^3$, Lean checks two necessary conditions along each axis. The boxes meeting each of the two opposite faces must supply area $s^2$. A line through each box must meet a set of boxes whose lengths sum to $s$. No compatible choice passes in all three directions. The finite check uses `native_decide`, which trusts Lean’s compiler. [Geometric counting lemmas](SevenSlabs/Grid.lean) · [Enumeration and completeness proof](SlabSearch/Enumerate.lean) · [Axis tests](SlabSearch/Sections.lean) · [Finite check](SevenSlabs/Discrete.lean)

## Reproduce

Run the following from this directory with the pinned Lean and mathlib 4.35.0.

```sh
lake exe cache get
lake build
```

The independent C++ placement search checks all 17,366 volume-compatible shape lists and returns zero tilings. As a positive control, the same executable finds the three-slab tiling of a side-6 cube. Two further C++ programs check the conclusion using transverse sections. [Placement search](verify/placement_search.cpp) · [Section-area test](verify/bound_profiles.cpp) · [Plane sweep](verify/geom_projection.cpp)

```sh
c++ -std=c++17 -O2 verify/placement_search.cpp -o /tmp/place-seven-slabs
/tmp/place-seven-slabs
/tmp/place-seven-slabs 3 6
```
