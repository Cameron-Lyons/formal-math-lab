# Can seven slabs tile a cube?

**No.** An **order-$k$ slab** is a rectangular box of dimensions $k \times k a_k \times k b_k$ for some positive integers $a_k, b_k$—equivalently, a single flat $a_k \times b_k$ layer of $k \times k \times k$ cubes. Suppose you choose one slab of each order $k = 1, 2, 3, 4, 5, 6, 7$, and you are free to rotate and translate each box independently in $\mathbb{R}^3$. Can their union form a solid closed cube with pairwise disjoint interiors?

The Lean 4 theorem `SevenSlabs.no_seven_slab_tiling` ([Main theorem](SevenSlabs.lean)) proves that **no such tiling exists** for any choice of $a_k, b_k$ and any cube size.

> **Why small $n$ works and $n = 7$ is subtle:** For $n = 3$, stacking three full-width layers of thicknesses $1, 2, 3$—namely $1 \times 6 \times 6$, $2 \times 6 \times 6$, and $3 \times 6 \times 6$—effortlessly tiles a $6 \times 6 \times 6$ cube because $1 + 2 + 3 = 6$ is divisible by all of $1, 2, 3$. For $n = 7$, the cube side is bounded by $s \le 1 + 2 + \cdots + 7 = 28$, which is far smaller than $\operatorname{lcm}(1, \ldots, 7) = 420$, so no flat stack is possible and slabs would have to interlock in 3D.

Erich Friedman's *Math Magic* Problem 6 asks which cubes can be tiled by one slab of each order through $n$. Vamshi Jandhyala previously excluded $n = 4, 5, 6$ and explicitly flagged $n = 7$ as untested ([Friedman's problem 6](https://erich-friedman.github.io/mathmagic/unsolved.html) · [Jandhyala, §6, p. 6](https://raw.githubusercontent.com/jvvk/mathematics/c6fecab25b6f821a7185bfdaa68c89bfaf54e4c7/math-magic-problems/paper/paper.pdf#page=6) · [Repository prior-art note](../PRIOR_ART.md#seven-slabs-tiling-a-cube)).

| Field | Summary |
| --- | --- |
| Problem | Tiling a cube with one order-$k$ slab ($k \times k a_k \times k b_k$) for each $k = 1, \ldots, 7$ (Friedman Problem 6; Jandhyala §6) |
| Result | Impossible (`SevenSlabs.no_seven_slab_tiling` in [SevenSlabs.lean](SevenSlabs.lean)) |
| Lean verification | `lake exe cache get && lake build` (Lean + mathlib 4.35.0; geometric reductions kernel-checked, finite axis-test check uses `native_decide`) |
| External cross-check | Independent C++17 placement search (17,366 shape lists, 0 tilings) plus two transverse-section C++ checkers |

## Proof strategy

The proof reduces a continuous 3D geometry problem in $\mathbb{R}^3$ to a finite discrete check in three steps:

1. **Axis alignment and reduction to unit cells (Lean kernel):** In any finite tiling of a real cube by rectangular boxes (even if arbitrarily rotated and translated), Lean proves that every box face normal must be parallel to an axis of the cube ([Alignment proof](SevenSlabs/Alignment.lean)). Sampling the resulting axis-aligned tiling at integer coordinates turns it into a discrete unit-cell tiling of an $s \times s \times s$ cube with the same seven slab dimensions ([Reduction to unit cells](SevenSlabs/RealBoxes.lean)).
2. **Upper bound on the cube side ($s \le 28$, Lean kernel):** Every order-$k$ slab fitting inside an $s \times s \times s$ cube has dimensions $k$, $k a_k \le s$, and $k b_k \le s$, so its volume is at most $k s^2$. Summing across $k = 1, \ldots, 7$ gives
   $$
   s^3 = \sum_{k=1}^7 \operatorname{vol}(\text{slab } k) \le \left(\sum_{k=1}^7 k\right) s^2 = 28 s^2 \implies s \le 28.
   $$
3. **Axis-by-axis elimination (soundness in kernel, finite check via `native_decide`):** For every side length $s \le 28$ and every list of seven slab shapes whose volumes sum to $s^3$, Lean enforces two necessary geometric conditions along each of the three coordinate axes:
   - *Opposite-face area:* The slabs touching each of the two opposite faces perpendicular to that axis must supply total face area $s^2$.
   - *Line-sum feasibility:* Any axis-parallel line piercing a given slab must meet a subset of slabs whose lengths along that axis sum to $s$.

   No volume-compatible shape list passes both tests across all three axes ([Geometric counting lemmas](SevenSlabs/Grid.lean) · [Enumeration and completeness proof](SlabSearch/Enumerate.lean) · [Axis tests](SlabSearch/Sections.lean) · [Finite check](SevenSlabs/Discrete.lean)).

## Verification and trust boundary

- **Lean kernel:** Continuous axis alignment, reduction to unit cells, volume bound $s \le 28$, geometric counting lemmas, and completeness of the shape enumeration.
- **`native_decide` (trusts Lean's compiler and runtime):** The final finite sweep verifying that no enumerated shape list passes all three axis tests ([SevenSlabs/Discrete.lean](SevenSlabs/Discrete.lean)).

Run the Lean build from this directory with pinned Lean and mathlib 4.35.0:

```sh
lake exe cache get
lake build
```

- **Independent C++17 verification (outside Lean):** A standalone C++ placement search independently tests all 17,366 volume-compatible shape lists and returns zero tilings. As a positive control, the exact same executable finds the 3-slab tiling of a side-6 cube. Two additional C++ programs independently confirm the conclusion using transverse sections ([Placement search](verify/placement_search.cpp) · [Section-area test](verify/bound_profiles.cpp) · [Plane sweep](verify/geom_projection.cpp)):

```sh
c++ -std=c++17 -O2 verify/placement_search.cpp -o /tmp/place-seven-slabs
/tmp/place-seven-slabs
/tmp/place-seven-slabs 3 6
```
