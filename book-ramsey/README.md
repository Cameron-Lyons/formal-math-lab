# The book Ramsey number R(B₆₃, B₆₄)

A book $B_k$ consists of $k$ triangles sharing an edge. Lean verifies
**253 ≤ R(B₆₃, B₆₄) ≤ 255**. Finding a graph on 254 vertices with no red
$B_{63}$ and no blue $B_{64}$ would settle the value at 255.
[Chung and Wesley, Appendix A](https://arxiv.org/html/2610.36522v1)

- `BookRamsey.Lower252.exists_252` certifies a 252-vertex graph from Dai and Lin’s construction. The maximum number of common neighbors of an edge in its own color is 62 in each color. [Lean proof](Lower252.lean) · [Adjacency matrix](witness252.txt) · [Dai and Lin, Theorem 1.1](https://arxiv.org/html/2606.07214v1)
- `BookRamsey.Upper255.upper` proves that every graph on 255 vertices contains a red $B_{63}$ or a blue $B_{64}$. Avoiding both would force all 255 vertices to have degree 127, contradicting the parity of the degree sum. [Lean proof](Upper255.lean)
- `BookRamsey.DegreeObstruction.no_identical_circulant_layers` rules out 254-vertex candidates with two identical circulant layers joined by a circulant block. [Lean proof](CayleyObstruction.lean)

## Verification

Run these commands in this directory to build the proofs and check the supplied witness.

```sh
lake build
lake exe verify witness252.txt 252 63 64
```

For a 254-vertex candidate, run `lake exe verify candidate.txt`. Supply one row
of 254 binary digits per vertex, with a symmetric matrix, zeros on the diagonal,
and ones for red edges. The verifier reports the largest book and the number of
violating spines in each color.
