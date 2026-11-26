# Book Ramsey number R(B_63, B_64)

A book graph $B_k$ is $k$ triangles sharing one edge (the spine). The book Ramsey number $R(B_{63}, B_{64})$ is the smallest $N$ such that every red-blue edge coloring of $K_N$ contains a red $B_{63}$ or a blue $B_{64}$. A 254-vertex graph with no red $B_{63}$ and no blue $B_{64}$ would prove $R(B_{63}, B_{64}) = 255$, which Chung and Wesley (`arXiv:2610.36522`) list as open.

This package verifies Dai and Lin's 252-vertex lower-bound graph ($R(B_{63}, B_{64}) \ge 253$) and proves Rousseau and Sheehan's upper bound ($R(B_{63}, B_{64}) \le 255$). It also rules out 254-vertex graphs built from two identical circulant layers joined by a circulant cross-block. That covers both groups of order 254 and, via McKay and Praeger's classification, all vertex-transitive graphs of order 254. A compiled verifier for candidate graphs is also included. The exact value remains open between 253 and 255.

| Field | Summary |
| --- | --- |
| Problem | Book Ramsey number $R(B_{63}, B_{64})$, Chung and Wesley (`arXiv:2610.36522`, Appendix A), Dai and Lin (`arXiv:2606.07214`, Theorem 1.1), Rousseau and Sheehan ($R(B_{n-1}, B_n) \le 4n - 1$) |
| Status | $253 \le R(B_{63}, B_{64}) \le 255$ verified and circulant/Cayley obstruction at 254 proved; existence of a 254-vertex witness remains open. |
| Main theorems | `BookRamsey.Lower252.exists_252` ([Lower252.lean](Lower252.lean)), `BookRamsey.Upper255.upper` ([Upper255.lean](Upper255.lean)), `BookRamsey.DegreeObstruction.no_identical_circulant_layers` ([CayleyObstruction.lean](CayleyObstruction.lean)) |
| Verification | `lake build && lake exe verify witness252.txt 252 63 64` (Lean 4.36.0, stdlib only; pure kernel proofs) |
| Prior art | Checked 23 November 2026: the 252-vertex lower bound follows Dai and Lin and the upper bound 255 follows Rousseau and Sheehan; Chung and Wesley list the 254-vertex construction as open. See [PRIOR_ART.md](../PRIOR_ART.md). |

## Lean results

| Lean declaration | File | What it proves |
| --- | --- | --- |
| `BookRamsey.Lower252.exists_252` | [Lower252.lean](Lower252.lean) | Checks a 252-vertex graph from Dai and Lin's conference-matrix construction (`witness252.txt`): every edge in either color has at most 62 common neighbors in its own color (`avoids_63_both` also proves no $B_{63}$ in either color). |
| `BookRamsey.Upper255.upper` | [Upper255.lean](Upper255.lean) | Every graph on 255 vertices contains a red $B_{63}$ or a blue $B_{64}$ (avoiding both forces all 255 vertices to have red degree 127, breaking handshaking parity). |
| `BookRamsey.DegreeObstruction.no_identical_circulant_layers` | [CayleyObstruction.lean](CayleyObstruction.lean) | Rules out 254-vertex graphs made of two identical 127-vertex circulant layers joined by a circulant cross-block. This covers both groups of order 254, and with McKay and Praeger's Theorem 1(b) for $2p$ ($p = 127 \equiv 3 \pmod 4$) rules out every vertex-transitive graph of order 254. |

## Verification

Run from this directory with Lean 4.36.0 (stdlib only):

```sh
lake build
lake exe verify witness252.txt 252 63 64
```

To test a 254-vertex candidate graph, run `lake exe verify candidate.txt`. Give 254 rows of 254 binary digits (`1` for red edges, `0` on the diagonal, symmetric); the verifier prints the largest book and the number of violating spines in each color ([Verify.lean](Verify.lean), [witness252.txt](witness252.txt)).

## References

* [Chung and Wesley, `arXiv:2610.36522v1`, Introduction and Appendix A](https://arxiv.org/html/2610.36522v1)
* [Dai and Lin, `arXiv:2606.07214v1`, Theorem 1.1](https://arxiv.org/html/2606.07214v1)
* [McKay and Praeger, vertex-transitive graphs of order $2p$, Theorem 1(b)](https://users.cecs.anu.edu.au/~bdm/papers/cheryl1.pdf)
* [Prior-art audit](../PRIOR_ART.md)
