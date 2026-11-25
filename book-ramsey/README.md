# Book Ramsey number R(B_63, B_64): 253 <= R(B_63, B_64) <= 255 and circulant obstructions — Lean 4 proofs

**Status: $253 \le R(B_{63}, B_{64}) \le 255$ is verified in Lean 4; the exact value remains open.** A book graph $B_k$ consists of $k$ triangles sharing a common edge (spine). The book Ramsey number $R(B_{63}, B_{64})$ is the smallest $N$ such that every red–blue edge coloring of $K_N$ contains a red $B_{63}$ or a blue $B_{64}$. Constructing a 254-vertex graph with no red $B_{63}$ and no blue $B_{64}$ would establish $R(B_{63}, B_{64}) = 255$ (listed as open in Chung and Wesley, `arXiv:2610.36522`).

This Lean 4 project certifies Dai and Lin's 252-vertex lower-bound graph ($R(B_{63}, B_{64}) \ge 253$), proves Rousseau and Sheehan's upper bound ($R(B_{63}, B_{64}) \le 255$), excludes 254-vertex candidates built from two identical circulant layers joined by a circulant cross-block (covering both groups of order 254 and, via McKay–Praeger's classification, all vertex-transitive graphs of order 254), and ships a compiled candidate verifier.

| Field | Summary |
| --- | --- |
| **Problem & identifiers** | **Book Ramsey number** `R(B_63, B_64)` (`R(B63, B64)`, $R(B_{63}, B_{64})$), bounds `253 <= R(B_63, B_64) <= 255`, Chung–Wesley (`arXiv:2610.36522`, Appendix A), Dai–Lin (`arXiv:2606.07214`, Theorem 1.1), Rousseau–Sheehan (`R(B_{n-1}, B_n) <= 4n - 1`) |
| **Status** | **Bounds verified ($253 \le R(B_{63}, B_{64}) \le 255$) and circulant/Cayley obstruction at 254 proved; existence of a 254-vertex witness remains open.** |
| **Main Lean theorems** | `BookRamsey.Lower252.exists_252` ([Lower252.lean](Lower252.lean)), `BookRamsey.Upper255.upper` ([Upper255.lean](Upper255.lean)), `BookRamsey.DegreeObstruction.no_identical_circulant_layers` ([CayleyObstruction.lean](CayleyObstruction.lean)) |
| **Verification** | `lake build && lake exe verify witness252.txt 252 63 64` (Lean 4.36.0, stdlib only; pure kernel proofs) |
| **Prior-art status** | Checked **23 November 2026**: the 252-vertex lower bound follows Dai–Lin and the upper bound 255 follows Rousseau–Sheehan; Chung–Wesley list the 254-vertex construction as open. See [PRIOR_ART.md](../PRIOR_ART.md). |

## Lean results

| Lean declaration | File | What it proves |
| --- | --- | --- |
| `BookRamsey.Lower252.exists_252` | [Lower252.lean](Lower252.lean) | Certifies a 252-vertex graph from Dai and Lin's conference-matrix construction (`witness252.txt`): every edge in either color has at most 62 common neighbors in its own color (`avoids_63_both` also proves no $B_{63}$ in either color). |
| `BookRamsey.Upper255.upper` | [Upper255.lean](Upper255.lean) | Every graph on 255 vertices contains a red $B_{63}$ or a blue $B_{64}$ (avoiding both forces all 255 vertices to have red degree 127, contradicting handshaking parity). |
| `BookRamsey.DegreeObstruction.no_identical_circulant_layers` | [CayleyObstruction.lean](CayleyObstruction.lean) | Rules out 254-vertex candidates formed from two identical 127-vertex circulant layers joined by a circulant cross-block (covering both groups of order 254; with McKay–Praeger's Theorem 1(b) for $2p$ with $p = 127 \equiv 3 \pmod 4$, this rules out every vertex-transitive graph of order 254). |

## Verification

Run from this directory with Lean **4.36.0** (standard library only):

```sh
lake build
lake exe verify witness252.txt 252 63 64
```

To test any 254-vertex candidate graph, run `lake exe verify candidate.txt`. Supply 254 rows of 254 binary digits (`1` for red edges, `0` on the diagonal, symmetric); the verifier reports the largest book and number of violating spines in each color. [Verifier source](Verify.lean) · [Adjacency matrix](witness252.txt)

## References

* [Chung and Wesley, `arXiv:2610.36522v1`, Introduction & Appendix A](https://arxiv.org/html/2610.36522v1)
* [Dai and Lin, `arXiv:2606.07214v1`, Theorem 1.1](https://arxiv.org/html/2606.07214v1)
* [McKay and Praeger, vertex-transitive graphs of order $2p$, Theorem 1(b)](https://users.cecs.anu.edu.au/~bdm/papers/cheryl1.pdf)
* [Dated prior-art audit](../PRIOR_ART.md)
