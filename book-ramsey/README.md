# Book Ramsey number $R(B_{63}, B_{64})$

A **book graph** $B_k$ consists of $k$ triangles all glued along a single shared edge—visualize a physical book whose binding is that shared edge (the **spine**) and whose $k$ triangles are its **pages**. In a red-blue coloring of the edges of the complete graph $K_N$, a red edge $uv$ serves as the spine of a red $B_k$ precisely when $u$ and $v$ have at least $k$ common neighbors joined to both of them by red edges.

The **book Ramsey number** $R(B_{63}, B_{64})$ is the smallest vertex count $N$ such that every red-blue edge coloring of $K_N$ forces either a red $B_{63}$ or a blue $B_{64}$. Constructing a 254-vertex coloring avoiding both a red $B_{63}$ and a blue $B_{64}$ would settle $R(B_{63}, B_{64}) = 255$, a question Chung and Wesley (`arXiv:2610.36522`) list as open.

This Lean 4 package formally verifies the known tight window $253 \le R(B_{63}, B_{64}) \le 255$—checking Dai and Lin's 252-vertex witness for the lower bound and proving Rousseau and Sheehan's 255-vertex upper bound—and proves a strong symmetry obstruction at order 254 ruling out all vertex-transitive graphs. It also includes a compiled verifier for testing candidate graphs. Whether a 254-vertex witness exists (and thus whether $R(B_{63}, B_{64})$ is 253, 254, or 255) remains open.

| Field | Summary |
| --- | --- |
| Problem | Book Ramsey number $R(B_{63}, B_{64})$, Chung and Wesley (`arXiv:2610.36522`, Appendix A), Dai and Lin (`arXiv:2606.07214`, Theorem 1.1), Rousseau and Sheehan ($R(B_{n-1}, B_n) \le 4n - 1$) |
| Status | $253 \le R(B_{63}, B_{64}) \le 255$ verified and circulant/Cayley obstruction at 254 proved; existence of a 254-vertex witness remains open. |
| Main theorems | `BookRamsey.Lower252.exists_252` ([Lower252.lean](Lower252.lean)), `BookRamsey.Upper255.upper` ([Upper255.lean](Upper255.lean)), `BookRamsey.DegreeObstruction.no_identical_circulant_layers` ([CayleyObstruction.lean](CayleyObstruction.lean)) |
| Verification | `lake build` (Lean 4.36.0, stdlib only; pure kernel proofs) |
| Prior art | Checked 23 November 2026: the 252-vertex lower bound follows Dai and Lin and the upper bound 255 follows Rousseau and Sheehan; Chung and Wesley list the 254-vertex construction as open. |

## Lean results

*(Recall that a **circulant graph** on $m$ vertices places its vertices around a cycle $\mathbb{Z}/m\mathbb{Z}$ and connects pairs whose cyclic difference lies in a fixed set, and a **vertex-transitive graph** is one whose symmetries can map any vertex to any other vertex.)*

| Lean declaration | File | What it proves |
| --- | --- | --- |
| `BookRamsey.Lower252.exists_252` | [Lower252.lean](Lower252.lean) | Verifies a 252-vertex graph from Dai and Lin's conference-matrix construction: every edge in either color has at most 62 common neighbors in its own color (`avoids_63_both` in fact proves no $B_{63}$ in either color), establishing $R(B_{63}, B_{64}) \ge 253$. |
| `BookRamsey.Upper255.upper` | [Upper255.lean](Upper255.lean) | Proves $R(B_{63}, B_{64}) \le 255$: avoiding both a red $B_{63}$ and a blue $B_{64}$ on 255 vertices forces every single vertex to have red degree 127. That breaks handshaking parity, since the sum of all red degrees would be $255 \times 127 = 32{,}385$ (odd), which can never equal twice the number of red edges. |
| `BookRamsey.DegreeObstruction.no_identical_circulant_layers` | [CayleyObstruction.lean](CayleyObstruction.lean) | Rules out all 254-vertex graphs built from two identical 127-vertex circulant layers joined by a circulant cross-block. This covers both groups of order 254, and combined with McKay and Praeger's Theorem 1(b) for order $2p$ ($p = 127 \equiv 3 \pmod 4$), rules out **every** vertex-transitive graph of order 254. |

## Verification

Run from this directory with Lean 4.36.0 (stdlib only; all theorems are pure kernel proofs):

```sh
lake build
```

To test any 254-vertex candidate graph, run `lake exe verify candidate.txt`. Format the input as 254 lines of 254 binary digits (`1` for red edges, `0` on the diagonal, symmetric adjacency matrix); the verifier reports the largest book and the number of violating spines in each color ([Verify.lean](Verify.lean)).

## References

- [Chung and Wesley, `arXiv:2610.36522v1`, Introduction and Appendix A](https://arxiv.org/html/2610.36522v1)
- [Dai and Lin, `arXiv:2606.07214v1`, Theorem 1.1](https://arxiv.org/html/2606.07214v1)
- [McKay and Praeger, vertex-transitive graphs of order $2p$, Theorem 1(b)](https://users.cecs.anu.edu.au/~bdm/papers/cheryl1.pdf)
