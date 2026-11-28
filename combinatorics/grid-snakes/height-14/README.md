# Longest Snakes on a $14 \times n$ Grid

On a grid with 14 rows and $n$ columns, a **snake** (an **induced path** in the grid graph) is a path of distinct squares in which consecutive squares share a horizontal or vertical edge and **no two non-consecutive squares touch orthogonally** (diagonal corner touches are fine, but touching along an edge is forbidden).

Let $L(n)$ be the maximum number of squares in a snake on a $14 \times n$ grid. Write $n = 6q + r$ with $0 \le r < 6$. Then for **every width $n \ge 18$**,

$$
L(n) = 52q + c_r, \qquad (c_0, c_1, c_2, c_3, c_4, c_5) = (3, 12, 20, 30, 38, 47).
$$

Remarkably, the exact same formula also holds for all smaller positive widths **except eight explicit exceptions**:

| $n$ | 1 | 2 | 5 | 10 | 11 | 13 | 14 | 17 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| $L(n)$ | 14 | 21 | 46 | 89 | 98 | 115 | 123 | 150 |

Outside those eight exceptions, the formula simplifies to a single closed-form expression:

$$
L(n) = \left\lfloor \frac{26n + 11 - (-1)^n}{3} \right\rfloor.
$$

In particular, adding 6 columns adds **exactly 52 squares** — $L(n + 6) = L(n) + 52$ — for every $n \ge 18$ (approaching density $\frac{52}{14 \times 6} = \frac{13}{21} \approx 61.9\%$). The onset $n \ge 18$ is **sharp**, because $L(23) - L(17) = 203 - 150 = 53$.

| | |
| --- | --- |
| **Result** | Exact formula for $L(n)$ on every $14 \times n$ grid ($n \ge 1$), with 8 small-width exceptions |
| **Periodicity** | $L(n + 6) = L(n) + 52$ for every $n \ge 18$ (sharp onset) |
| **Lean 4 formalization** | Theorem `Height14.longest_snake` in [lean/Height14.lean](lean/Height14.lean) (Lean 4.36.0 + stdlib; finite checks use `native_decide`) |
| **Prior context** | First 16 values match [OEIS A360917 data](https://oeis.org/A360917/b360917.txt); follows [Niu, §8](https://arxiv.org/html/2611.26640v1#S8) (heights $\le 12$) and [Height-13 proof](../height-13/README.md) |

---

## Lean 4 formal proof

The main theorem `Height14.longest_snake` ([Main theorem](lean/Height14.lean)) proves both directions for every positive width $n$:

1. **Lower bound:** there exists a valid snake of length `formula n` ([Length formula](lean/Height14/Formula.lean)), and
2. **Upper bound:** every valid snake has length at most `formula n`.

Formally, a snake is a nonempty list of distinct grid squares in which two squares share an edge if and only if they are consecutive in the list ([Grid path definition](lean/Height14/Path.lean)).

**How the Lean proof works:**

- **Lower bound ([Construction](lean/Height14/Witness.lean)):** Constructs explicit base snakes and splices in a repeatable 52-square, 6-column path segment as many times as needed.
- **Upper bound ([Grid-to-boundary proof](lean/Height14/Grid.lean), [Propagation](lean/Height14/Pumping.lean)):** Proves structurally that scanning any grid snake column by column follows the boundary state-transition table, then checks the transition table ([Transition check](lean/Height14/RefinementCert.lean)) and computes optimal continuation scores **backwards** ([Score check](lean/Height14/Certificate.lean)). For every boundary state, the best continuation through **46** columns adds at most **52** more squares than the best continuation through **40** columns; by induction, that upper bound propagates each time another column is prepended.

### Building the Lean proof

From this directory, run:

```sh
cd lean
lake build
```

**Environment and trust boundary:** The package uses **Lean 4.36.0** and its standard library. Lean computes all tables from source, and the finite table/score checks use `native_decide`, so they trust Lean's compiler and native runtime.

---

## References

- [OEIS A360917 data](https://oeis.org/A360917/b360917.txt) (first 16 widths agree)
- [Tong Niu, §8 — fixed-height snakes through height 12](https://arxiv.org/html/2611.26640v1#S8)
- [Height-13 proof](../height-13/README.md)
