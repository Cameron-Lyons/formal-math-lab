# Graham's rearrangement problem modulo 43

**Theorem.** Every subset of the nonzero residues modulo 43 has an ordering with distinct nonempty partial sums.

By the zero-sum reduction, it suffices to order sets $A$ with $\sum A=0$. For such a set, let $t=\sum_{a\in A}a^{-1}$ modulo 43. If $t\ne0$, multiplying every element of $A$ by $t$ makes its reciprocal sum $1$. Scaling also multiplies every partial sum by the same factor. Thus it suffices to check zero-sum sets with reciprocal sum **0 or 1**. [Zero-sum reduction](README.md#reduction-to-sets-of-sum-zero)

The verifier lists subsets of $\{1,\ldots,21\}$ and of $\{22,\ldots,42\}$ and joins halves with the required totals. Each qualifying set occurs exactly once, including the empty and full sets. It found and replayed a valid ordering for **all 4,757,514,809 qualifying sets**. This proves the theorem. [Verifier](verify_reciprocal.cpp)

~~~sh
c++ -std=c++20 -O3 -march=native -fopenmp -DGRAHAM_PRIME=43 verify_reciprocal.cpp -o /tmp/graham43
/tmp/graham43
~~~

An independent verification used rotations of subsets in the order of powers of 3. It found 2,784,081,790 cycles and matched the expected count at every searched size. To reproduce that check, compile the rotation verifier with the same flags and run it with `--all`. The command below audits its saved transcript. [Rotation argument](zero-sum.md) · [Rotation verifier](verify_zero_sum.cpp) · [Per-size counts](modulo-43-counts.txt)

~~~sh
python3 verify_counts.py --prime 43 modulo-43-counts.txt
~~~
