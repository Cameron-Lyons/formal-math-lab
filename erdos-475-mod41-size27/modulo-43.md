# Graham's rearrangement problem modulo 43

Every subset of the nonzero residues modulo $43$ can be ordered so that its walk of running sums never revisits a vertex (except on the final return to $0$ when the set sums to zero).

**Theorem.** Every subset of the nonzero residues modulo $43$ has an ordering with distinct nonempty partial sums.

## Proof via reciprocal-sum normalization

Two elementary reductions collapse the $2^{42}$ subsets of $\mathbb{F}_{43}^\times$ into a tractable exhaustive check:

1. **Reduce to sum zero.** By the [zero-sum reduction](README.md#reduction-to-sets-of-sum-zero), it suffices to find a valid ordering for every subset $A \subseteq \mathbb{F}_{43}^\times$ with $\sum_{a \in A} a \equiv 0 \pmod{43}$.
2. **Normalize the reciprocal sum.** For such a zero-sum set $A$, define its reciprocal sum
   $$t = \sum_{a \in A} a^{-1} \pmod{43}.$$
   Multiplying every element of $A$ by a nonzero constant multiplies every partial sum by that same constant, preserving distinctness and the zero-sum property, while dividing the reciprocal sum by that constant. Whenever $t \ne 0$, the scaled set $tA$ has reciprocal sum $1$. It therefore suffices to verify only zero-sum sets whose reciprocal sum is **0 or 1**.

**Exhaustive check.** The C++20 verifier ([verify_reciprocal.cpp](verify_reciprocal.cpp)) splits $\mathbb{F}_{43}^\times$ into two equal halves, $\{1, \ldots, 21\}$ and $\{22, \ldots, 42\}$, lists all $2^{21}$ subsets of each half, and joins pairs whose ordinary sums total $0$ and whose reciprocal sums total $0$ or $1$. Every qualifying set splits uniquely across the two halves and therefore appears exactly once, including the empty and full sets.

The verifier found and independently replayed a valid ordering for **all 4,757,514,809 qualifying sets**, completing the proof of the theorem. $\square$

## Reproduction

Run from this directory with a C++20 compiler (OpenMP is optional):

~~~sh
c++ -std=c++20 -O3 -march=native -fopenmp -DGRAHAM_PRIME=43 verify_reciprocal.cpp -o /tmp/graham43
/tmp/graham43
~~~
