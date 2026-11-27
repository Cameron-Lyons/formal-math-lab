# Graham’s rearrangement conjecture modulo 47

**Theorem.** Every subset of the nonzero residues modulo 47 has an ordering with pairwise distinct nonempty partial sums.

It suffices to order the sets of sum zero. For these sets, we need a path whose steps are the elements of the set and whose only repeated vertex is the final return to 0. The empty set is immediate. [Reduction to sets of sum zero](README.md#reduction-to-sets-of-sum-zero)

**The finite lemma.** Let $H$ be the nonzero squares modulo 47. There are 15 regions $R$, each containing one residue from every pair $\{x,1-x\}$ for $2\le x\le23$ and omitting $0,1,24$. For every subset of $H$ or $-H$ with sum 1, at least **8 of the 15** regions admit an ordering of its steps from 0 to 1 with distinct interior vertices in that region. For a sum-one subset of $(-H)\cup\{1\}$ the same holds when the midpoint $24=1/2$ is also available.

The verifier lists the 15 regions and enumerates the subsets of sum 1. To check a path it tries each possible next step, removes the vertex it reaches from the available interior vertices, and continues. The last step must land at 1. The check passes for all 178,481 subsets tested in $H$ and all 356,963 in $(-H)\cup\{1\}$. In the latter family it allows the midpoint only when the set contains 1, so it also verifies the claim for $-H$. [Verifier](verify_half_paths.cpp) · [Recorded output](modulo-47-paths.txt)

**Proof.** Since $47\equiv3\pmod4$, the squares $H$ and their negatives $-H$ partition the nonzero residues. Write a nonempty zero-sum set as $S=X\cup(-Y)$ with $X,Y\subseteq H$. The halves have the same sum $s$. If $s=0$, negate $S$ if necessary so that $X$ is nonempty. Move any $a\in X$ to the other half by deleting $a$ from $X$ and adjoining $-a$ to $Y$. This preserves $S$ and makes the common sum $s=-a\ne0$.

Divide both halves by $s$. They now have sum 1. Without a transfer they lie in the same square class, $H$ or $-H$. After a transfer the first lies in $-H$ and the second in $(-H)\cup\{1\}$, since the transferred step becomes $(-a)/s=1$.

Each half works in at least eight regions, so they share one. Follow the first ordering from 0 to 1, then take the negatives of the second ordering’s steps in the same order. The second path returns from 1 to 0. Its interior lies in $1-(R\cup\{24\})$, disjoint from the first path’s interior in $R$. This gives the required cycle. Undoing the scaling and any initial negation preserves distinctness. $\square$

## Reproduce the finite lemma

Run from this directory with a C++20 compiler.

~~~sh
c++ -std=c++20 -O3 -Wall -Wextra -Werror -pedantic verify_half_paths.cpp -o /tmp/graham47-paths
/tmp/graham47-paths > /tmp/graham47-paths.txt && diff -u modulo-47-paths.txt /tmp/graham47-paths.txt
~~~

A second verifier independently checks all 1,497,207,322,930 zero-sum sets by inserting pairs of opposite steps into cycles. [Insertion verifier](verify_splices.cpp) · [Recorded output](modulo-47-splices.txt)
