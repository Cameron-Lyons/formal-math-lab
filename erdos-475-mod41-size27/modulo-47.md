# Graham’s rearrangement conjecture modulo 47

**Theorem.** Every subset of the 46 nonzero residues modulo 47 has an ordering whose nonempty partial sums are pairwise distinct.

Two independent C++20 computations prove the zero-sum case. The first joins paths through disjoint sets of vertices. The second inserts opposite pairs of steps into cycles. Both replay the orderings they use with ordinary modular addition. The proof for arbitrary subsets then follows by the same replacement argument as at 41 and 43. [First verifier](verify_half_paths.cpp) · [Second verifier](verify_splices.cpp) · [Reduction to zero sum](README.md#reduction-to-sets-of-sum-zero)

## Joining two paths

Let $H=\{2^j\bmod 47:0\le j<23\}$. Since $2^{23}\equiv1\pmod{47}$, $23$ is prime, and $2\ne1$, this is a subgroup of order 23. The sets $H$ and $-H$ partition the nonzero residues. Write a zero-sum set uniquely as $S=X\cup(-Y)$ with $X,Y\subseteq H$. Then $\sum X=\sum Y=s$ in the field.

Suppose $s\ne0$. Multiplication by an element of $H$ preserves the two halves and lets us take $s=1$ or $s=-1$, according to its coset. For either endpoint $s$, choose a set of internal vertices $R$ that omits $0,s$ and is disjoint from its reflection $s-R$. If both $X$ and $Y$ admit paths from $0$ to $s$ with all internal vertices distinct and in $R$, traverse the steps of $X$, then the negatives of the steps of $Y$ **in the same order**. The second path runs from $s$ to $0$ and its interior lies in $s-R$. This gives a simple cycle using precisely $S$.

If $s=0$ and $S$ is nonempty, negate $S$ if needed to make $X$ nonempty. Choose $a\in X$ and scale by $a^{-1}\in H$, so $1\in X$. Move that step from the first path to the second by taking

$$U=X\setminus\{1\},\qquad V=Y\cup\{-1\}.$$

Now $\sum U=\sum V=-1$ and $U\cup(-V)=S$ in the normalized coordinates. The two step sets $U$ and $-V$ are disjoint because $U$ omits $1$. The same path test applies. The empty set has the empty ordering.

**Finite check.** For each endpoint the verifier builds 32 sets $R$, choosing one vertex from every two-element reflection pair away from $0,s$ and omitting the midpoint. For each possible half it records the regions in which it actually found and replayed a path. Any two halves whose records share a region give a cycle by the argument above. If their records have more than 32 successes in total, they automatically intersect. The verifier compares the other records and directly finds and replays a full cycle for each pair left over. A search cutoff can leave a region unmarked. Finishing the proof requires a witness for every remaining pair. [Path searches and coverage check](verify_half_paths.cpp)

| Common sum | Ordered pairs covered | Pairs requiring direct cycles |
| --- | ---: | ---: |
| $1$ | 31,855,467,361 | 1,158 |
| $-1$ | 31,855,467,361 | 364,077 |
| $0$, after moving one step | 15,927,912,162 | 269,132 |

Together the three rows required 634,367 direct cycle checks. [Path verifier transcript](modulo-47-paths.txt)

The pair counts have a simple independent check. The binary digits of an integer $0\le b<2^{23}$ specify a subset of $H$, with sum $b\bmod47$. As $2^{23}=47\cdot178481+1$, there are 178,481 subsets at every nonzero sum and 178,482 at zero. Complementing inside $H$ preserves sum zero and toggles membership of $1$. Thus there are 89,241 possible $U$ in the transfer and 178,482 possible $V$. Different choices of the transferred step can represent the same original set. Before any scaling the number of distinct zero-sum sets is $178482^2+46\cdot178481^2=1{,}497{,}207{,}322{,}930$.

## Inserting opposite pairs

Remove all complete pairs $\{x,-x\}$ from a zero-sum set to obtain its zero-sum subset of unpaired steps $C$. A cycle for $C$ can sometimes accommodate many optional pairs at once. Given an edge $u\to v$ and an offset $e\in\{x,-x\}$, replace that edge by the path $u,u+e,v+e,v$. Its steps are $e,v-u,-e$. If the insertions use distinct edges and all new vertices are distinct and off the original cycle, any subcollection of insertions gives a simple cycle. The checker replays the base cycle and the fully expanded cycle. When it cannot certify simultaneous insertions it branches on including or omitting one pair and verifies both resulting families. [Insertion verifier](verify_splices.cpp)

To enumerate $C$, each magnitude $1,\ldots,23$ contributes either sign or no singleton. The verifier joins two lists to enforce sum zero. Let $T=\sum_{x\in C}x^{-1}$ and $D=\sum_{x\in C}x^3$. If $T\ne0$, dilation uniquely normalizes $T$ to 1. If $T=0$ and $D\ne0$, dilation uniquely normalizes $D$ to 1 because cubing permutes the nonzero residues modulo 47. Each normalized set in these cases represents 46 sets before scaling. When both sums vanish the verifier keeps every core with weight one. The total count must equal the independent zero-sum count above.

The run certified 51,812,777 families and recovered all 1,497,207,322,930 zero-sum sets. To check each row independently, start with one empty set of sum zero. For each magnitude $x$, choosing neither sign or both signs preserves the sum and singleton count. Choosing one sign adds one singleton and shifts the sum by $x$ or $-x$. This recurrence gives all 24 counts in the final column. [Insertion verifier transcript](modulo-47-splices.txt)

## Reproduce

From this directory, run either verifier with a C++20 compiler. Each command below writes a fresh transcript and compares it with the recorded run. Both proofs cover every subset size. These are computer-assisted proofs using compiled C++.

~~~sh
c++ -std=c++20 -O3 -Wall -Wextra -Werror -pedantic verify_half_paths.cpp -o /tmp/graham47-paths
/tmp/graham47-paths > /tmp/graham47-paths.txt && diff -u modulo-47-paths.txt /tmp/graham47-paths.txt

c++ -std=c++20 -O3 -Wall -Wextra -Werror -pedantic verify_splices.cpp -o /tmp/graham47-splices
/tmp/graham47-splices > /tmp/graham47-splices.txt && diff -u modulo-47-splices.txt /tmp/graham47-splices.txt
~~~
