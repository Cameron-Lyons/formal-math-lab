# Graham’s rearrangement conjecture modulo 47

At $p = 47$, there are nearly $1.5 \times 10^{12}$ zero-sum subsets of $\mathbb{F}_{47}^\times$ — far more than at $41$ or $43$. Rather than checking every subset one by one, we split any zero-sum set into two halves (using quadratic residues), build a short walk from $0$ to $1$ for each half inside one of **15 specially chosen regions**, and glue the two walks together into a simple cycle. Each half succeeds in at least **8 of the 15** regions, so by the pigeonhole principle they must share one. This reduces the computer check to just half a million small subsets.

**Theorem.** Every subset of the nonzero residues modulo $47$ has an ordering with pairwise distinct nonempty partial sums.

## Setup and the big idea

By the [reduction to sets of sum zero](README.md#reduction-to-sets-of-sum-zero), it suffices to order every zero-sum subset $S \subseteq \mathbb{F}_{47}^\times$. Geometrically, we want a closed walk starting at $0$ whose steps are the elements of $S$ and whose only repeated vertex is the final return to $0$. The empty set is immediate, so assume $S \ne \emptyset$.

**How two $0 \to 1$ walks glue into a cycle.** Suppose we partition $S$ into $X$ and $-Y$ so that $\sum X = \sum Y = 1 \pmod{47}$, and suppose we have:
* a walk $P_1$ for $X$ from $0$ to $1$, visiting interior vertices $u_1, u_2, \ldots, u_{j-1}$, and
* a walk $P_2$ for $Y$ from $0$ to $1$, visiting interior vertices $v_1, v_2, \ldots, v_{k-1}$.

To turn $P_2$ into a return walk from $1$ back to $0$ using the steps of $-Y$, simply **start at $1$ and take the negatives of $P_2$’s steps in the same order**. If $P_2$ steps by $y_1, y_2, \ldots, y_k$ (with partial sums $v_r = y_1 + \cdots + y_r$), the negated return walk visits
$$1 - v_1, \quad 1 - v_2, \quad \ldots, \quad 1 - v_{k-1}, \quad 1 - 1 = 0.$$
Every interior vertex $v$ of $P_2$ moves to its reflection $1 - v$ across the midpoint $24 \equiv 1/2 \pmod{47}$!

Now choose a region $R \subset \mathbb{F}_{47} \setminus \{0, 1, 24\}$ that contains **exactly one** element from each of the 22 reflection pairs $\{x, 1 - x\}$ ($2 \le x \le 23$; note $1 - x \equiv 48 - x \pmod{47}$). Then $R$ and $1 - R$ are completely disjoint. Even better, because $R$ omits the midpoint $24 = 1 - 24$, the reflected set $1 - (R \cup \{24\}) = (1 - R) \cup \{24\}$ is *still* disjoint from $R$ (and from $\{0, 1\}$). So if $P_1$ stays inside $R$ and $P_2$ stays inside $R \cup \{24\}$, gluing $P_1$ to the negated $P_2$ automatically produces a simple cycle!

## The finite lemma

Let $H \subset \mathbb{F}_{47}^\times$ be the set of 23 nonzero squares (quadratic residues) modulo $47$.

**Lemma (verified by finite search).** There are 15 regions $R$, each containing one residue from every pair $\{x, 1 - x\}$ for $2 \le x \le 23$ and omitting $0, 1, 24$, with the following property:
* For every subset of $H$ or $-H$ with sum $1$, at least **8 of the 15** regions admit an ordering of its steps from $0$ to $1$ whose interior vertices are pairwise distinct and lie in $R$.
* For every subset of $(-H) \cup \{1\}$ with sum $1$, the same holds in at least **8 of the 15** regions when the midpoint $24 = 1/2$ is also permitted as an interior vertex.

**How the finite lemma is verified.** The C++20 program [verify_half_paths.cpp](verify_half_paths.cpp) lists the 15 regions and enumerates every sum-one subset of the two families. To test whether a subset has a valid walk in a given region, it recursively tries each remaining element as the next step, checks that the new vertex lies in the available interior set, removes that vertex from the available pool, and continues until the final step lands at $1$.

All **178,481** sum-one subsets tested in $H$ and all **356,963** in $(-H) \cup \{1\}$ passed ([recorded output](modulo-47-paths.txt)). In the second family, the verifier permits the midpoint $24$ *only* when the subset actually contains $1$; hence the subsets of $(-H) \cup \{1\}$ that omit $1$ simultaneously verify the stricter claim for $-H$ without using $24$.

## Proof of the theorem

1. **Split $S$ by quadratic character.** Because $47 \equiv 3 \pmod 4$, $-1$ is not a square modulo $47$. Hence the squares $H$ and their negatives $-H$ partition $\mathbb{F}_{47}^\times$. Write any nonempty zero-sum set $S$ as
   $$S = X \cup (-Y), \qquad X, Y \subseteq H.$$
   Since $\sum S = 0$, the two subsets $X$ and $Y$ have the same sum $s = \sum X = \sum Y \pmod{47}$.
2. **Ensure $s \ne 0$ by transferring one element if needed.** If $s = 0$, first replace $S$ by $-S$ if necessary so that $X$ is nonempty. Pick any element $a \in X$, delete $a$ from $X$, and adjoin $-a$ to $Y$. Because $-(-a) = a$, the union $S = X \cup (-Y)$ is unchanged, while the new common sum of $X$ and $Y$ becomes $s = -a \ne 0$.
3. **Normalize both halves to sum $1$.** Divide both $X$ and $Y$ by $s \ne 0$ so that both scaled halves have sum $1$:
   * *Without a transfer:* $X, Y \subseteq H$, so $s^{-1}X$ and $s^{-1}Y$ lie in the same square class ($H$ if $s \in H$, or $-H$ if $s \in -H$).
   * *After a transfer:* since $a \in H$, we have $s = -a \in -H$ and hence $s^{-1} \in -H$. Thus the first scaled half $s^{-1}(X \setminus \{a\})$ lies in $-H$, while the second scaled half $s^{-1}(Y \cup \{-a\})$ lies in $(-H) \cup \{1\}$ (the transferred step becomes $(-a)/s = 1$).
4. **Match a region by pigeonhole and glue.** By the finite lemma, the first scaled half admits a $0 \to 1$ walk in at least 8 of the 15 regions (without using $24$), and the second scaled half admits a $0 \to 1$ walk in at least 8 of the 15 regions (using $24$ only when it lies in $(-H) \cup \{1\}$ and contains $1$). Since $8 + 8 = 16 > 15$, some region $R$ works for both halves.

   Follow the first ordering from $0$ to $1$ (interior vertices in $R$), then take the negatives of the second ordering’s steps in the same order to return from $1$ to $0$. The return path’s interior vertices lie in $1 - (R \cup \{24\})$, which is completely disjoint from $R$ and from $\{0, 1\}$. This produces a simple cycle for $s^{-1}S$. Undoing the scaling by $s$ and any initial negation preserves distinctness of partial sums and gives the required ordering of $S$. $\square$

## Reproduce the finite lemma

Run from this directory with a C++20 compiler:

~~~sh
c++ -std=c++20 -O3 -Wall -Wextra -Werror -pedantic verify_half_paths.cpp -o /tmp/graham47-paths
/tmp/graham47-paths > /tmp/graham47-paths.txt && diff -u modulo-47-paths.txt /tmp/graham47-paths.txt
~~~

## Independent splice verification

A second C++ verifier ([verify_splices.cpp](verify_splices.cpp)) independently checks all **1,497,207,322,930** zero-sum subsets of $\mathbb{F}_{47}^\times$ directly by inserting pairs of opposite steps into cycles ([recorded output](modulo-47-splices.txt)).
