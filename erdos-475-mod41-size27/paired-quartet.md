# Graham orderings with at most four omitted residues

**Theorem.** At every prime $p$, each set $A\subseteq\mathbb F_p^\times$ omitting at most four residues has an ordering with distinct nonempty partial sums.

Let $p=2h+1$ be odd, and first suppose $A$ sums to zero. Pair each step with its negative whenever possible. Each unpaired step accounts for a different omission, so there are at most four. Their sum is zero, so there are either none, three or four.

**Put the pairs in order.** If three steps remain, add a temporary zero. Split the four remaining steps, if any, into two pairs. Neither pair sums to zero, so scale all steps to make the two pair sums $1$ and $-1$. In the range $[-h,h]$, two distinct representatives have sum between $2-p$ and $p-2$. Hence the sums $1$ and $-1$ hold as integers. Each of these pairs has opposite signs and consecutive magnitudes, counting zero as the missing sign.

Every ordinary opposite pair uses a single magnitude, and different pairs share no magnitude. Their intervals are therefore disjoint. List the pairs from largest to smallest. A pair containing zero comes last, and all steps together sum to zero as integers.

**Read off the ordering.** Take one step from each pair, alternating signs from positive. Take the unused step of the largest pair as a bridge, then the remaining steps from smallest pair to largest. Skip the temporary zero. The empty set needs no steps.

Before the bridge, the steps alternate from positive with strictly decreasing magnitudes. Each new endpoint after the first lies strictly inside the preceding edge, so the partial sums are distinct in $[1,h]$. Now read backwards from the final zero to the end of the bridge. Those steps alternate from negative with strictly decreasing magnitudes, so the remaining partial sums are distinct in $[-h,0]$. The temporary zero, when present, was last in one of these two lists, so skipping it preserves the alternation. The two intervals are disjoint modulo $p$, and undoing the scaling preserves distinctness.

**For a set of nonzero total $s$**, put $X=A\cup\{0\}$. This is a proper subset of the field, since the full set of nonzero residues sums to zero. Subtracting $s$ cycles through the field, so some $a\in X$ has $b=a-s\notin X$. The set $(A\setminus\{a\})\cup\{b\}$ sums to zero and has at most as many omissions. Its ordering traces a simple cycle, so rotate it to start with $b$, then replace $b$ by $a$. Every nonempty partial sum shifts by $s$, so they stay distinct. If $a=0$, discard the initial zero. At $p=2$ both subsets work directly.

For example, modulo 13 the pairs $(+6,-5),(+4,-4),(+2,-3),(+1,-1)$ give the order $6,-4,2,-1,\,-5,\,1,-3,4$. Its nonempty partial sums are $6,2,4,3,\,-2,-1,-4,0$.

The same proof works for any collection of opposite pairs together with three or four unpaired residues of sum zero. The executable constructor checks each ordering it returns. [Constructor and tests](paired_triple.py)

~~~sh
python3 paired_triple.py --through 257
~~~
