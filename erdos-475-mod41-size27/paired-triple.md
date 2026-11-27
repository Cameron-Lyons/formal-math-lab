# Graham orderings with at most three omitted residues

**Theorem.** For every prime $p$, every $A\subseteq\mathbb F_p^\times$ that omits at most three nonzero residues has an ordering with distinct nonempty partial sums. In particular this holds at size $p-4$ for every prime $p\ge5$.

The construction also applies to much smaller sets. If a zero-sum set consists of any number of complete pairs $\{a,-a\}$ together with three unpaired elements, its steps form a simple cycle. The proof below is independent of the modulo-41 computation. [Erdős problem #475](https://www.erdosproblems.com/475) · [Witness constructor](paired_triple.py)

## A cycle for inverse pairs

Write $p=2m+1$. Represent each pair by its unique positive magnitude in $[1,m]$. Let $D$ be the largest magnitude of a nonempty collection of pairs. List the smaller magnitudes as $d_1>d_2>\cdots>d_j$. Start an integer path $P$ at zero and take steps $d_1,-d_2,d_3,-d_4,\ldots$. After the first step, each new point lies strictly inside the interval spanned by the preceding edge. Thus the vertices are distinct, lie in $[0,d_1]$, and the intervals between successive vertices are nested. If $j=0$, take $P$ to be the single vertex zero.

Traverse $P$, jump by $D$, traverse the translated path $P+D$ backwards, then jump by $-D$ to zero. The two paths are disjoint, one in $[0,D-1]$ and one in $[D,2D-1]$. These integer positions stay distinct modulo $p$. Each smaller magnitude occurs once in each direction, and the bridges use $D$ and $-D$. This folding construction occurs in the proof of Lemma 3.4 of Alspach, Gavlas, Šajna, and Verrall. [Cycle decompositions IV (2003), pp. 170–171](https://core.ac.uk/download/pdf/81154598.pdf#page=6)

## Inserting three unpaired elements

Suppose the three unpaired elements sum to zero. Multiply all the residues by the inverse of one of them. In the signed representatives $[-m,m]$, the triple is now $1,r,-(r+1)$ for some $2\le r<m$. Indeed, the other two representatives sum to $-1$ modulo $p$. Their integer sum cannot equal $2m$ since they are distinct, and cannot be as small as $-1-p$. It is therefore $-1$. Their signs are opposite and neither can be $1$ or $-1$.

Keep all the original pairs and introduce the pair $\pm L$, where $L=r+1$. This gives a symmetric set of steps containing neither magnitude $1$ nor magnitude $r$. Construct the folded cycle above. We will replace its positive step $L$ by two steps $1$ and $r$, in a suitable order. Its negative step $-L$ stays in the cycle.

* If $L<D$, consider the edge of length $L$ from $u$ to $v$ on the original path $P$. The integer point one unit inside the edge from $u$ is free. Earlier vertices lie outside the open interval between $u$ and $v$ by nesting. If another edge follows, its length is at most $L-2$, since magnitude $L-1=r$ is absent. All later points therefore lie in a subinterval within $L-2$ of $v$. Our point is $L-1$ from $v$. The same free point exists on the translated copy. The positively directed occurrence of this edge can now pass through the free point in its own copy, using $1,r$ or $r,1$ according to the direction of traversal.
* If $L=D$, reverse the folded cycle so that its bridge from $0$ to $L$ is traversed in the positive direction. Reversal preserves the symmetric step set. All smaller magnitudes are at most $L-2$, so $L-1=r$ is free between the two paths. Replace the bridge by $0,r,L$.

In both cases the extra vertex is distinct from every old vertex. The resulting closed cycle uses exactly the required steps. Undo the scaling to obtain a cycle for the original set.

For example modulo 13, the steps $5,9,2,6,11,3,1,8,7$ give running sums $5,1,3,9,7,10,11,6,0$. Here the unpaired triple is $1,3,-4$, and the positive step $4$ in the symmetric cycle was split into $3,1$.

## Passing from zero total to all totals

Suppose $p\ge7$. The sum of all nonzero residues is zero. If a set of size $p-4$ has sum zero, its three omitted elements sum to zero. No two of them are opposites, as that would force the third to be zero. Hence their three negatives are the only unpaired elements of the set, and the preceding construction applies. At size $p-3$, the two omitted elements of a zero-sum set must be opposites, leaving only complete pairs. The same-size replacement argument now covers all nonzero totals at both sizes. Sizes $p-2$ and $p-1$ follow from the geometric ordering. At $p=5$ every ordering of two distinct nonzero steps has distinct nonempty partial sums, and the size $p-4$ case is a singleton. At $p=2,3$ all cases are immediate. [Replacement argument and endpoint sizes](README.md#reduction-to-sets-of-sum-zero)

The constructor uses integer arithmetic and rechecks the running sums of each witness. The first command below prints a witness. The second tests all 43,118 sets omitting at most three residues at primes through 43. It also exercises the normalized triple construction through prime 257.

~~~sh
python3 paired_triple.py --example 13 1 2 3 5 6 7 8 9 11
python3 paired_triple.py --through 257
~~~
