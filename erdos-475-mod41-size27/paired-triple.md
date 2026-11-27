# Graham orderings with at most three omitted residues

**Theorem.** At every prime $p$, any $A\subseteq\mathbb F_p^\times$ that omits at most three nonzero residues has an ordering with distinct nonempty partial sums.

A single ordering rule now covers both three and four omissions. Padding a triple with a zero lets it use the same rule as a quartet. The original edge-insertion proof follows below. [Unified proof](paired-quartet.md)

The case $p=2$ is immediate. At an odd prime the zero-sum reduction lets us assume that $A$ sums to zero. Its complement in $\mathbb F_p^\times$ also sums to zero and has at most three elements. It is empty, an opposite pair, or a triple containing no opposite pair. In the first two cases $A$ consists of pairs $\{d,-d\}$. In the third it also has three unpaired elements, the negatives of the omitted triple. They sum to zero. [Zero-sum reduction](README.md#reduction-to-sets-of-sum-zero)

### Make a cycle from opposite pairs

Write the positive representatives of the pairs in decreasing order $D=d_1>d_2>\cdots>d_n$, with $D\le(p-1)/2$. Start at $x_0=0$ and walk by $+D,-d_2,+d_3,\ldots$ to get $x_1,\ldots,x_n$. Each new endpoint after $x_1$ lies strictly inside the preceding edge. Thus $x_1,\ldots,x_n$ are distinct and lie in $[1,D]$.

Close the walk by appending $x_n-D,x_{n-1}-D,\ldots,x_1-D=0$. These vertices are distinct and lie in $[1-D,0]$. The whole interval $[1-D,D]$ has fewer than $p$ integers, so the cycle stays simple modulo $p$. Its steps use each magnitude once in each direction. The empty set needs no steps. [Alspach, Gavlas, Šajna and Verrall, proof of Lemma 3.4](https://core.ac.uk/download/pdf/81154598.pdf#page=6)

### Split one edge to insert the triple

Scale one unpaired element to $1$. The least positive representatives of the other two sum to $p-1$, so the triple is $1,r,-(r+1)$, where $r$ is the smaller representative and $2\le r<(p-1)/2$. Put $L=r+1$. Temporarily replace the triple by the pair $\{L,-L\}$ and make the cycle above. It has no pair of magnitude $r$.

On the alternating part of the walk, take the edge $u\to v$ of length $L$. **The point one unit from $u$ toward $v$ is free.** Earlier vertices lie outside the open edge by nesting. Later vertices on the alternating walk stay within $L-2$ of $v$, since the next magnitude, if any, is smaller than $L$ and cannot be $r=L-1$. The proposed point is $L-1$ from $v$. The return part lies at or below zero, and the point is strictly positive.

Insert that point and traverse the cycle in the direction that makes the split edge positive. Its steps are now $1,r$ in some order, and the other copy still gives $-L$. Undoing the scaling gives the required ordering. This also proves the construction for any number of opposite pairs together with three unpaired elements of sum zero.

For example, modulo 11 the cycle $0,5,1,4,-1,-4,0$ uses the pairs $\pm3,\pm4,\pm5$. Inserting $2$ between $1$ and $4$ splits the step $3$ into $1,2$. The seven nonempty partial sums are $5,1,2,4,-1,-4,0$.

The Python constructor uses the unified ordering rule and checks each resulting ordering. [Witness constructor](paired_triple.py)

~~~sh
python3 paired_triple.py --example 11 1 2 4 5 6 7 8
python3 paired_triple.py --through 257
~~~
