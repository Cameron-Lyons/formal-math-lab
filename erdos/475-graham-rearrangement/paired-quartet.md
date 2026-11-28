# Graham orderings with at most four omitted residues

Unlike the finite prime-by-prime searches for $p = 41, 43, 47$, the result below holds for **every prime $p$** by a single, completely explicit rule. When a subset of $\mathbb{F}_p^\times$ misses at most four residues, almost all of its elements come in opposite pairs $\{d, -d\}$, with at most four unpaired stragglers left over. By arranging the pairs in decreasing order of magnitude and walking in two alternating "pendulum" swings — one staying in the positive half $[1, h]$ and the other in the nonpositive half $[-h, 0]$ — we guarantee that no partial sum can ever repeat.

**Theorem.** At every prime $p$, each set $A \subseteq \mathbb{F}_p^\times$ omitting at most four residues has an ordering with distinct nonempty partial sums.

More generally, the exact same proof constructs a valid ordering for **any** collection of opposite pairs together with three or four unpaired residues of sum zero.

## Step 1: Reduce to a zero-sum set

At $p = 2$, $\mathbb{F}_2^\times = \{1\}$ and both subsets ($\emptyset$ and $\{1\}$) work immediately. So let $p = 2h + 1$ be an odd prime, and represent $\mathbb{F}_p$ by the balanced integer interval $[-h, h] = \{-h, \ldots, 0, \ldots, h\}$.

Suppose first that $A$ has a **nonzero** total $s \pmod p$. We reduce to the zero-sum case without increasing the number of omitted residues:

* Put $X = A \cup \{0\}$. Because the full set $\mathbb{F}_p^\times$ sums to $0 \ne s$, $X$ is a proper subset of $\mathbb{F}_p$.
* Repeatedly subtracting $s$ cycles through all of $\mathbb{F}_p$, so some $a \in X$ satisfies $b = a - s \notin X$.
* The set $B = (A \setminus \{a\}) \cup \{b\}$ sums to $0 \pmod p$ and has size $|A|$ (if $a \in A$) or $|A| + 1$ (if $a = 0$), so it omits at most as many residues as $A$.
* Take a valid zero-sum ordering of $B$ (a simple cycle through $0$), rotate it to begin with $b$, and replace that first step $b$ by $a$. Every nonempty partial sum shifts by the same constant $s$, preserving distinctness. If $a = 0$, discard the leading zero step to obtain a valid ordering of $A$.

From here on, assume $\sum A \equiv 0 \pmod p$. (If $A = \emptyset$, the empty ordering needs no steps.)

## Step 2: Group the steps into ordered pairs

Pair each element of $A$ with its negative whenever both belong to $A$. Every remaining **unpaired** element $u \in A$ means $-u$ is omitted from $A$, so distinct unpaired elements account for distinct omissions; hence there are at most four unpaired elements. Since the paired elements cancel out, the unpaired elements themselves sum to $0 \pmod p$. A single nonzero residue cannot sum to $0$, and two nonzero residues summing to $0$ would form an opposite pair, so there are either **0, 3, or 4** unpaired elements.

Now turn the unpaired elements (if any) into two "nearly opposite" pairs:

1. **Pad a triple with a temporary zero.** If three unpaired elements remain, adjoin a temporary $0$ so there are four elements in all.
2. **Split into two pairs and rescale their sums to $\pm 1$.** Partition these four elements into two pairs. Neither pair sums to $0 \pmod p$ (the nonzero elements had no opposite partners, and $0$ is paired with a nonzero element), so their two sums are opposite nonzero residues. Scale the entire set $A$ by the inverse of one of those sums so the two pair sums become **$1$ and $-1$** modulo $p$. (Scaling preserves opposite pairs and distinctness of partial sums.)
3. **Pass from $\mathbb{F}_p$ to exact integers.** Write every element as its balanced representative in $[-h, h]$. Any two distinct integers in $[-h, h]$ have integer sum between $(-h) + (-h + 1) = 2 - p$ and $h + (h - 1) = p - 2$. Within $[2 - p, p - 2]$, the only integer congruent to $1 \pmod p$ is $1$, and the only one congruent to $-1 \pmod p$ is $-1$. Hence the two pair sums equal $1$ and $-1$ **as exact integers**!
4. **Disjoint magnitudes and strict ordering.** Two distinct integers summing to $+1$ or $-1$ must have opposite signs and **consecutive magnitudes** (counting $0$ as the missing sign for $(+1, 0)$ or $(0, -1)$). Meanwhile, each ordinary opposite pair $(+d, -d)$ uses a single magnitude $d$. Because all elements are distinct and no unpaired element has an opposite partner in $A$, **no two pairs share a magnitude**. Their magnitude intervals (singletons $\{d\}$ or consecutive pairs $\{k - 1, k\}$) are therefore completely disjoint.

List all pairs from **largest magnitude to smallest**. Any pair containing the temporary $0$ necessarily comes last, and because the ordinary pairs sum to $0$ while the two special pairs sum to $+1$ and $-1$, **all steps together sum to $0$ as exact integers**.

## Step 3: Read off the pendulum ordering

Every pair has one element in the positive slot and one in the negative slot (with the temporary $0$ occupying the missing sign slot in the last pair). Read off the ordering in three parts, skipping the temporary $0$ wherever it appears:

1. **Outbound pendulum (largest pair to smallest):** take one step from each pair, alternating signs starting with positive ($+, -, +, -, \ldots$).
2. **The bridge:** take the unused (negative) step of the **largest** pair.
3. **Return pendulum (smallest pair up to second-largest):** take the remaining unused steps in reverse pair order, from the smallest pair back up to the second-largest pair.

**Why every nonempty partial sum is distinct:**

* **Before the bridge (positive half $[1, h]$).** The outbound steps alternate signs starting from positive, with strictly decreasing magnitudes (since the pairs have disjoint, strictly decreasing magnitude intervals). Geometrically, the first step lands in $[1, h]$, and every subsequent step swings back strictly inside the preceding edge. Thus all outbound partial sums are pairwise distinct and lie in $[1, h]$.
* **From the bridge onward (nonpositive half $[-h, 0]$).** Because the entire ordering sums to $0$ as exact integers, it finishes at $0$. Now trace the partial sums **backwards** from the final $0$ back to the end of the bridge. Walking backwards from $0$ subtracts the return steps in reverse order (from the second-largest pair down to the smallest pair). Since the outbound walk chose the *negative* element of the second-largest pair, its unused step is *positive* — so subtracting it starts the backward walk with a **negative** step! Thereafter, the negated unused steps alternate signs with strictly decreasing magnitudes. Just as before, every backward step swings strictly inside the preceding edge, so all partial sums from the end of the bridge through the final $0$ are pairwise distinct and lie in $[-h, 0]$.
* **Skipping the temporary zero.** When present, the temporary $0$ lies in the *smallest* pair, which is the **very last** entry of whichever pendulum (outbound, or backward-read return) uses that slot. Dropping a trailing $0$ does not disturb the sign alternation or strictly decreasing magnitudes of the remaining steps.
* **No overlap modulo $p$.** The two intervals $[1, h]$ and $[-h, 0]$ partition the $2h + 1 = p$ residues modulo $p$, so they are completely disjoint modulo $p$. Undoing the initial scaling preserves distinctness and completes the proof. $\square$

## Worked example (modulo 13)

Take $p = 13$ ($h = 6$) and the zero-sum set with four pairs listed from largest magnitude to smallest:
$$(+6, -5), \quad (+4, -4), \quad (+2, -3), \quad (+1, -1).$$
Notice that $(+6, -5)$ sums to $+1$, $(+2, -3)$ sums to $-1$, and the other two are ordinary opposite pairs; their magnitudes $\{6, 5\}, \{4\}, \{3, 2\}, \{1\}$ are strictly decreasing and disjoint.

1. **Outbound pendulum** ($+, -, +, -$ from largest to smallest): $6, -4, 2, -1$.
   * Running sums: $6,\; 2,\; 4,\; 3$ — all distinct in $[1, 6]$.
2. **Bridge** (unused step of largest pair): $-5$.
   * Running sum: $3 - 5 = -2$.
3. **Return pendulum** (unused steps from smallest pair up to second-largest): $1, -3, 4$.
   * Running sums: $-1,\; -4,\; 0$ — together with $-2$, all distinct in $[-6, 0]$.
   * Reading backwards from $0$ to $-2$ uses the negated return steps $-4, +3, -1$: alternating from negative with strictly decreasing magnitudes!

The complete ordering is $6, -4, 2, -1,\; -5,\; 1, -3, 4$, with distinct nonempty partial sums $6, 2, 4, 3,\; -2, -1, -4, 0$ (modulo $13$: $6, 2, 4, 3, 11, 12, 9, 0$).

## Executable constructor and tests

The Python script [paired_triple.py](paired_triple.py) implements this constructive algorithm and independently verifies every ordering it returns:

~~~sh
python3 paired_triple.py --through 257
~~~
