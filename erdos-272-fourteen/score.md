# Counting short progressions in an arbitrary set of integers

Let $S$ be a finite nonempty set of integers, let $m=|S|$, and write $a_j$ for the
number of increasing $j$-term arithmetic progressions contained in $S$.
If $S$ contains no seven-term progression, then

$$
q(S)=\binom{m-1}{2}-a_3-a_4-a_6\ge 0,
$$

with equality exactly when $S$ is an arithmetic progression. This includes
singletons and pairs. In particular the assertion holds for sets of arbitrarily
large diameter. For all $S$, the argument proves the stronger inequality

$$
Q(S)=\binom{m-1}{2}-a_3-a_4-a_6+a_7
\ \ge\ \left\lfloor\frac{(m-1)^2}{4}\right\rfloor-a_3\ \ge 0.
$$

## A count of maximal runs

For each positive integer $d$, break $S$ into maximal runs of consecutive terms
with step $d$, working separately in every residue class modulo $d$. Write $H_d$
for the number of these runs of length at least three and $L_d$ for the number
of length at least six. Summing over $d$ gives

$$
\sum_d H_d=a_3-a_4,\qquad \sum_d L_d=a_6-a_7.
$$

Indeed a run of length $\ell$ contains $\max(0,\ell-j+1)$ consecutive
$j$-term progressions of that step. Let $R=\sum_d(H_d-L_d)$, the number
of runs of lengths three through five. Let $D=\{d:H_d>0\}$, the set of
differences of all triples in arithmetic progression. We claim that $R\ge|D|$.

Fix $d$ and a residue class modulo $d$. Its points occupy two residue classes
modulo $2d$. For every maximal $2d$-run of length at least three in these
two classes, take the closed interval between its endpoints. Intervals from
the same class modulo $2d$ are disjoint. Join two intervals if they intersect.
The graph is a forest. In a cycle, choose an interval with the smallest right
endpoint. Both its neighbours then contain that endpoint, but they belong
to the same residue class modulo $2d$.

A maximal $d$-run of length at least six has three or more points in each of
its alternating classes. The two maximal $2d$-runs containing these points
give intersecting intervals, hence an edge. This assignment is injective.
Every point of the original residue class in the intersection of the intervals
belongs to one of the two $2d$-runs. These points form a consecutive $d$-run
that meets the interior of the original run. Thus an edge determines a unique
maximal $d$-run. Taking the disjoint union of the forests over residues modulo
$d$ gives $L_d$ distinct edges among $H_{2d}$ vertices. Consequently

$$
H_{2d}-L_d\ge \mathbf{1}_{H_{2d}>0}.
$$

Summing this bound and adding $H_e\ge\mathbf{1}_{H_e>0}$ for odd $e$ gives
$R\ge |D|$.

## The score and its equality case

Write $s_0<\cdots<s_{m-1}$ for the elements of $S$. Each $s_i$ is the centre
of at most $\min(i,m-1-i)$ triples. Write $\delta_i$ for the deficit in this
bound. Its sum is

$$
\Delta=\sum_i\delta_i=\left\lfloor\frac{(m-1)^2}{4}\right\rfloor-a_3.
$$

Put $h=\lfloor(m-1)/2\rfloor$ and take the lower median $x=s_h$. The
$h-\delta_h$ triples centred there have distinct differences, so
$R\ge|D|\ge h-\delta_h$. Since
$\binom{m-1}{2}=2\lfloor(m-1)^2/4\rfloor-h$, it follows that

$$
Q(S)=\binom{m-1}{2}-2a_3+R=2\Delta+R-h
      \ge 2\Delta-\delta_h\ge\Delta.
$$

Suppose $Q(S)=0$ and $m\ge 3$. Every centre attains its bound, and
$R=|D|=h$. Let $T=\{x-s_i:i<h\}$. At $x$ each of these $h$ left
distances occurs in a triple, so $T=D$. If $a<b\le x$ belong to $S$, the
centre $b$ attains its bound on the left, so $2b-a\in S$ and $b-a\in D$.
It follows that $T$ is closed under positive differences. If $d=\min T$,
repeated subtraction of $d$ shows that $T=\{d,2d,\ldots,hd\}$.

The right side of $x$ contains $x+T$. When $m$ is odd these are all its
points, so $S$ is an arithmetic progression. When $m$ is even there is just
one additional point $x+r$ with $r>0$. For any $x<a<b$ in $S$, the centre
$a$ attains its bound on the right, whence $b-a\in D=T$. Applying this to
$x+d$ and $x+r$ gives $|r-d|\in T$. Therefore $r$ is a positive multiple of
$d$ no larger than $(h+1)d$. It is outside $T$, so $r=(h+1)d$. Again $S$
is an arithmetic progression.

For $a_7=0$ we have $q=Q$. Every arithmetic progression in this case has
length at most six. For lengths $1,2,3,4,5,6$, respectively, the values of
$a_3+a_4+a_6$ are $0,0,1,3,6,10$, which equal $\binom{m-1}{2}$.
This proves both directions of the claimed equality criterion.
