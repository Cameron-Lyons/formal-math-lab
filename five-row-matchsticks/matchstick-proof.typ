#set document(title: "Breaking every rectangle in a five-row matchstick grid")
#set page(paper: "us-letter", margin: (x: 0.85in, y: 0.66in), numbering: "1")
#set text(font: "Libertinus Serif", size: 11pt)
#set par(leading: 0.57em, justify: false)
#set heading(numbering: none)
#let ink = rgb("#173d4c")
#let pale = rgb("#edf4f5")
#show heading: it => text(fill: ink, it)
#let pairs(s) = text(font: "Liberation Mono", size: 9.2pt, s)

#align(center)[#text(size: 21pt, weight: "bold", fill: ink)[Breaking every rectangle in a five-row grid]]

#block(width: 100%, fill: pale, inset: 10pt, radius: 3pt)[
  *Theorem.* Form a grid of $5 times n$ unit squares from matchsticks. Let $S(n)$
  be the fewest sticks that must be removed to break the outline of every
  axis-aligned rectangle, including every square. Then
  $ S(1) = 5, quad S(n) = floor((10n+4)/3) quad "for all" n >= 2. $
]

= Lower bound

Let $N=5n$. Make a graph with one vertex for each cell and one extra vertex
for the exterior. For each erased stick, join the two regions it separated.
Call the components disjoint from the exterior *interior components*.
Every edge along the boundary of such a component is intact, since an erased
edge would join it to its neighbor. Hence an interior component cannot itself
be a rectangle. In particular, it contains at least three cells.

At least one cell belongs to the exterior component, since some stick on the
outer perimeter must be erased. If there are $t$ interior components, then
$3t <= N-1$. The graph starts with $N+1$ isolated vertices and ends with $t+1$
components. Each erased stick reduces the component count by at most one.
Thus the number $e$ of erasures satisfies
$ e >= N-t >= N-floor((N-1)/3) = ceil((2N+1)/3). $
For $n >= 2$ congruent to 0 or 1 modulo 3, this gives the claimed lower bound.
At width one every connected set of cells is an interval, itself a rectangle.
All five cells must therefore join the exterior, which requires five erasures.

== The remaining widths

Suppose $n=3k+2$, so $N=3q+1$ with $q=5k+3$. If $2q+1$ erasures sufficed,
the inequalities above would force $t=q$. Exactly one cell would belong to
the exterior and each interior component would have three cells. Each such
component must be an L, since the only other connected three-cell shape is a
straight rectangle.

Choose a five-cell end column that omits the exterior cell. An L meeting
this column covers at most two of its cells and lies entirely within the
first two columns from that end. At least three Ls are needed to cover the
end column, and four Ls would need twelve cells in a ten-cell region. Thus
exactly three meet it. They cover consecutive runs of lengths 2, 2, and 1
in some order.

#let tile(x) = table.cell(fill: if x == "A" {rgb("#d8e9ec")} else {rgb("#f5e8c7")})[#text(weight: "bold")[#x]]
#grid(columns: (auto, 1fr), column-gutter: 14pt, align: (center+horizon, left+horizon),
  table(columns: (20pt,20pt), rows: (16pt,16pt,16pt), align: center+horizon,
    inset: 1pt, stroke: 0.5pt + ink,
    tile("A"), tile("A"), tile("B"), tile("A"), tile("B"), tile("B")),
  [Let A cover the singleton. It extends into the next column and turns
   toward an adjacent row. On the end column that row belongs to a two-cell
   run, B. The square directly across from that row is already in A, so B
   must turn at its other row. The picture shows the forced arrangement,
   up to reflection.])

Together A and B form a $3 times 2$ rectangle. Every edge on its perimeter
joins different components and is intact. This is a contradiction. Hence
$e >= 2q+2=10k+8$, as required.

#pagebreak()

= Upper bound

We construct one infinite strip whose first $n$ columns attain the bound
for every $n$. Number the horizontal grid lines from 0 at the top to 5 at the
bottom. In each new column, erase the horizontal sticks at levels $H$. On
its right boundary erase the vertical sticks indexed by $V$, where index $i$
means the stick from level $i$ to $i+1$. Keep all sticks on the initial left
boundary.

Use the two starting columns below and then the three-column block A, B, C.
Follow it with its top-to-bottom reflection, then alternate the block and its
reflection forever. Under reflection a horizontal index $i$ becomes $5-i$,
and a vertical index $i$ becomes $4-i$. Stop at any desired width.

#align(center)[#table(
  columns: (auto, auto, auto, auto, auto),
  inset: (x: 7pt, y: 4pt),
  stroke: none,
  align: (left,center,center,center,left),
  table.header([*Column*],[*$H$*],[*$V$*],[*Erasures*],[*Pairs arriving at the right*]),
  table.hline(stroke: 0.6pt + ink),
  [Start 1], [1, 3, 4], [0, 2], [5], pairs("02  05  25"),
  [Start 2], [4], [1, 4], [3], pairs("02  05  12  25  35"),
  table.hline(stroke: 0.3pt + ink),
  [A], [2], [0, 3], [3], pairs("01  05  34  35"),
  [B], [1, 3], [4], [3], pairs("05  45"),
  [C], [1, 4], [0, 2], [4], pairs("02  03  05  23"),
  table.hline(stroke: 0.6pt + ink),
)]

== Why no rectangle closes

At a vertical boundary, call a level pair $a<b$ *open* if an intact vertical
segment at some earlier or current boundary joins $a$ and $b$, and both
horizontal runs from that segment to the current boundary are intact.
Write $P$ for the set of open pairs and abbreviate $(a,b)$ by
#pairs("ab"). Initially all fifteen pairs are open.

When the next column is added, a pair in $P$ arrives at its right side exactly
when both its levels avoid $H$. These surviving pairs form the last column
of the table. A rectangle closes precisely when one of them also has an
intact right side, that is, when none of the indices $a, dots, b-1$ lies in
$V$. In every row of the table each arriving pair contains a cut on this
vertical interval. For example, in row B, both #pairs("05") and #pairs("45")
cross vertical cut 4.

To get the next open set, take the arriving pairs and add all pairs joined
on the new vertical boundary. Write $P_2$ and $P_5$ for the sets after
Start 2 and after C, respectively.

#align(center)[#table(columns: (auto, auto), stroke: none, align: left, inset: (x: 7pt, y: 2pt),
  [$P_2$], pairs("01  02  05  12  23  24  25  34  35"),
  [$P_5$], pairs("02  03  05  12  23  34  35  45"),
)]

Let $R$ reflect pairs, taking $(a,b)$ to $(5-b,5-a)$. The displayed sets give
$P_5 subset.eq R(P_2)$ with just one extra pair, #pairs("13"), in $R(P_2)$.
Starting with fewer open pairs can only reduce the set at every later step.
Thus the block is safe from any subset of $P_2$ and ends in a subset of
$R(P_2)$. By reflection the next block is safe and ends in a subset of $P_2$.
Induction proves every prefix is rectangle-free.

The first column costs five erasures. For $n=2+3k+r$ with $r in {0,1,2}$,
the two starting columns cost eight, each whole block costs ten, and the
first $r$ columns of the next block cost $3r$. The total is
$8+10k+3r=floor((10n+4)/3)$. This attains the lower bound. #h(1fr) $square.filled$

#v(1fr)
#text(size: 9pt)[*Related work.* E. Niu and Z. Tang, “On the rectangle eliminating number of grid graphs,”
_Theoretical Computer Science_ 1085 (2026), 116199. #link("https://doi.org/10.1016/j.tcs.2026.116199")[doi:10.1016/j.tcs.2026.116199].]
