# R₃²(C₇) = 11 — seven-cycle Ramsey number with at most two color changes

**Prior-art status (22 November 2026):** no earlier proof of this exact
threshold was located. It is one finite case of Allen et al.'s odd-cycle
problem, not a solution to the whole family. The lower-bound construction
uses the paper's colored-K₄ template with the part sizes specified below.
See the [dated audit](../PRIOR_ART.md#seven-cycle).
The term *colour changes* refers to consecutive cycle edges, including the
last-to-first transition; a cycle that merely uses two colors need not qualify.

**The smallest number of vertices that guarantees such a cycle is 11.** Color every edge of a complete graph red, green or blue. A color change occurs when consecutive edges of the cycle have different colors, including where the last edge meets the first.

**Why 10 can fail.** Take one vertex and three groups of three. Name the groups red, green and blue. Use each group’s color inside it and on its edges to the single vertex. Between two groups, use the third color. Lean checks that every seven-cycle in this coloring changes color at least three times.

**Why 11 works.** Pick any vertex. Of its ten edges, at least four have the same color. Keep that vertex, those four neighbors and five others. Lean checks that every way to color the remaining edges on these ten vertices gives a seven-cycle with at most two changes.

Run `lake build` in this folder to check the proof. [Lean theorem](SevenCycle.lean) · [Original problem, specialized here to seven vertices](https://arxiv.org/html/2607.03243v1#Thmtheorem22)
