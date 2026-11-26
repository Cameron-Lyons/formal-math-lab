#set page(paper: "a4", margin: (x: 21mm, y: 19mm))
#set text(size: 11pt)
#set par(leading: 0.62em)
#show heading.where(level: 2): set text(size: 13pt)
#align(center)[#text(size: 18pt, weight: "bold")[Why 83 sets are impossible]]
#v(3pt)

*Claim.* The largest family of subsets of $[13]$ whose pairwise intersections are nonempty arithmetic progressions has size *82*.

Szabó's construction gives 82. Yang proved the upper bound of 82 for families with a common element. It suffices to rule out 83 with no common element. Write AP for arithmetic progression.

== 1. Set aside 315 subsets

Set aside every subset containing a seven-term AP, and also every five-term AP. There are 300 of the first kind and 15 of the second. We show that *at most 79 of the remaining subsets can belong to one valid family*.

For a set $A$, let $u_A$ record which of the empty set and the 78 pairs are contained in $A$. Let $v_A$ record which singletons and which three-, four- and six-term APs are contained in $A$. Each entry is 0 or 1. If $a_j(S)$ counts the $j$-term APs in $S$, put
$ q(S) = 1 + binom(|S|,2) - |S| - a_3(S)-a_4(S)-a_6(S). $
For every nonempty $S$ containing no seven-term AP, a direct count gives $q(S)=0$ for APs and $q(S)>0$ for all other sets. The verifier checks all 7,891 such $S$. Counting common coordinates gives
$ u_A dot u_B - v_A dot v_B = q(A inter B). $

Now take the remaining members of a valid family. For distinct $A,B$, the right side is zero because $A inter B$ is a nonempty AP of at most six terms. If $sum_A c_A u_A=0$, squaring and using the last identity gives
$ 0 = norm(sum_A c_A v_A)^2 + sum_A c_A^2 q(A). $
Every term is nonnegative. Hence $c_A=0$ for all non-APs, and $sum_A c_A v_A=0$ as well. Each AP still under consideration has length 1, 2, 3, 4 or 6, so *it is itself a coordinate* in $u$ or $v$. Choose an inclusion-maximal AP $A$ with $c_A!=0$. In its own coordinate only $A$ can contribute a nonzero coefficient, a contradiction. Thus the vectors $u_A$ are independent. They have only $1+binom(13,2)=79$ coordinates.

== 2. Check the families using four of the 315 subsets

By the bound just proved, an 83-set family needs at least $83-79=4$ of the subsets set aside. Join two subsets by an edge when their intersection is a nonempty AP. A valid family is a clique in this graph. Order the 315 subsets and try every compatible choice for the *first two* that belong to the clique. There are 9,862 choices. For each, search its common neighbors for 81 more members, requiring at least two further sets from the 315 and no common element overall.

The search is exhaustive. It discards a branch whenever the remaining vertices can be covered by fewer independent classes than the number of vertices still needed, since a clique takes at most one vertex per class. The cases were checked in batches, using the reflection $i arrow.r 14-i$ to identify equivalent cases. No such family was found. Thus 83 is impossible, and 82 is attained.

#text(size: 9.5pt)[*Reproduce both finite checks* with `clique_search/verify.cpp`. Compile with `g++ -O3 -std=c++20 -march=native clique_search/verify.cpp -o verify`, then run `./verify --simple`. The starred theorem and Szabó's construction appear in #link("https://arxiv.org/abs/2607.23004")[Yang, arXiv:2607.23004].]
