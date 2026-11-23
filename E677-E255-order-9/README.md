# Equation 677 implies Equation 255 at order nine

Every nine-element multiplication table satisfying $x=y⋆(x⋆((y⋆x)⋆y))$ also satisfies $x=((x⋆x)⋆x)⋆x$ at every element. The complete proof is in [Nine.lean](Nine.lean).

## The argument

Suppose the second equation fails. Label a failing element 0. In the first row, scan the columns from left to right. If the output in column $i$ is larger than $i+1$, swap its label with $i+1$. Each swap fixes the names and outputs at all earlier columns. We may therefore assume $0⋆i≤i+1$.

Now represent a table by Boolean variables $T(r,c,v)$ meaning $r⋆c=v$. Each cell has exactly one value. Each value occurs once per row because Equation 677 supplies a preimage for every value, and a surjection on nine points is a permutation.

The two equations translate directly into rules about three known entries.

| If the table contains | What follows |
| --- | --- |
| $y⋆x=a$, $a⋆y=b$, $x⋆b=c$ | Equation 677 requires $y⋆c=x$. |
| $0⋆0=a$, $a⋆0=b$, $b⋆0=0$ | Equation 255 holds at 0, contradicting the choice of 0. |

Lean proves that a counterexample would satisfy these rules and the label bounds. The resulting formula has 729 variables and 65,152 clauses. Lean verifies a refutation of that formula, completing the contradiction.

## Verify

Run `lean Nine.lean` with Lean 4.36.0, or run `lake build` in this directory. Lean uses its bundled CaDiCaL solver to generate an LRAT certificate and replays it with the standard library’s verified checker. Replay uses `native_decide`, so this computation trusts Lean’s native compiler and runtime. The algebra, relabelling and translation to Boolean clauses are kernel-checked.

After a Lake build, inspect the theorem and its axioms with

```sh
printf '%s\n' 'import Nine' '#check Nine.eq677_implies_eq255' \
  '#print axioms Nine.eq677_implies_eq255' | lake env lean --stdin
```

The optional command `lake env lean --run ExportCNF.lean > nine.cnf` exports the exact search formula for use with an independent SAT checker.

José Brox reported an independent computational exclusion in December 2024. [Original report](https://leanprover-community.github.io/archive/stream/458659-Equational/topic/FINITE.3A.20677.20-.3E.20255.html#487358914)
