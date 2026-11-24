"""Absolute elimination of the invariant-quadratic sextic-square condition.

Run with uv run --with python-flint==0.9.0 python quintic_invariant_elimination.py.
All discriminants and squarefree factorizations are over the integers.
"""
from flint import fmpz_mpoly_ctx, fmpz_poly


def check(seed):
    ctx = fmpz_mpoly_ctx.get(("t", "b", "c"), "lex")
    t, b, c = ctx.gens()
    a = 2-seed**3
    h = 2-t**3
    q = -seed+b*(t-seed)+c*(t-seed)**2
    f = a**3-a*h-3*a**2*t**2*q-3*a*t*q**2*h-q**3*h**2
    # f = a² y² after the substitution. Its leading t coefficient is -c³.
    assert {(j,k):v for (i,j,k),v in f.to_dict().items() if i==12} == {(0,3):-1}
    disc = f.discriminant("t")
    primitive, rem = divmod(disc,c**18)
    assert not rem
    d = primitive.primitive()[1]
    assert d.degrees()==(0,30,27)
    if seed == 0:
        # For c nonzero, replacing c by C=c³ preserves root multiplicities.
        assert all(k%3==0 for i,j,k in d.to_dict())
        d = ctx.from_dict({(i,j,k//3):v for (i,j,k),v in d.to_dict().items()})
    n = d.degrees()[2]
    leading = {(i,j):v for (i,j,k),v in d.to_dict().items() if k==n}
    assert set(leading)=={(0,0)}  # No degree drop can occur at any b.
    proj = d.discriminant("c")
    coeffs = proj.to_dict()
    assert all(i==0 and k==0 for i,j,k in coeffs)
    p = fmpz_poly([coeffs.get((0,j,0),0) for j in range(proj.degrees()[1]+1)])
    mults = []
    scalar, blocks = p.factor_squarefree()
    product = fmpz_poly([scalar])
    for g, m in blocks:
        if m>=4:
            assert g==fmpz_poly([0,1])
        product *= g**m
        mults.append((g.degree(),m))
    assert product==p
    # At b=0 the only possible multiplicity >=5 of the first discriminant
    # is at c=0, which would lose the quintic term.
    bzero = fmpz_poly([d.to_dict().get((0,0,k),0) for k in range(n+1)])
    rem = bzero
    while rem[0]==0:
        rem //= fmpz_poly([0,1])
    assert rem.degree()>0 and rem.gcd(rem.derivative()).degree()==0
    print(f"r(seed)={seed}: second discriminant degree {p.degree()}, "
          f"squarefree block (degree,multiplicity) {sorted(mults)}",flush=True)


if __name__ == "__main__":
    for r0 in (0,1,-1,2,-2):
        check(r0)
