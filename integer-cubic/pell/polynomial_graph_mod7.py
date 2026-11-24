"""List all f in F7[y] of degree at most eight for which y^4+8-4f^3
has squarefree part of degree at most two, up to the indicated symmetries.
Run with uv run --with python-flint==0.9.0 polynomial_graph_mod7.py.
"""

from itertools import product
from flint import nmod_poly


P = 7
Y = nmod_poly([0, 1], P)
H = Y**4+8
EXPECTED = {
    (5, 1), (6, 3),
    (1, 2, 1), (2, 0, 1), (4, 1, 1), (1, 0, 3),
}


def check_graph(f):
    delta = H - 4*f**3
    # A factor E with E² | delta divides both delta and delta'.
    if 2*delta.gcd(delta.derivative()).degree() + 2 < delta.degree():
        return None
    _, factors = delta.factor_squarefree()
    odd_part = nmod_poly([1], P)
    for factor, multiplicity in factors:
        if multiplicity % 2:
            odd_part *= factor
    return odd_part if odd_part.degree() <= 2 else None


def main():
    assert all((c**3-2) % P for c in range(P))
    assert all((c**4+8) % P for c in range(P))
    assert check_graph(nmod_poly([], P)) is None
    cube_roots = [c for c in range(1, P) if c**3 % P == 1]
    leads = {min(c*z % P for z in cube_roots) for c in range(1, P)}
    assert leads == {1, 3}
    found = set()
    for degree in range(9):
        tested = 0
        for a in sorted(leads):
            for lower in product(range(P), repeat=degree):
                # For even degree, y ↦ −y preserves the normalized leading term.
                if degree % 2 == 0 and next((v for v in lower[1::2] if v), 0) > 3:
                    continue
                coeffs = (*lower, a)
                tested += 1
                odd = check_graph(nmod_poly(list(coeffs), P))
                if odd is not None:
                    assert odd.degree() == 2
                    assert odd.gcd(odd.derivative()).degree() == 0
                    found.add(coeffs)
        print(f"Degree {degree}: {tested} normalized polynomials tested", flush=True)
    assert found == EXPECTED
    print("All six surviving representatives have degree one or two and two distinct branch roots.")


if __name__ == "__main__":
    main()
