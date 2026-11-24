"""Verify the two full-pole branches through (1,0,1) for D=2 modulo 7.

Run with: uv run --with python-flint==0.9.0 seed_one_endpoint.py
"""
from flint import nmod_mat, nmod_poly

from cubic_elimination_symmetry import coordinates
from search_pell_mod import cubic_candidates


def main():
    p, D = 7, 2
    t = nmod_poly([0, 1], p)
    L, U, V = 1-D*t**2, 1+D*t**2, 2*t
    cubics = [U**j*L**(3-j) for j in range(4)]
    quadratics = [V*U**j*L**(2-j) for j in range(3)]
    models = []
    for X, Y, Z in cubic_candidates(p, D, (1, 0, 1)):
        cols = [f*t**i for f in (3*X**2, 2*Y*Z, Y**2+2*Z*L**3) for i in range(1, 7)]
        jacobian = nmod_mat([[int(col[i]) for col in cols] for i in range(1, 19)], p)
        assert int(jacobian.det()) == 6
        assert X(-t) == X and Y(-t) == -Y and Z(-t) == Z
        c, e, h = coordinates(X, cubics), coordinates(Y, quadratics), coordinates(Z, cubics)
        assert c == [4, 0, 0, 4] and h == [1, 0, 1, 6]
        den = (-D)**3
        endpoint_x, endpoint_y, endpoint_z = (
            int(F[6]) * pow(den, -1, p) % p for F in (X, Y, Z)
        )
        assert (endpoint_x, endpoint_y, endpoint_z) == (0, 0, 3)
        models.append(e)
        print(f"x(u)={c}, y/v={e}, z(u)={h}, determinant=6, endpoint=(0,0,3)")
    assert sorted(models) == [[0, 2, 4], [0, 5, 3]]


if __name__ == "__main__":
    main()
