"""Compute 7-adic obstruction jets for the seven normalized positive-slope charts.

Run with uv run --with python-flint==0.9.0 cubic_chart_obstructions.py.
Pass --forms to print all ordinary and weighted initial polynomials.
See cubic_chart_obstructions.md for the coordinate and degree conventions.
"""

import argparse
from collections import defaultdict
from dataclasses import dataclass
from functools import lru_cache
from itertools import product

from flint import fmpz_poly, nmod_mat, nmod_mpoly_ctx
from search_pell_mod import cubic_candidates
from seeded_denominator_lifts import (
    PRIME,
    SEEDS,
    CorrectionSystem,
    T,
    add_digits,
    correction_rhs,
    residual,
)

P = PRIME
DENOMINATOR_UNITS = (3, 5, 6)


@dataclass
class Chart:
    seed: tuple[int, int, int]
    origin: tuple[int, ...]
    gauge: tuple[int, ...]
    gauge_value: int
    dependent: list[int]
    free: list[int]
    jacobian_inverse: list[list[int]]


def echelon_pivots(rows):
    reduced, rank = nmod_mat(rows, P).rref()
    return [
        next(j for j, value in enumerate(row) if value)
        for row in reduced.tolist()[:rank]
    ]


def normalized_charts():
    charts = []
    orbit_counts = []
    for seed in SEEDS:
        total = normalized = 0
        for triple in cubic_candidates(P, 0, seed):
            if max(f.degree() for f in triple) < 1:
                continue
            total += 1
            x, y, _z = triple
            gauge = [0] * 19
            if seed == SEEDS[0]:
                scale = int(x[4]) * pow(int(y[3]), -1, P) % P
                gauge[3], gauge[8] = 1, -1
                gauge_value = 0
            else:
                j = 0 if x[1] else 1
                scale = int(triple[j][1])
                assert scale
                gauge[6 * j] = 1
                gauge_value = 1
            if scale != 1:
                continue
            normalized += 1
            base = tuple(
                fmpz_poly([constant, *map(int, f.coeffs()[1:])])
                for constant, f in zip(seed, triple, strict=False)
            )
            system = CorrectionSystem(base)
            rhs = correction_rhs(residual(base, 1), P)
            test_lift = add_digits(base, system.particular(rhs), P)
            if not system.solvable(correction_rhs(residual(test_lift, 1), P**2)):
                # A failed particular lift alone would not exclude a residue.
                for digits in system.solutions(rhs):
                    lifted = add_digits(base, digits, P)
                    for c in range(P):
                        error = residual(lifted, 1 - P**2 * c * T**2)
                        assert not system.solvable(correction_rhs(error, P**2))
                continue

            denominator_derivative = (18 - 3 * base[2] ** 2) * T**2
            jacobian = [
                [*row, int(denominator_derivative[i])]
                for i, row in enumerate(system.rows, 1)
            ] + [gauge]
            dep = echelon_pivots(jacobian)
            rows = echelon_pivots(list(zip(*jacobian, strict=False)))
            assert rows == [*list(range(15)), 18] and len(dep) == 16
            inverse = nmod_mat([[jacobian[i][j] for j in dep] for i in rows], P).inv()
            free = [j for j in range(19) if j not in dep]
            assert len(free) == 3 and free[2] == 18
            origin = (*tuple(int(f[j]) for f in base for j in range(1, 7)), 0)
            charts.append(
                Chart(
                    seed,
                    origin,
                    tuple(gauge),
                    gauge_value,
                    dep,
                    free,
                    [list(map(int, row)) for row in inverse.tolist()],
                )
            )
        orbit_counts.append((total, normalized))
    assert orbit_counts == [(6, 1), (42, 7)] and len(charts) == 7
    return sorted(charts, key=lambda chart: (-chart.seed[0], chart.origin))


def obstruction_jet(chart, precision, denominator_weight):
    """Return all three obstruction polynomials mod 7^precision after U=7u,V=7v."""
    ring = nmod_mpoly_ctx.get(("t", "u", "v", "c"), modulus=P**precision)
    t, u, v, c = ring.gens()
    ts = [t**j for j in range(1, 7)]

    def equations(values):
        x, y, z = [
            chart.seed[j]
            + sum(a * b for a, b in zip(values[6 * j : 6 * j + 6], ts, strict=False))
            for j in range(3)
        ]
        q = 1 - values[18] * t**2
        polynomial = x**3 + z * y**2 + z**2 * q**3 - 2 * q**9
        by_degree = [{} for _ in range(18)]
        for (i, j, k, ell), a in polynomial.to_dict().items():
            assert 1 <= i <= 18
            by_degree[i - 1][0, j, k, ell] = a
        coefficients = [ring.from_dict(entries) for entries in by_degree]
        gauge = (
            sum(a * b for a, b in zip(values, chart.gauge, strict=False))
            - chart.gauge_value
        )
        return coefficients, gauge

    values = [ring.constant(a) for a in chart.origin]
    for column, change in zip(
        chart.free, (P * u, P * v, P**denominator_weight * c), strict=False
    ):
        values[column] += change
    for n in range(1, precision):
        coefficients, gauge = equations(values)
        selected = [*coefficients[:15], gauge]
        assert all(int(a) % P**n == 0 for f in selected for a in f.coeffs())
        for column, row in zip(chart.dependent, chart.jacobian_inverse, strict=False):
            values[column] -= sum(
                a * f for a, f in zip(row, selected, strict=False) if a
            )
    coefficients, gauge = equations(values)
    assert not any(coefficients[:15]) and not gauge
    return coefficients[15:]


def first_form(polynomial, precision):
    """Return order and initial form in F7[u,v,c] after setting the symbol of 7 to 1."""
    residue = nmod_mpoly_ctx.get(("u", "v", "c"), modulus=P)
    entries = [(e[1:], int(a)) for e, a in polynomial.to_dict().items()]
    for order in range(precision):
        first = {e: a // P**order % P for e, a in entries if a // P**order % P}
        if first:
            return order, residue.from_dict(first)
    return precision, residue.constant(0)


@lru_cache(maxsize=8192)
def common_digits(form_data):
    residue = nmod_mpoly_ctx.get(("u", "v", "c"), modulus=P)
    forms = [residue.from_dict(dict(data)) for data in form_data if data]
    if any(f.is_constant() for f in forms):
        return ()
    return tuple(
        digit
        for digit in product(range(P), repeat=3)
        if all(not f(*digit) for f in forms)
    )


def possible_digits(jets, precision):
    forms = [first_form(f, precision)[1] for f in jets]
    keys = tuple(
        tuple((tuple(e), int(a)) for e, a in f.to_dict().items()) for f in forms
    )
    return common_digits(keys)


def refine(jets, u_digit, v_digit):
    """Fix one digit of u and v; keep c symbolic with all its higher digits."""
    t, u, v, c = jets[0].context().gens()
    return [f.compose(t, u_digit + P * u, v_digit + P * v, c) for f in jets]


def count_boxes(jets, precision, denominator_digits, depth):
    """Count (u mod 7^j,v mod 7^j,c mod 7) passing successive initial-form tests."""
    counts = []
    boxes = [(jets, frozenset(denominator_digits))]
    for level in range(depth):
        total = 0
        children = []
        for equations, allowed in boxes:
            by_pair = defaultdict(set)
            for u, v, c in possible_digits(equations, precision):
                if c in allowed:
                    by_pair[u, v].add(c)
                    total += 1
            if level + 1 < depth:
                for (u, v), residues in by_pair.items():
                    children.append((refine(equations, u, v), residues))
        counts.append(total)
        if not total:
            break
        boxes = children
    return counts


def show_forms(jets, precision, weight, verbose):
    forms = [first_form(f, precision) for f in jets]
    for degree, form in forms:
        assert form and all(i + j + weight * k <= degree for i, j, k in form.monoms())
    print(f"  weight {weight}, orders {tuple(degree for degree, _ in forms)}")
    if verbose:
        for i, (degree, form) in enumerate(forms, 16):
            print(f"    F{i} / 7^{degree} = {form} (mod 7)")


def verify_specialization(lighter, heavier, weight_change):
    """Compare independently computed jets at their common denominator precision."""
    ring = lighter[0].context()
    t, u, v, c = ring.gens()
    modulus = int(ring.modulus())
    for low, high in zip(lighter, heavier, strict=False):
        projected = ring.from_dict(
            {e: int(a) % modulus for e, a in high.to_dict().items()}
        )
        assert low.compose(t, u, v, P**weight_change * c) == projected


def verify_table(index, jets):
    """Independently encode the ordinary initial forms displayed in the notes."""
    forms = [first_form(f, 9)[1] for f in jets]
    u, v, c = forms[0].context().gens()
    if index == 0:
        expected = [4 * c**2, 6 * c**2 * (u + 4 * v * c + c**2), 4 * c**3]
    elif index == 1:
        l = u - v
        expected = [
            c * (l - c),
            2 * (l + 3 * c) * (l + 5 * c) ** 2,
            l**3 + 6 * l**2 * c + 5 * l * c**2 + 6 * c**3,
        ]
    elif index == 2:
        l = u + 3 * v + 5
        expected = [
            4 * c * (l - c),
            l * (l + 4 * c) ** 2,
            l**3 + l**2 * c + 5 * l * c**2 + 4 * c**3,
        ]
    elif index == 3:
        l = u + v + 6
        expected = [
            6 * c * (l + c),
            2 * l**3
            + 2 * l**2 * c
            + 2 * l**2
            + 5 * l * c**2
            + 3 * l * c
            + 4 * c**3
            + 2 * c**2,
            6 * l**3 + 6 * l**2 * c + 2 * l * c**2 + 6 * c**3,
        ]
    elif index == 4:
        expected = [5 * c**2, 5 * c**3, 5 * c**3]
    elif index == 5:
        l = u + 2 * v + 3
        expected = [3 * c**2, 4 * l**3 + 4 * c**3, 6 * l**3 + 3 * c**3]
    else:
        assert index == 6
        expected = [5 * c**2, 6 * c**3, 5 * c**3]
    assert forms == expected


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--forms", action="store_true", help="print all initial polynomials"
    )
    args = parser.parse_args()
    for i, chart in enumerate(normalized_charts()):
        print(
            f"chart {i}: seed {chart.seed}, X[1:7] = {chart.origin[:6]}, "
            f"free Z indices {tuple(j - 11 for j in chart.free[:2])}",
            flush=True,
        )
        jets = obstruction_jet(chart, 9, 1)
        verify_table(i, jets)
        show_forms(jets, 9, 1, args.forms)
        previous_weight = 1
        for weight, precision, depth in (
            (2, 12, 2),
            (4, 15, 4),
            (6, 20, 6),
            (8, 22, 6),
        ):
            if weight == 8 and i in (0, 4):
                continue
            current = obstruction_jet(chart, precision, weight)
            verify_specialization(jets, current, weight - previous_weight)
            if weight == 2:
                show_forms(current, precision, weight, args.forms)
            digits = range(P) if weight == 8 else DENOMINATOR_UNITS
            label = "h>=4" if weight == 8 else f"h={weight // 2}"
            counts = count_boxes(current, precision, digits, depth)
            assert counts[-1] == 0
            print(f"  {label} modulus 7^{precision}: {counts}", flush=True)
            jets, previous_weight = current, weight


if __name__ == "__main__":
    main()
