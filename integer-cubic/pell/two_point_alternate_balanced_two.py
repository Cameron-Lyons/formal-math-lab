"""Check the alternate two-point Pell charts with bad denominators at 2.

Run with uv run --with python-flint==0.9.0 python two_point_alternate_balanced_two.py.
"""

from ast import literal_eval
from fractions import Fraction
from itertools import product
from pathlib import Path

from two_point_primary_two import INDICES, SlopeChart, split_residues

ALTERNATE_MARKS = ((0, -2), (1, 2), (1, 0))
TARGET_PARITY = (0, 1, 1)


def pack(bits):
    return sum(value << j for j, value in enumerate(bits))


def binary_solutions(columns, rhs):
    """Column elimination tracks a particular solution and all column dependencies."""
    pivots = {}
    kernel = []
    for j, column in enumerate(columns):
        value, combination = column, 1 << j
        while value and value.bit_length() in pivots:
            earlier, representation = pivots[value.bit_length()]
            value ^= earlier
            combination ^= representation
        if value:
            pivots[value.bit_length()] = value, combination
        else:
            kernel.append(combination)
    particular = 0
    while rhs:
        if rhs.bit_length() not in pivots:
            return []
        column, representation = pivots[rhs.bit_length()]
        rhs ^= column
        particular ^= representation
    result = [particular]
    for dependency in kernel:
        result += [v ^ dependency for v in result]
    return result


def check_chart(slope, certificates):
    chart = SlopeChart(slope, ALTERNATE_MARKS)
    e = slope.denominator
    counts = [0, 0, 0]
    used = set()

    def contradictory(rows, rhs):
        augmented = {r | (v << 23) for r, v in zip(rows, rhs, strict=False)}
        found = {k for k, patterns in enumerate(certificates) if patterns <= augmented}
        used.update(found)
        return bool(found)

    for a, q in split_residues(e, TARGET_PARITY):
        fixed = [((a, q)[m][j] >> i) & 1 for j, m, i in INDICES]
        unknown = [k for k, (_, _, i) in enumerate(INDICES) if i % e]
        for bits in product(range(2), repeat=len(unknown)):
            coefficients = fixed.copy()
            for k, bit in zip(unknown, bits, strict=False):
                coefficients[k] = bit
            if any(chart.digit(chart.identity(coefficients), 0)):
                continue
            counts[0] += 1
            matrix, rhs = chart.correction_matrix(coefficients)
            rows = [pack(row) for row in matrix]
            if contradictory(rows, rhs):
                continue
            corrections = binary_solutions(
                [pack(column) for column in zip(*matrix, strict=False)], pack(rhs)
            )
            # Every inconsistent binary system must have matched a stored certificate.
            assert corrections
            counts[1] += 1
            counts[2] += len(corrections)
            for correction in corrections:
                lifted = [
                    v + 2 * ((correction >> j) & 1) for j, v in enumerate(coefficients)
                ]
                # At any lift the Jacobian has the same reduction modulo two.
                rhs_next = chart.digit(chart.identity(lifted), 2)
                assert contradictory(rows, rhs_next), "A mod-8 obstruction is missing"

    mod_two = {1: 33, 2: 384, 3: 512}[e]
    extra = slope.numerator % 3 == 2 and e == 3
    assert counts == [mod_two, 4 if extra else 0, 4096 if extra else 0]
    print(
        f"h={slope}: {counts[0]} normalized tuples mod 2; "
        f"{counts[1]} have a mod-4 lift; {counts[2]} tuples mod 4; 0 lift mod 8."
    )
    return used


if __name__ == "__main__":
    counts = [len(split_residues(e, TARGET_PARITY)) for e in range(1, 7)]
    assert counts == [33, 3, 1, 0, 0, 0]
    print("Nonconstant split residues by reduced slope denominator 1..6:", counts)
    source = Path(__file__).with_name("TwoPointAlternateTwo.lean").read_text()
    data = (
        source.split("def contradictorySubsystems :", 1)[1]
        .split(":= #[", 1)[1]
        .split("\n]", 1)[0]
    )
    certificates = [set(rows) for rows in literal_eval("[" + data + "]")]
    assert len(certificates) == 37
    used = set()
    for h in ("1", "2", "3/2", "5/2", "2/3", "4/3", "5/3", "7/3", "8/3", "11/3"):
        used.update(check_chart(Fraction(h), certificates))
    assert used == set(range(len(certificates)))
    print(
        "Every terminal correction matrix contains a Lean-certified inconsistent subsystem."
    )
