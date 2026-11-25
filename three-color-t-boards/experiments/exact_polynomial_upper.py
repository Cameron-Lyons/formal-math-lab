#!/usr/bin/env python3
"""Upper bounds from an explicitly separate monomial relaxation, never a GB claim.

For known members f of the board ideal I, J=<LM(f)> is contained in in(I).
Every monomial generating set is a Groebner basis of its own monomial ideal J.
Thus the exact staircase count of J is an UPPER BOUND for dim(R/I), not the
dimension of I. No polynomial solver is started by this program.
"""

import argparse
import hashlib
import itertools
import json
import resource
import signal
import subprocess
import sys
import time
from pathlib import Path

from exact_algebra_backend import monomial_dimension
from exact_msolve_review import parse_polynomial
from exact_standard_monomials import count_standard_monomials

HERE = Path(__file__).resolve().parent
ROTOR_BOUND = 3**19 * 6**27
KINDS = ["native-e3", "translated-e3", "translated-e3-minfill", "sign", "sign-minfill"]
KINDS += [f"branch{k}-{order}" for k in range(4) for order in ("natural", "minfill")]


def model(kind):
    if kind == "native-e3":
        from exact_msolve_native_e3 import augment
        from exact_msolve_native_field import native_definitions

        return augment(*native_definitions())
    if kind.startswith("translated-e3"):
        from exact_msolve_translation import translation_definitions

        source, metadata = translation_definitions(e3=True)
        if kind.endswith("-minfill"):
            from exact_msolve_native_order import reorder

            source, metadata = reorder(source, metadata)
        return source, metadata
    if kind.startswith("sign"):
        from exact_msolve_native_sign import sign_definitions

        return sign_definitions("minimum-fill" if kind.endswith("-minfill") else None)
    if kind.startswith("branch"):
        from exact_msolve_native_branch_elimination import eliminated_branch_definitions

        branch, order = kind[6:].split("-")
        return eliminated_branch_definitions(
            int(branch), "minimum-fill" if order == "minfill" else None
        )
    raise ValueError("unknown input model")


def drl_key(exponents):
    return sum(exponents), tuple(-e for e in reversed(exponents))


def parse_leading(source, variables):
    header, field, body = source.split("\n", 2)
    if header != ",".join(f"x{i + 1}" for i in range(variables)) or field != "3":
        raise ValueError("unsupported ring header")
    leading, domains, generator_count, terms = [], set(), 0, 0
    for text in body.strip().split(",\n"):
        poly = parse_polynomial(text, variables, 3)
        if not poly:
            raise ValueError("unexpected zero polynomial")
        leading.append(max(poly, key=drl_key))
        generator_count += 1
        terms += len(poly)
        if len(poly) == 2:
            for i in range(variables):
                cube, linear = [0] * variables, [0] * variables
                cube[i], linear[i] = 3, 1
                c, l = poly.get(tuple(cube)), poly.get(tuple(linear))
                if c and l and (c + l) % 3 == 0:
                    domains.add(i)
                    break
    if domains != set(range(variables)):
        raise ValueError("missing explicit ordinary field-domain generator")
    return sorted(set(leading)), generator_count, terms


class CounterTimeout(Exception):
    pass


def bounded_count(call, seconds=15):
    def timeout(_signum, _frame):
        raise CounterTimeout("bounded auxiliary monomial count timed out")

    previous = signal.signal(signal.SIGALRM, timeout)
    signal.setitimer(signal.ITIMER_REAL, seconds)
    try:
        return call()
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)
        signal.signal(signal.SIGALRM, previous)


def worker(kind):
    resource.setrlimit(resource.RLIMIT_AS, (768 * 1024**2, 768 * 1024**2))
    resource.setrlimit(resource.RLIMIT_CPU, (40, 41))
    started = time.monotonic()
    source, metadata = model(kind)
    n = metadata["variables"]
    assert metadata["count_divisor"] == metadata["count_multiplier"] == 1
    assert metadata["prefix"] == "" and metadata["fixed_original_cells"] == []
    leading, generators, terms = parse_leading(source, n)
    assert generators == metadata["generators"]
    stats = {}
    # This attestation is ONLY for the monomial ideal J, which is its own GB.
    # It does not attest a completed basis of the source polynomial ideal I.
    value = bounded_count(
        lambda: count_standard_monomials(
            leading, n, standard_basis_complete=True, max_states=100000, stats=stats
        )
    )
    reference, ref_stats = bounded_count(
        lambda: monomial_dimension(leading, n, seconds=14)
    )
    assert value == reference
    return {
        "format": "monomial-relaxation-upper-v1",
        "status": "CERTIFIED_UPPER_BOUND",
        "source_kind": kind,
        "source_input_sha256": hashlib.sha256(source.encode()).hexdigest(),
        "variables": n,
        "source_generators": generators,
        "source_terms": terms,
        "coefficient_field": "F3",
        "order": "degree reverse lexicographic, x1 > ... > xn",
        "source_polynomial_basis_complete": False,
        "exact_board_count": None,
        "auxiliary_monomial_ideal": "J = ideal of the listed source leading monomials",
        "auxiliary_monomial_basis_complete": True,
        "attestation_scope": "monomial generators themselves form a GB of J; no GB claim for I",
        "containment": "J is a subideal of in_DRL(I)",
        "consequence": "dim(R/I) <= dim(R/J)",
        "count_scope": metadata["count_scope"],
        "count_divisor": 1,
        "count_multiplier": 1,
        "unique_leading_monomials": len(leading),
        "leading_monomials": leading,
        "auxiliary_quotient_dimension_decimal": str(value),
        "upper_bound_decimal": str(value),
        "counter_stats": stats,
        "independent_counter_stats": ref_stats,
        "elapsed_seconds": time.monotonic() - started,
    }


def fixtures():
    # A deliberately incomplete polynomial list: <xy+1,x^3-x,y^3-y> has two
    # F3 zeros, but its source-leading relaxation has five standard monomials.
    source = "x1,x2\n3\nx1*x2+1,\nx1^3+2*x1,\nx2^3+2*x2\n"
    leading, _, _ = parse_leading(source, 2)
    a = count_standard_monomials(leading, 2, standard_basis_complete=True)
    b, _ = monomial_dimension(leading, 2)
    points = sum((x * y + 1) % 3 == 0 for x, y in itertools.product(range(3), repeat=2))
    assert a == b == 5 and points == 2 and points < a
    # Leading terms are selected AFTER collecting and reducing coefficients.
    cancelled = parse_polynomial("x1^2+2*x1^2+x2", 2, 3)
    assert max(cancelled, key=drl_key) == (0, 1)
    assert max([(2, 0, 0), (0, 1, 1)], key=drl_key) == (2, 0, 0)
    assert max([(1, 0, 1), (0, 2, 0)], key=drl_key) == (0, 2, 0)
    return {
        "status": "PASS",
        "deliberately_nonsharp_bound": 5,
        "actual_small_fixture_count": 2,
        "cancellation_before_leading": True,
        "drl_tie_checks": 2,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--worker", choices=KINDS)
    parser.add_argument(
        "--output", type=Path, default=HERE / "exact_polynomial_upper_results.json"
    )
    args = parser.parse_args()
    if args.worker:
        print(json.dumps(worker(args.worker)))
        return
    if args.output.exists():
        raise FileExistsError(args.output)
    result = {
        "format": "polynomial-upper-bound-study-v1",
        "fixture_checks": fixtures(),
        "source_polynomial_basis_complete": False,
        "exact_board_count": None,
        "rotor_upper_bound_decimal": str(ROTOR_BOUND),
        "models": [],
    }
    for kind in KINDS:
        try:
            run = subprocess.run(
                [sys.executable, __file__, "--worker", kind],
                text=True,
                capture_output=True,
                timeout=45,
                check=False,
            )
            if run.returncode:
                raise RuntimeError(
                    f"worker returncode {run.returncode}: {run.stderr[-2000:]}"
                )
            record = json.loads(run.stdout)
        except (subprocess.TimeoutExpired, RuntimeError, ValueError) as error:
            record = {
                "source_kind": kind,
                "status": "INCOMPLETE_AUXILIARY_COUNT",
                "upper_bound_decimal": None,
                "error": str(error),
            }
        result["models"].append(record)
        print(kind, record["status"], record.get("upper_bound_decimal"), flush=True)
    complete = {
        r["source_kind"]: int(r["upper_bound_decimal"])
        for r in result["models"]
        if r["status"] == "CERTIFIED_UPPER_BOUND"
    }
    full = {
        kind: count for kind, count in complete.items() if not kind.startswith("branch")
    }
    if full:
        result["best_full_polynomial_upper_decimal"] = str(min(full.values()))
    branch_best = {}
    for k in range(4):
        values = [
            complete[name]
            for name in (f"branch{k}-natural", f"branch{k}-minfill")
            if name in complete
        ]
        if values:
            branch_best[str(k)] = str(min(values))
    result["branch_best_upper_decimal"] = branch_best
    if len(branch_best) == 4:
        total = sum(map(int, branch_best.values()))
        result["sum_disjoint_branch_upper_decimal"] = str(total)
        result["branch_upper_improves_rotor"] = total < ROTOR_BOUND
        result["branch_upper_to_rotor_exact_ratio"] = [str(total), str(ROTOR_BOUND)]
    result["generator_sha256"] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    result["counter_source_sha256"] = {
        name: hashlib.sha256((HERE / name).read_bytes()).hexdigest()
        for name in ("exact_standard_monomials.py", "exact_algebra_backend.py")
    }
    args.output.write_text(json.dumps(result, indent=2) + "\n")


if __name__ == "__main__":
    main()
