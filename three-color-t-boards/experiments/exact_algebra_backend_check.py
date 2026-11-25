#!/usr/bin/env python3
"""Reproduce small algebra checks; optionally repeat the two known ternary fibers."""

import argparse
import json
from pathlib import Path
from unittest.mock import patch

import exact_algebra_backend as backend
from exact_standard_monomials import count_standard_monomials

ROOT = Path(__file__).resolve().parent
FIXTURES = {
    "domain1": 3,
    "domain2": 9,
    "diagonal": 3,
    "cyclotomic": 2,
    "fourier3": 6,
    "fourier3-reduced": 6,
    "gf4-linear": 1,
    "zero": 0,
    "bigint-product": 10**20,
}
FIBERS = [
    (
        "one",
        "000000100002011001202102210110211112012122202200112210102022200122211121210122112",
        1,
    ),
    (
        "six",
        "100011101011000101010011112112211212021201221022121202020220010222002102100022222",
        6,
    ),
]


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--include-fibers", action="store_true")
    a = p.parse_args()
    results = []
    for name, expected in FIXTURES.items():
        r = backend.run(
            "fixture:" + name,
            ROOT / ("exact_algebra_backend_check_" + name.replace("-", "_")),
            timeout=10,
        )
        assert r["status"] == "COMPLETE" and r["quotient_dimension"] == expected
        assert r["hilbert_dimension"] == r["independent_monomial_dimension"] == expected
        results.append(
            {"test": name, "status": "PASS", "dimension_decimal": str(expected)}
        )
    for model, count in [
        ("ternary-original", 140),
        ("ternary-reduced", 136),
        ("binary-reduced", 32),
    ]:
        _, m = backend.definitions(model)
        assert m["generators"] == count
        results.append(
            {"test": model + " generator count", "status": "PASS", "generators": count}
        )
    for model in [
        "ternary-reduced",
        "binary-reduced",
        "ternary-prefix",
        "fixture:domain1",
    ]:
        try:
            backend.definitions(model, normalize_apex=True)
        except ValueError:
            pass
        else:
            raise AssertionError("unsupported normalization was accepted: " + model)
    definition, metadata = backend.definitions("ternary-original", normalize_apex=True)
    assert (
        metadata["generators"] == 141
        and metadata["unrestricted_multiplier"] == 3
        and ",\nx1+1;\n" in definition
    )
    results.append(
        {
            "test": "apex normalization is imposed and only supported for original model",
            "status": "PASS",
        }
    )
    with patch.object(
        backend,
        "definitions",
        lambda *args: (
            "ring R=2,(x1),dp;\nideal I=x1;\nthisProcedureDoesNotExist();\n",
            {
                "model": "fixture:diagnostic",
                "variables": 1,
                "generators": 1,
                "field": "F2",
            },
        ),
    ):
        out = ROOT / "exact_algebra_backend_check_diagnostic"
        r = backend.run("fixture:diagnostic", out, timeout=10)
        assert (
            r["status"] == "BACKEND_ERROR"
            and not r["basis_complete"]
            and "quotient_dimension" not in r
        )
        assert "BACKEND_COMPLETE" in out.with_suffix(".log").read_text()
        results.append(
            {
                "test": "actual Singular diagnostic rejects later completed-looking output",
                "status": "PASS",
            }
        )
    prime_fixtures = [
        ("prime29_domain", "ring R=29,(x1),dp;\nideal I=x1^3-1;\n", 1, 1, 3),
        (
            "prime29_fourier3",
            "ring R=29,(x1,x2,x3),dp;\nideal I=x1^3-1,x2^3-1,x3^3-1,x1+x2+x3;\n",
            3,
            4,
            6,
        ),
        (
            "prime29_extension_color2",
            "ring R=(29,a),(x1),dp;\nminpoly=a^2+a+1;\nideal I=x1^3-1,x1+a+1;\n",
            1,
            2,
            1,
        ),
    ]
    for name, definition, n, generators, expected in prime_fixtures:
        metadata = {
            "model": "fixture:" + name,
            "variables": n,
            "generators": generators,
            "field": "F29^2" if "extension" in name else "F29",
        }
        with patch.object(
            backend,
            "definitions",
            lambda *args, definition=definition, metadata=metadata: (
                definition,
                metadata.copy(),
            ),
        ):
            r = backend.run(
                "fixture:" + name,
                ROOT / ("exact_algebra_backend_check_" + name),
                timeout=10,
            )
            assert (
                r["status"] == "COMPLETE"
                and r["quotient_dimension"]
                == r["hilbert_dimension"]
                == r["independent_monomial_dimension"]
                == expected
            )
            results.append(
                {"test": name, "status": "PASS", "dimension_decimal": str(expected)}
            )
    for name, prefix, expected in FIBERS:
        out = ROOT / ("exact_algebra_backend_ternary_prefix_" + name)
        if a.include_fibers:
            r = backend.run("ternary-prefix", out, timeout=90, prefix=prefix)
        else:
            r = json.loads(out.with_suffix(".json").read_text())
        leading = json.loads(out.with_suffix(".leading.json").read_text())
        independent = count_standard_monomials(
            leading["leading_monomials"],
            variables=leading["variables"],
            standard_basis_complete=leading["standard_basis_complete"],
        )
        assert r["prefix"] == prefix and r["status"] == "COMPLETE"
        assert (
            r["quotient_dimension"] == r["hilbert_dimension"] == independent == expected
        )
        results.append(
            {
                "test": "ternary nine-row fiber " + name,
                "status": "PASS",
                "dimension_decimal": str(expected),
                "basis_recomputed": a.include_fibers,
            }
        )
    path = ROOT / "exact_algebra_backend_check.json"
    path.write_text(json.dumps(results, indent=2) + "\n")
    print(json.dumps(results, indent=2))


if __name__ == "__main__":
    main()
