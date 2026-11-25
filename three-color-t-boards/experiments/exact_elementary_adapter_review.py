#!/usr/bin/env python3
"""Audit actual augmented msolve definitions and prepare-only artifacts."""

import hashlib
import json
from pathlib import Path
from unittest.mock import patch

import exact_msolve_backend as backend
from exact_elementary_review import (
    EDGES,
    PIVOTS,
    e2,
    geometry,
    partner,
    substitute,
    substitutions,
)
from exact_msolve_review import parse_polynomial

HERE = Path(__file__).resolve().parent


def expressions(text):
    return "\n".join(text.splitlines()[2:]).split(",")


def main():
    directory = HERE / "exact_elementary_adapter_review_prepared_verified"
    directory.mkdir(exist_ok=False)
    _, roles = geometry()
    replacements = substitutions(roles)
    free = [i for i in range(100) if i not in PIVOTS]
    original = [e2(roles["T"])] + [
        e2(roles[a] - roles[b]) ^ e2(roles[b] - roles[a]) for a, b in EDGES
    ]
    reduced = [substitute(polynomial, replacements, free) for polynomial in original]
    original += [partner(p) for p in original]
    reduced += [partner(p) for p in reduced]
    variants = [
        ("original", {}, 100, 188, original, list(range(100))),
        ("pivot", {"pivot_order": True}, 100, 188, original, list(range(100))),
        ("reduced40", {"ternary_reduced": "representatives"}, 96, 144, reduced, free),
        ("reduced80", {"ternary_reduced": "all"}, 96, 180, reduced, free),
    ]
    checks = []
    for name, options, variables, generators, expected, source_cells in variants:
        base, base_metadata = backend.base_definitions(prime=2, **options)
        unchanged, unchanged_metadata = backend.definitions(
            prime=2, histogram_e2=False, **options
        )
        assert base == unchanged and base_metadata == unchanged_metadata
        text, metadata = backend.definitions(prime=2, histogram_e2=True, **options)
        assert text.startswith(base.rstrip("\n") + ",\n")
        assert (
            metadata["variables"] == variables and metadata["generators"] == generators
        )
        assert metadata["count_divisor"] == 1 and metadata["prefix"] == ""
        assert metadata["prime"] == 2 and metadata["field"] == "F2"
        assert metadata["ring_type"] == "ordinary polynomial ring"
        assert (
            metadata["histogram_e2"] is True and metadata["elementary_generators"] == 8
        )
        assert len(expressions(text)) == generators
        assert len(expressions(base)) == generators - 8
        order = metadata.get(
            "variable_original_cells", metadata.get("free_original_cells")
        )
        assert set(order) == set(source_cells) and len(order) == variables
        if name == "pivot":
            assert order == [0, 81, 90, 99] + [i for i in range(100) if i not in PIVOTS]
        else:
            assert order == source_cells
        inverse = {cell: i for i, cell in enumerate(source_cells)}
        actual = []
        for expression in expressions(text)[-8:]:
            polynomial = parse_polynomial("".join(expression.split()), variables, 2)
            normalized = set()
            for exponents, coefficient in polynomial.items():
                assert coefficient == 1
                factors = []
                for variable, exponent in enumerate(exponents):
                    factors += [inverse[order[variable]]] * exponent
                normalized.add(tuple(sorted(factors)))
            actual.append(normalized)
        assert actual == expected, name
        if name.startswith("reduced"):
            assert (
                metadata["base_input_sha256"]
                == hashlib.sha256(base.encode()).hexdigest()
            )
            assert metadata["input_sha256"] == hashlib.sha256(text.encode()).hexdigest()
            assert [sum(len(t) == 1 for t in p) for p in actual[4:]] == [80, 32, 8, 8]
            # The complete original 96 free cubes + four pivot cubics are
            # retained byte-for-byte inside the base; no generator replacement.
            assert metadata["base_input_sha256"] != metadata["input_sha256"]
            assert metadata["reduced_source_sha256"] == base_metadata["source_sha256"]
        output = directory / name
        with patch.object(
            backend.subprocess, "run", side_effect=AssertionError("solver must not run")
        ):
            result = backend.run(
                output,
                prime=2,
                histogram_e2=True,
                prepare_only=True,
                executable=HERE / "exact_msolve_f2_bitset_tools/msolve",
                require_export_marker=True,
                seconds=1,
                memory_mb=2048,
                max_pairs=16,
                **options,
            )
        prepared = output.with_suffix(".ms").read_text()
        assert prepared == text
        assert (
            result["status"] == "PREPARED_NOT_RUN" and result["basis_complete"] is False
        )
        assert "dimension_decimal" not in result and "board_count_decimal" not in result
        assert result["source_sha256"] == hashlib.sha256(prepared.encode()).hexdigest()
        assert json.loads(output.with_suffix(".json").read_text()) == result
        assert (
            not output.with_suffix(".basis").exists()
            and not output.with_suffix(".log").exists()
        )
        for key, value in base_metadata.items():
            # run() has always used source_sha256 for the emitted .ms file;
            # the underlying reduced JSON hash survives in reduced_source_sha256.
            if key not in ("generators", "input_sha256", "source_sha256"):
                assert result[key] == value, (name, key)
        checks.append(
            {
                "mode": name,
                "variables": variables,
                "generators": generators,
                "base_generators": generators - 8,
                "appended_generators": 8,
                "appended_term_counts": list(map(len, actual)),
                "variable_map_checked_in_reverse": True,
                "base_retained_byte_for_byte": True,
                "count_divisor": 1,
                "status": result["status"],
                "input_file": str(output.with_suffix(".ms")),
                "source_sha256": result["source_sha256"],
                "base_sha256": hashlib.sha256(base.encode()).hexdigest(),
            }
        )
    invalid = [
        {"prime": 29},
        {"prime": 2, "prefix": "0"},
        {"prime": 2, "binary": True},
        {"prime": 2, "fixture": "domain"},
        {"prime": 2, "ternary_reduced": "all", "pivot_order": True},
    ]
    for options in invalid:
        try:
            backend.definitions(histogram_e2=True, **options)
        except ValueError:
            pass
        else:
            raise AssertionError("incompatible augmentation scope accepted")
    report = {
        "status": "PASS",
        "variants": checks,
        "invalid_scope_cases_rejected": len(invalid),
        "solver_processes_started": 0,
        "full_count_status": "NOT_COMPUTED",
        "backend_sha256": hashlib.sha256(
            Path(backend.__file__).read_bytes()
        ).hexdigest(),
        "augmentation_adapter_sha256": hashlib.sha256(
            (HERE / "exact_msolve_elementary.py").read_bytes()
        ).hexdigest(),
    }
    (HERE / "exact_elementary_adapter_review_results.json").write_text(
        json.dumps(report, indent=2) + "\n"
    )
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
