#!/usr/bin/env python3
"""Mock-gate tests only: no branch is computed or certified by this script."""

import itertools
import json
import subprocess
import sys
import tempfile
from copy import deepcopy
from pathlib import Path

import exact_sign_branch_aggregate as audit
from exact_algebra_backend import monomial_dimension
from exact_msolve_backend import parse_leading
from exact_msolve_native_sign_branch import branch_definitions
from exact_standard_monomials import count_standard_monomials

HERE = Path(__file__).resolve().parent


def main():
    checks = []

    def reject(name, action):
        try:
            action()
        except ValueError, OSError, KeyError, TypeError:
            checks.append({"name": name, "expected": "reject", "passed": True})
        else:
            raise AssertionError("unexpected acceptance: " + name)

    # Source-only checks of every one of the eight actual frozen inputs.
    for branch, order in itertools.product(range(4), (None, "minimum-fill")):
        text, data = branch_definitions(branch, order)
        data["source_sha256"] = audit.digest(text.encode())
        assert audit._check_scope(data, text.encode()) == (branch, order or "natural")
        checks.append(
            {
                "name": f"actual-scope-{branch}-{order}",
                "expected": "scope-only pass",
                "passed": True,
            }
        )

    text, base = branch_definitions(0)
    raw = text.encode()
    base["source_sha256"] = audit.digest(raw)
    for key, value in [
        ("native_sign_branch", False),
        ("native_sign_branch", 4),
        ("native_sign_branch", 1),
        ("native_variable_order", "affine-eliminated"),
        ("variables", 96),
        ("generators", 180),
        ("prefix", "0"),
        ("fixed_original_cells", [0]),
        ("count_divisor", 2),
        ("count_multiplier", 6),
        ("offset_variable_index", 94),
        ("sign_variable_index", 95),
        ("extension_variable", True),
        ("branch_manifest_sha256", "0" * 64),
        ("branch_model_source_sha256", "0" * 64),
        ("source_sha256", "0" * 64),
        ("input_sha256", "0" * 64),
        ("native_sign", True),
        ("field_domain_equations", 96),
        ("coupled_variables", 94),
        ("mock_test_only", True),
        ("affine_eliminated", True),
        ("count_scope", "all full labeled boards"),
    ]:
        bad = deepcopy(base)
        bad[key] = value
        reject(
            "scope-" + key + "-" + str(value),
            lambda bad=bad: audit._check_scope(bad, raw),
        )
    for name, changed in [
        ("truncated", raw[:-30]),
        ("header96", raw.replace(b"x96,x97\n", b"x96\n", 1)),
        ("extra-fix", raw.rstrip() + b",\nx1\n"),
    ]:
        reject(
            "actual-input-" + name,
            lambda changed=changed: audit._check_scope(base, changed),
        )
    fixed_prefix = HERE / "exact_algorithms_sign_six.ms"
    assert fixed_prefix.exists()
    reject(
        "known-prefix-cannot-masquerade-as-full-branch",
        lambda: audit._check_scope(base, fixed_prefix.read_bytes()),
    )

    # Synthetic process records exercise individual gate functions only. They
    # are never submitted as authoritative branch results or saved as counts.
    done = {
        "status": "COMPLETE",
        "returncode": 0,
        "basis_complete": True,
        "standard_basis_complete": True,
        "require_export_marker": True,
        "export_marker_count": 1,
        "error_diagnostics": [],
        "linear_algebra": "exact sparse (-l 2)",
        "threads": 1,
        "dimension_decimal": "6",
        "board_count_decimal": "6",
    }
    log = "synthetic unit-test log\n" + audit.MARKER + "\n"
    assert audit._check_terminal(done, log) == 6
    checks.append(
        {
            "name": "mock-terminal-positive-gate",
            "expected": "gate-only pass; not a count",
            "passed": True,
        }
    )
    for key, value in [
        ("status", "PREPARED_NOT_RUN"),
        ("status", "INCOMPLETE_TIMEOUT"),
        ("status", "BACKEND_ERROR"),
        ("status", "POSTPROCESS_ERROR"),
        ("status", "COMPLETE_FROM_LEADING_IDEAL"),
        ("returncode", 1),
        ("returncode", -11),
        ("returncode", False),
        ("basis_complete", False),
        ("standard_basis_complete", False),
        ("leading_export_complete", False),
        ("dimension_complete", False),
        ("require_export_marker", False),
        ("export_marker_count", 2),
        ("export_marker_count", True),
        ("error_diagnostics", ["allocation failed"]),
        ("postprocess_error", "counter timeout"),
        ("linear_algebra", "probabilistic"),
        ("threads", 2),
        ("threads", True),
        ("dimension_decimal", "006"),
        ("dimension_decimal", "6.0"),
        ("dimension_decimal", "-6"),
        ("dimension_decimal", 6),
        ("board_count_decimal", "12"),
        ("board_count_decimal", "3"),
    ]:
        bad = deepcopy(done)
        bad[key] = value
        reject(
            "terminal-" + key + "-" + str(value),
            lambda bad=bad: audit._check_terminal(bad, log),
        )
    for name, changed in [
        ("missing-marker", ""),
        ("duplicate-marker", log + audit.MARKER + "\n"),
        ("false-marker", "prefix " + audit.MARKER + " suffix\n"),
        ("allocation-failed", log + "exponent allocation failed\n"),
        ("error", log + "Error: bad result\n"),
        ("segmentation", log + "segmentation fault\n"),
    ]:
        reject(
            "log-" + name, lambda changed=changed: audit._check_terminal(done, changed)
        )

    # Tiny algebra fixture: independent dimension6, with exactly97 variable
    # names in the parser. This is a monomial-ideal test, not a branch basis.
    terms = ["x1^2", "x2^3"] + [f"x{i}" for i in range(3, 98)]
    body = (
        "#Leading ideal data\n#field characteristic: 3\n#length of basis: 97 elements\n"
        "#variable order: "
        + ",".join(f"x{i}" for i in range(1, 98))
        + "\n"
        + "#monomial order: graded reverse lexicographical\n["
        + ",".join(terms)
        + "]:\n"
    )
    leading = parse_leading(body, 97, 3)
    assert count_standard_monomials(leading, 97, standard_basis_complete=True) == 6
    assert monomial_dimension(leading, 97, seconds=10)[0] == 6
    for name, changed in [
        ("missing-end", body[:-2]),
        ("wrong-field", body.replace("characteristic: 3", "characteristic: 2")),
        ("wrong-size", body.replace("97 elements", "96 elements")),
        ("wrong-name", body.replace("x96,x97\n", "x96,a\n")),
        ("duplicate-marker", body + "#Leading ideal data\n"),
    ]:
        reject("basis-" + name, lambda changed=changed: parse_leading(changed, 97, 3))

    # Mock aggregation arithmetic. No synthetic total is emitted to a file.
    mock = [(0, audit.LOWER_BOUND), (1, 0), (2, 0), (3, 0)]
    assert audit._sum_branch_counts(mock) == audit.LOWER_BOUND
    assert (
        audit._sum_branch_counts([(0, 6), (1, audit.LOWER_BOUND - 6), (2, 0), (3, 0)])
        == audit.LOWER_BOUND
    )
    reject("missing-branch", lambda: audit._sum_branch_counts(mock[:3]))
    reject(
        "duplicate-alternative-order", lambda: audit._sum_branch_counts([*mock, (0, 0)])
    )
    reject("replaced-duplicate", lambda: audit._sum_branch_counts([*mock[:3], (2, 0)]))
    reject(
        "branch-not-multiple6",
        lambda: audit._sum_branch_counts(
            [(0, audit.LOWER_BOUND + 1), (1, 0), (2, 0), (3, 0)]
        ),
    )
    reject(
        "below-certified-bound",
        lambda: audit._sum_branch_counts([(i, 0) for i in range(4)]),
    )
    reject(
        "total-not-multiple12",
        lambda: audit._sum_branch_counts(
            [(0, audit.LOWER_BOUND + 6), (1, 0), (2, 0), (3, 0)]
        ),
    )
    reject(
        "negative-count",
        lambda: audit._sum_branch_counts(
            [(0, -6), (1, audit.LOWER_BOUND + 6), (2, 0), (3, 0)]
        ),
    )
    reject(
        "boolean-count",
        lambda: audit._sum_branch_counts(
            [(0, False), (1, audit.LOWER_BOUND), (2, 0), (3, 0)]
        ),
    )
    reject("empty-results", lambda: audit.aggregate_results([]))
    with tempfile.TemporaryDirectory(
        prefix="exact-sign-branch-mock-", dir=HERE
    ) as folder:
        folder = Path(folder)
        paths = []
        for k in range(4):
            p = folder / f"mock-{k}.json"
            p.write_text(
                json.dumps(
                    {
                        "mock_test_only": True,
                        "native_sign_branch": k,
                        "status": "COMPLETE",
                    }
                )
            )
            paths.append(p)
        reject(
            "production-rejects-synthetic-completion",
            lambda: audit.aggregate_results(paths),
        )
        p = folder / "duplicate.json"
        p.write_text(json.dumps({"native_sign_branch": 0}))
        reject(
            "production-rejects-duplicate-ID-before-recount",
            lambda: audit.aggregate_results([*paths[:3], p]),
        )
        data = json.loads(paths[0].read_text())
        data["native_sign_branch"] = False
        paths[0].write_text(json.dumps(data))
        reject("production-rejects-boolean-ID", lambda: audit.aggregate_results(paths))
    cli = subprocess.run(
        [sys.executable, str(HERE / "exact_sign_branch_aggregate.py")],
        capture_output=True,
        text=True,
        timeout=10,
        check=False,
    )
    result = json.loads(cli.stdout)
    assert (
        cli.returncode == 1
        and result["status"] == "INCOMPLETE_OR_INVALID"
        and result["full_labeled_board_count_decimal"] is None
    )
    report = {
        "status": "PASS_TESTS_ONLY",
        "tests": checks,
        "test_count": len(checks),
        "frozen_actual_input_scope_checks": 8,
        "arithmetic_and_terminal_tests_use_mocks": True,
        "tiny_monomial_fixture_is_not_a_branch_basis": True,
        "actual_complete_branch_results": 0,
        "unrestricted_count": None,
        "solver_processes_started": 0,
        "manifest_sha256": audit.MANIFEST_SHA,
        "production_auditor_sha256": audit.digest(
            (HERE / "exact_sign_branch_aggregate.py").read_bytes()
        ),
    }
    (HERE / "exact_sign_branch_aggregate_check_results.json").write_text(
        json.dumps(report, indent=2) + "\n"
    )
    print(json.dumps({k: v for k, v in report.items() if k != "tests"}, indent=2))


if __name__ == "__main__":
    main()
