#!/usr/bin/env python3
"""Tests of elimination/ordering selection; all completion data are mock gates."""

import itertools
import json
import tempfile
from copy import deepcopy
from pathlib import Path
from unittest.mock import patch

import exact_sign_branch_aggregate as audit
from exact_algebra_backend import monomial_dimension
from exact_msolve_backend import parse_leading
from exact_msolve_native_branch_elimination import eliminated_branch_definitions
from exact_msolve_native_sign_branch import branch_definitions
from exact_standard_monomials import count_standard_monomials

HERE = Path(__file__).resolve().parent


def main():
    checks = []

    def reject(name, fn):
        try:
            fn()
        except ValueError, TypeError, KeyError, OSError:
            checks.append({"name": name, "expected": "reject", "passed": True})
        else:
            raise AssertionError("unexpected acceptance: " + name)

    for branch, order in itertools.product(range(4), (None, "minimum-fill")):
        text, model = eliminated_branch_definitions(branch, order)
        model["source_sha256"] = audit.digest(text.encode())
        assert audit._check_scope(model, text.encode()) == (branch, order or "natural")
        assert model["variables"] == 96 - branch and model["generators"] == 177 - branch
        assert model["offset_variable_index"] == model["variables"] - 2
        assert model["sign_variable_index"] == model["variables"] - 1
        checks.append(
            {
                "name": f"actual-eliminated-scope-{branch}-{order}",
                "expected": "scope-only pass",
                "passed": True,
            }
        )
        for key, value in [
            ("native_branch_elimination", False),
            ("native_affine_elimination", False),
            ("native_branch_elimination", 1),
            ("variables", 97),
            ("generators", 179 + branch),
            ("offset_variable_index", 95),
            ("sign_variable_index", 96),
            ("prefix", "0"),
            ("count_multiplier", 6),
            ("count_divisor", 6),
            ("branch_manifest_sha256", audit.MANIFEST_SHA),
            ("selected_old97_pivots", []),
            ("new_index_to_old97_index", []),
            ("original_color_polynomials", []),
            ("canonical_color_affine_forms", []),
            ("old97_affine_reconstruction", []),
            ("field_domain_equations", 97),
        ]:
            bad = deepcopy(model)
            bad[key] = value
            reject(
                f"eliminated-{branch}-{order}-{key}",
                lambda bad=bad, text=text: audit._check_scope(bad, text.encode()),
            )
        unchanged, _ = branch_definitions(branch, order)
        reject(
            f"uneliminated-input-with-eliminated-scope-{branch}-{order}",
            lambda model=model, unchanged=unchanged: audit._check_scope(
                model, unchanged.encode()
            ),
        )
        fixed = (HERE / "exact_algorithms_sign_six.ms").read_bytes()
        reject(
            f"actual-known-prefix-input-{branch}-{order}",
            lambda model=model, fixed=fixed: audit._check_scope(model, fixed),
        )

    # Each permitted dimension has a genuine small monomial ideal of dimension
    # six. These exercise dynamic parsing and both counters, not a board basis.
    for n in (93, 94, 95, 96, 97):
        monomials = ["x1^2", "x2^3"] + [f"x{i}" for i in range(3, n + 1)]
        body = (
            f"#Leading ideal data\n#field characteristic: 3\n#length of basis: {n} elements\n"
            "#variable order: "
            + ",".join(f"x{i}" for i in range(1, n + 1))
            + "\n"
            + "#monomial order: graded reverse lexicographical\n["
            + ",".join(monomials)
            + "]:\n"
        )
        leading = parse_leading(body, n, 3)
        assert count_standard_monomials(leading, n, standard_basis_complete=True) == 6
        assert monomial_dimension(leading, n, seconds=10)[0] == 6
        reject(
            "dynamic-parser-wrong-variable-count-" + str(n),
            lambda body=body, n=n: parse_leading(body, n + 1, 3),
        )
        checks.append(
            {
                "name": f"dynamic-monomial-fixture-{n}",
                "expected": "dimension6 fixture, not branch count",
                "passed": True,
            }
        )

    mixed = 0
    duplicates = 0
    with tempfile.TemporaryDirectory(
        prefix="exact-branch-variant-gates-", dir=HERE
    ) as tmp:
        tmp = Path(tmp)
        paths = {}
        records = {}
        for branch, eliminated, order in itertools.product(
            range(4), (False, True), ("natural", "minimum-fill")
        ):
            p = tmp / f"branch{branch}-elim{int(eliminated)}-{order}.json"
            p.write_text(
                json.dumps(
                    {
                        "mock_test_only": True,
                        "native_sign_branch": branch,
                        "native_branch_elimination": eliminated,
                        "native_variable_order": order,
                    }
                )
            )
            paths[branch, eliminated, order] = p
            # Explicitly mocked audit output, never saved or used by production
            # audit_branch_result. The production entry rejects these JSONs.
            records[p.resolve()] = audit._AuditedBranch(
                branch,
                order,
                eliminated,
                audit.LOWER_BOUND if branch == 0 else 0,
                {"mock_gate_only": True},
            )
        variants = list(itertools.product((False, True), ("natural", "minimum-fill")))
        with patch.object(
            audit,
            "audit_branch_result",
            side_effect=lambda p, **_: records[Path(p).resolve()],
        ):
            for selections in itertools.product(variants, repeat=4):
                selected = [
                    paths[(k, *variant)] for k, variant in enumerate(selections)
                ]
                result = audit.aggregate_results(selected)
                assert result["full_labeled_board_count_decimal"] == str(
                    audit.LOWER_BOUND
                )
                assert [
                    (r["affine_eliminated"], r["order"]) for r in result["branches"]
                ] == list(selections)
                mixed += 1
            for branch in range(4):
                others = [k for k in range(4) if k != branch][:2]
                for left, right in itertools.combinations(variants, 2):
                    selected = [paths[(branch, *left)], paths[(branch, *right)]] + [
                        paths[(k, False, "natural")] for k in others
                    ]
                    reject(
                        f"cross-variant-duplicate-{branch}-{left}-{right}",
                        lambda selected=selected: audit.aggregate_results(selected),
                    )
                    duplicates += 1
        reject(
            "production-still-rejects-all-mock-variants",
            lambda: audit.aggregate_results(
                [paths[(k, True, "minimum-fill")] for k in range(4)]
            ),
        )

    # These four real completed fixtures have81 additional original-color
    # fixes. Their6/0/0/0 dimensions must not become unrestricted branch counts.
    fixture_rejections = []
    for k in range(4):
        path = HERE / f"exact_algorithms_eliminated_six_{k}.json"
        data = json.loads(path.read_bytes())
        assert data["status"] == "COMPLETE" and data["native_sign_branch"] == k
        assert len(data["prefix"]) == 81 and data["generators"] == 258 - k
        try:
            audit.audit_branch_result(path)
        except ValueError as error:
            assert str(error) == "actual input is not a frozen full branch input"
            checks.append(
                {
                    "name": f"real-eliminated-prefix-result-{k}",
                    "expected": "reject by actual input",
                    "passed": True,
                }
            )
            fixture_rejections.append(
                {
                    "branch": k,
                    "result": str(path),
                    "result_sha256": audit.digest(path.read_bytes()),
                    "rejection": str(error),
                }
            )
        else:
            raise AssertionError(
                "completed fixed-prefix fixture accepted as unrestricted"
            )

    coordinated = {}
    for name in (
        "exact_algorithms_branch_elimination_review.json",
        "exact_algorithms_eliminated_adapter_review.json",
    ):
        path = HERE / name
        report = json.loads(path.read_bytes())
        assert report["status"] == "PASS"
        coordinated[name] = audit.digest(path.read_bytes())
    owner_fixture_summary = HERE / "exact_algorithms_eliminated_six_results.json"
    owner = json.loads(owner_fixture_summary.read_bytes())
    assert owner["all_worker_processes_terminal"] and owner[
        "exact_branch_dimensions"
    ] == ["6", "0", "0", "0"]
    coordinated[owner_fixture_summary.name] = audit.digest(
        owner_fixture_summary.read_bytes()
    )

    report = {
        "status": "PASS_TESTS_ONLY",
        "tests": checks,
        "test_count": len(checks),
        "additional_frozen_eliminated_scope_checks": 8,
        "mocked_variant_selections": mixed,
        "mocked_cross_variant_duplicate_rejections": duplicates,
        "dynamic_monomial_fixture_variable_counts": [93, 94, 95, 96, 97],
        "synthetic_completions_are_only_in_memory_and_patched": True,
        "actual_complete_branch_results": 0,
        "unrestricted_count": None,
        "solver_processes_started": 0,
        "coordinated_independent_model_adapter_and_fixture_reports": coordinated,
        "completed_fixed_prefix_results_rejected": fixture_rejections,
        "partition_manifest_sha256": audit.MANIFEST_SHA,
        "elimination_manifest_sha256": audit.ELIMINATION_MANIFEST_SHA,
        "production_auditor_sha256": audit.digest(
            (HERE / "exact_sign_branch_aggregate.py").read_bytes()
        ),
    }
    (HERE / "exact_sign_branch_elimination_aggregate_check_results.json").write_text(
        json.dumps(report, indent=2) + "\n"
    )
    print(json.dumps({k: v for k, v in report.items() if k != "tests"}, indent=2))


if __name__ == "__main__":
    main()
