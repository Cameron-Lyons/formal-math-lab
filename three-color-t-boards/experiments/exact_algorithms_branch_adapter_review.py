#!/usr/bin/env python3
"""Independent adapter audit for all four branches and both orders; no solver."""

import hashlib
import json
import subprocess
import sys
from pathlib import Path

import exact_msolve_backend as backend
from exact_algorithms_sign_review import add, linear, mul, packed, parse

HERE = Path(__file__).resolve().parent
OUT = HERE / "exact_algorithms_branch_adapter_cases"
MANIFEST_SHA = "9ecb49f828699a3966c0349bddb4bc4f57cc163b65ba1855770357bf2e39d2c7"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def verify_metadata(meta, model, k, label, input_hash, prepared=False):
    for key, value in {
        "prime": 3,
        "field": "F3",
        "ring_type": "ordinary polynomial ring",
        "variables": 97,
        "coupled_variables": 95,
        "generators": 179 + k,
        "count_divisor": 1,
        "count_multiplier": 1,
        "prefix": "",
        "fixed_prefix_rows": 0,
        "fixed_cell_count": 0,
        "fixed_original_cells": [],
        "extension_variable": False,
        "ternary_native_field": True,
        "native_translation": True,
        "native_e3": True,
        "native_sign": False,
        "native_sign_branch": k,
        "native_variable_order": "natural" if label == "natural" else "minimum-fill",
        "field_domain_equations": 97,
        "offset_variable_index": 95,
        "sign_variable_index": 96,
        "required_branch_ids": [0, 1, 2, 3],
        "status": "PREPARED_NOT_RUN",
        "standard_basis_complete": False,
        "input_sha256": input_hash,
        "branch_manifest_sha256": MANIFEST_SHA,
    }.items():
        assert meta.get(key) == value, (key, meta.get(key), value)
    assert type(meta["native_sign_branch"]) is int
    assert meta["count_scope"] == f"full labeled boards in branch {k}"
    for key in [
        "scope",
        "full_count_rule",
        "branch_original_condition",
        "branch_canonical_condition",
        "independent_factors",
        "original_color_reconstruction",
        "inverse_reconstruction",
        "original_prefix_reconstruction",
        "original_cell_order",
        "free_canonical_prefix_indices",
        "original_color_bilinear_polynomials",
    ]:
        assert meta[key] == model[key], key
    assert (
        meta["canonical_color_linear_forms"] == model["normalized_color_linear_forms"]
    )
    assert "original_color_linear_forms" not in meta
    assert "sign_model_source_sha256" not in meta
    assert "dimension_decimal" not in meta and "board_count_decimal" not in meta
    model_path = HERE / f"exact_f3_sign_branch{k}_{label}.json"
    assert meta["branch_model_source_sha256"] == sha(model_path)
    assert meta["source_sha256"] == (input_hash if prepared else sha(model_path))
    if prepared:
        assert meta["basis_complete"] is False


def main():
    manifest_path = HERE / "exact_f3_sign_branches_manifest.json"
    assert sha(manifest_path) == MANIFEST_SHA
    manifest = json.loads(manifest_path.read_text())
    OUT.mkdir(exist_ok=False)
    cases = []
    for k in range(4):
        for label, order in [("natural", None), ("minfill", "minimum-fill")]:
            args = {
                "prime": 3,
                "ternary_native_field": True,
                "native_translation": True,
                "native_e3": True,
                "native_sign_branch": k,
                "native_order": order,
            }
            expected_path = HERE / manifest["branches"][k][label + "_input"]
            expected = expected_path.read_text()
            input_hash = sha(expected_path)
            assert input_hash == manifest["branches"][k][label + "_sha256"]
            model = json.loads(expected_path.with_suffix(".json").read_text())
            text, meta = backend.definitions(**args)
            assert text == expected
            verify_metadata(meta, model, k, label, input_hash)
            n, polys = parse(text)
            assert n == 97 and len(polys) == 179 + k
            # Independently derive the sparse branch equations from color forms.
            forms = {
                int(c): linear(f)
                for c, f in model["normalized_color_linear_forms"].items()
            }
            delta = [
                add(forms[a], forms[b], -1)
                for a, b in zip([0, 1, 2, 3], [3, 6, 7, 8], strict=False)
            ]
            assert polys[178:] == [*delta[:k], add(delta[k], {(): 2})]
            assert polys[176] == {((96, 3),): 1, ((96, 1),): 2}
            assert polys[177] == {((96, 2),): 1, (): 2}
            for cell in range(100):
                expected_form = add({((95, 1),): 1}, mul({((96, 1),): 1}, forms[cell]))
                assert (
                    packed(meta["original_color_bilinear_polynomials"][str(cell)])
                    == expected_form
                )
            output = OUT / f"branch{k}_{label}"
            command = [
                sys.executable,
                str(HERE / "exact_msolve_backend.py"),
                "--prime",
                "3",
                "--ternary-native-field",
                "--native-e3",
                "--native-translation",
                "--native-sign-branch",
                str(k),
                "--prepare-only",
                "--output",
                str(output),
            ]
            if order is not None:
                command += ["--native-order", order]
            process = subprocess.run(
                command, capture_output=True, text=True, timeout=20, check=False
            )
            output.with_suffix(".cli.log").write_text(process.stdout + process.stderr)
            assert process.returncode == 0, (command, process.stderr)
            assert output.with_suffix(".ms").read_text() == expected
            prepared = json.loads(output.with_suffix(".json").read_text())
            verify_metadata(prepared, model, k, label, input_hash, prepared=True)
            assert not output.with_suffix(".basis").exists()
            cases.append(
                {
                    "branch": k,
                    "order": label,
                    "input_sha256": input_hash,
                    "model_sha256": sha(expected_path.with_suffix(".json")),
                }
            )
    valid = {
        "prime": 3,
        "ternary_native_field": True,
        "native_translation": True,
        "native_e3": True,
        "native_sign_branch": 0,
    }
    overrides = [
        {"prime": 2},
        {"prime": 29},
        {"prefix": "0"},
        {"binary": True},
        {"fixture": "domain"},
        {"pivot_order": True},
        {"ternary_reduced": "all"},
        {"histogram_e2": True},
        {"ternary_prefix_sums": "all"},
        {"prefix_field_equations": True},
        {"histogram_e4": True},
        {"ternary_native_field": False},
        {"native_translation": False},
        {"native_e3": False},
        {"native_sign": True},
        {"native_order": "natural"},
        *[{"native_sign_branch": x} for x in [-1, 4, False, True, 0.0, "0"]],
    ]
    rejected = []
    for override in overrides:
        try:
            backend.definitions(**(valid | override))
        except ValueError:
            rejected.append(override)
        else:
            raise AssertionError(("invalid scope accepted", override))
    # Both zero and three must trigger the model requirement even when falsey zero is supplied.
    for branch in [0, 1, 2, 3]:
        try:
            backend.definitions(native_sign_branch=branch)
        except ValueError:
            rejected.append({"default_model_with_branch": branch})
        else:
            raise AssertionError("branch ignored")
    cli_failures = []
    for index, flags in enumerate(
        [
            ["--native-sign-branch", "0"],
            [
                "--prime",
                "3",
                "--ternary-native-field",
                "--native-translation",
                "--native-sign-branch",
                "0",
            ],
            [
                "--prime",
                "3",
                "--ternary-native-field",
                "--native-e3",
                "--native-translation",
                "--native-sign",
                "--native-sign-branch",
                "0",
            ],
            [
                "--prime",
                "3",
                "--ternary-native-field",
                "--native-e3",
                "--native-translation",
                "--native-sign-branch",
                "4",
            ],
        ]
    ):
        output = OUT / f"reject{index}"
        cmd = [
            sys.executable,
            str(HERE / "exact_msolve_backend.py"),
            *flags,
            "--prepare-only",
            "--output",
            str(output),
        ]
        p = subprocess.run(cmd, capture_output=True, text=True, timeout=20, check=False)
        output.with_suffix(".cli.log").write_text(p.stdout + p.stderr)
        assert p.returncode != 0 and not output.with_suffix(".ms").exists()
        cli_failures.append(flags)
    result = {
        "status": "PASS",
        "scope": "independent branch adapter review; no solver",
        "input_variants": cases,
        "actual_prepared_inputs": 8,
        "branch_zero_explicitly_checked": True,
        "bilinear_forms_checked": 800,
        "definition_rejections": len(rejected),
        "cli_rejections": len(cli_failures),
        "rejected_arguments": rejected,
        "full_solver_runs": 0,
        "solver_processes_launched": 0,
        "backend_sha256": sha(HERE / "exact_msolve_backend.py"),
        "helper_sha256": sha(HERE / "exact_msolve_native_sign_branch.py"),
        "reviewer_sha256": sha(Path(__file__)),
    }
    (HERE / "exact_algorithms_branch_adapter_review.json").write_text(
        json.dumps(result, indent=2) + "\n"
    )
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
