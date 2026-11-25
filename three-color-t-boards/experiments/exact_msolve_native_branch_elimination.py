#!/usr/bin/env python3
"""Export a frozen affine elimination of one linear sign branch."""

import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
MANIFEST = HERE / "exact_f3_branch_elimination_manifest.json"
MANIFEST_SHA = "91e25ac8803be65a12998e344060e3e48778e499722f30aaf7b5a663f8b2eaa0"


def eliminated_branch_definitions(branch, order=None):
    if (
        type(branch) is not int
        or branch not in range(4)
        or order not in (None, "minimum-fill")
    ):
        raise ValueError("unsupported eliminated branch or variable order")
    raw = MANIFEST.read_bytes()
    if hashlib.sha256(raw).hexdigest() != MANIFEST_SHA:
        raise ValueError("elimination manifest changed; independent review required")
    manifest = json.loads(raw)
    entry = manifest["branches"][branch]
    representation = entry["representations"][order is not None]
    assert representation["order"] == ("natural" if order is None else "minfill")
    model_path = HERE / representation["metadata"]
    input_path = HERE / representation["input"]
    model_raw, source = model_path.read_bytes(), input_path.read_bytes()
    if (
        hashlib.sha256(model_raw).hexdigest() != representation["metadata_sha256"]
        or hashlib.sha256(source).hexdigest() != representation["input_sha256"]
    ):
        raise ValueError(
            "eliminated branch source changed; independent review required"
        )
    model = json.loads(model_raw)
    n = 96 - branch
    if (
        model["branch_id"] != branch
        or model["variables"] != n
        or model["coupled_variables"] != n - 2
        or model["generators"] != n + 81
        or model["coefficient_characteristic"] != 3
        or model["coefficient_field"] != "F3"
        or model["individual_field_domain_count"] != n
        or model["moment_count"] != 76
        or model["e3_count"] != 4
        or model["extra_sign_square_count"] != 1
        or model["independent_offset_index"] != n - 2
        or model["independent_sign_index"] != n - 1
        or model["sign_field_domain_explicit"] is not True
        or model["count_divisor"] != 1
        or model["count_multiplier"] != 1
        or model["prefix"]
        or model["fixed_original_cells"]
        or model["exact_total_claimed"]
        or model["input_sha256"] != representation["input_sha256"]
    ):
        raise ValueError("invalid eliminated branch scope")
    text = source.decode("ascii")
    header, prime, body = text.split("\n", 2)
    if (
        header != ",".join(f"x{i + 1}" for i in range(n))
        or prime != "3"
        or len(body.strip().split(",\n")) != n + 81
    ):
        raise ValueError("invalid eliminated branch input layout")
    metadata = {
        "model": "ternary-native-field-f3-affine-eliminated-branch",
        "prime": 3,
        "field": "F3",
        "ring_type": "ordinary polynomial ring",
        "variables": n,
        "coupled_variables": n - 2,
        "generators": n + 81,
        "scope": model["scope"],
        "count_scope": f"full labeled boards in branch {branch}",
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
        "native_sign_branch": branch,
        "native_branch_elimination": True,
        "native_affine_elimination": True,
        "native_variable_order": order or "natural",
        "field_domain_equations": n,
        "offset_variable_index": n - 2,
        "sign_variable_index": n - 1,
        "full_count_rule": model["full_count_rule"],
        "required_branch_ids": [0, 1, 2, 3],
        "branch_original_condition": model["branch_original_condition"],
        "branch_canonical_condition": model["branch_canonical_condition"],
        "original_color_reconstruction": model["original_color_reconstruction"],
        "original_color_polynomials": model[
            "original_color_degree_at_most2_polynomials"
        ],
        "canonical_color_affine_forms": model["canonical_color_affine_forms"],
        "inverse_reconstruction": model["inverse_reconstruction"],
        "old97_affine_reconstruction": model[
            "all_old97_affine_polynomials_in_new_variables"
        ],
        "selected_old97_pivots": model["selected_pivots_in_old97_indices"],
        "new_index_to_old97_index": model["new_index_to_old97_index"],
        "source": str(model_path),
        "source_sha256": representation["metadata_sha256"],
        "input_sha256": representation["input_sha256"],
        "branch_model_source_sha256": representation["metadata_sha256"],
        "branch_manifest_sha256": MANIFEST_SHA,
        "branch_exporter_sha256": hashlib.sha256(
            Path(__file__).read_bytes()
        ).hexdigest(),
        "status": "PREPARED_NOT_RUN",
        "standard_basis_complete": False,
    }
    return text, metadata
