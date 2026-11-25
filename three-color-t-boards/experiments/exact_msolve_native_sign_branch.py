#!/usr/bin/env python3
"""Export one certified linear sign branch; all four counts must be summed."""

import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
MANIFEST = HERE / "exact_f3_sign_branches_manifest.json"
MANIFEST_SHA = "9ecb49f828699a3966c0349bddb4bc4f57cc163b65ba1855770357bf2e39d2c7"
MODEL_HASHES = [
    (
        "60e5325699e1228251a2698658d71ab487367a9f193048f8b915cc914fdb69d4",
        "2a6423b9eb6fb78b3c8317e0f90552ac90aa67907aa6ff486d849552fbba303b",
    ),
    (
        "4dd43cb48cf7685db58f47dab2d88ed847c89f92d3e1c6b8029c95e9bf78d85b",
        "4b32958c3c94f4912cd68deda550eb51945bdc57d0fa6a4821ae6841a48188ec",
    ),
    (
        "e7b28402f52cba32b55090012dd704784720b43e16c168ec7bacee28b2e39530",
        "89aa7de87cdfc334c5c2f0d9e375d0bc37d2d8d5102788cca10a307f95200f8f",
    ),
    (
        "3b6ecd98c50872a2d2463973fe1f9c0706a62b040bc024faecae781388ca19c4",
        "f61ce552ef831147c4216fd04e0a239e7c8a7e33ae8d9c7a0e730dae3b1271d9",
    ),
]


def branch_definitions(branch, order=None):
    if (
        type(branch) is not int
        or branch not in range(4)
        or order not in (None, "minimum-fill")
    ):
        raise ValueError("unsupported native sign branch or variable order")
    raw = MANIFEST.read_bytes()
    if hashlib.sha256(raw).hexdigest() != MANIFEST_SHA:
        raise ValueError("branch manifest changed; independent review required")
    manifest = json.loads(raw)
    label = "natural" if order is None else "minfill"
    entry = manifest["branches"][branch]
    input_path = HERE / entry[label + "_input"]
    model_path = input_path.with_suffix(".json")
    model_raw = model_path.read_bytes()
    source = input_path.read_bytes()
    model_hash = MODEL_HASHES[branch][order is not None]
    input_hash = entry[label + "_sha256"]
    if (
        hashlib.sha256(source).hexdigest() != input_hash
        or hashlib.sha256(model_raw).hexdigest() != model_hash
    ):
        raise ValueError("branch source changed; independent review required")
    model = json.loads(model_raw)
    if (
        model["branch_id"] != branch
        or model["coefficient_characteristic"] != 3
        or model["variables"] != 97
        or model["coupled_variables"] != 95
        or model["generators"] != 179 + branch
        or model["individual_field_domain_count"] != 97
        or model["count_divisor"] != 1
        or model["count_multiplier"] != 1
        or model["independent_offset_index"] != 95
        or model["independent_sign_index"] != 96
        or model["prefix"]
        or model["fixed_original_cells"]
        or model["quintic_selector_included"]
        or model["exact_total_claimed"]
        or model["input_sha256"] != input_hash
    ):
        raise ValueError("invalid linear branch model scope")
    text = source.decode("ascii")
    header, prime, body = text.split("\n", 2)
    if (
        header != ",".join(f"x{i + 1}" for i in range(97))
        or prime != "3"
        or len(body.strip().split(",\n")) != 179 + branch
    ):
        raise ValueError("invalid branch input layout")
    metadata = {
        "model": "ternary-native-field-f3-affine-linear-branch",
        "prime": 3,
        "field": "F3",
        "ring_type": "ordinary polynomial ring",
        "variables": 97,
        "coupled_variables": 95,
        "generators": 179 + branch,
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
        "native_variable_order": order or "natural",
        "field_domain_equations": 97,
        "offset_variable_index": 95,
        "sign_variable_index": 96,
        "full_count_rule": model["full_count_rule"],
        "required_branch_ids": [0, 1, 2, 3],
        "branch_original_condition": model["branch_original_condition"],
        "branch_canonical_condition": model["branch_canonical_condition"],
        "independent_factors": model["independent_factors"],
        "original_color_reconstruction": model["original_color_reconstruction"],
        "original_color_bilinear_polynomials": model[
            "original_color_bilinear_polynomials"
        ],
        "canonical_color_linear_forms": model["normalized_color_linear_forms"],
        "inverse_reconstruction": model["inverse_reconstruction"],
        "original_prefix_reconstruction": model["original_prefix_reconstruction"],
        "original_cell_order": model["original_cell_order"],
        "free_canonical_prefix_indices": model["free_canonical_prefix_indices"],
        "source": str(model_path),
        "source_sha256": model_hash,
        "input_sha256": input_hash,
        "branch_model_source_sha256": model_hash,
        "branch_manifest_sha256": MANIFEST_SHA,
        "branch_exporter_sha256": hashlib.sha256(
            Path(__file__).read_bytes()
        ).hexdigest(),
        "status": "PREPARED_NOT_RUN",
        "standard_basis_complete": False,
    }
    return text, metadata
