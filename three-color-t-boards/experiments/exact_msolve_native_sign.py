#!/usr/bin/env python3
"""Export the frozen native-F3 sign factorization, including both finite factors."""

import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
SOURCES = {
    None: (
        "exact_f3_sign_model",
        "a568c7b0341b54ba28d9c01cf000ac0c4fb8ecd89fb27abd9b678262d2ae85bc",
        "dd0d371541d7a0ebbff559a854a08cd89219928e56e570265d29ef31b19fa381",
    ),
    "minimum-fill": (
        "exact_f3_sign_minfill",
        "d8e366d5dabbc3eddfe0fdf519ea87b1f37602b153e47f209f70c2553db41bbd",
        "14247d0e4cfaff8636e99852902816d8d0ab97de47ada08cb2e40fa7576e71cf",
    ),
}


def sign_definitions(order=None):
    if order not in SOURCES:
        raise ValueError("unsupported native-sign variable order")
    stem, model_hash, input_hash = SOURCES[order]
    model_path = HERE / (stem + ".json")
    input_path = HERE / (stem + ".ms")
    raw = model_path.read_bytes()
    source = input_path.read_bytes()
    if (
        hashlib.sha256(raw).hexdigest() != model_hash
        or hashlib.sha256(source).hexdigest() != input_hash
    ):
        raise ValueError("sign-factor source changed; independent review required")
    model = json.loads(raw)
    if (
        model["coefficient_characteristic"] != 3
        or model["coefficient_field"] != "F3"
        or model["variables"] != 97
        or model["coupled_variables"] != 95
        or model["generators"] != 179
        or model["domain_count"] != 97
        or model["independent_offset_index"] != 95
        or model["independent_sign_index"] != 96
        or model["count_divisor"] != 1
        or model["count_multiplier"] != 1
        or model["prefix"]
        or model["fixed_original_cells"]
        or model["exact_total_claimed"]
        or model["input_sha256"] != input_hash
        or len(model["original_color_bilinear_polynomials"]) != 100
    ):
        raise ValueError("invalid sign-factor scope or reconstruction")
    text = source.decode("ascii")
    header, prime, body = text.split("\n", 2)
    if (
        header != ",".join(f"x{i + 1}" for i in range(97))
        or prime != "3"
        or len(body.strip().split(",\n")) != 179
    ):
        raise ValueError("invalid sign-factor input layout")
    metadata = {
        "model": "ternary-native-field-f3-affine-factors",
        "prime": 3,
        "field": "F3",
        "ring_type": "ordinary polynomial ring",
        "variables": 97,
        "coupled_variables": 95,
        "generators": 179,
        "count_scope": "full labeled boards",
        "scope": "full labeled ternary boards",
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
        "native_sign": True,
        "native_variable_order": order or "natural",
        "field_domain_equations": 97,
        "offset_variable_index": 95,
        "sign_variable_index": 96,
        "independent_factors": model["independent_factors"],
        "coupled_canonical_condition": model["coupled_canonical_condition"],
        "original_color_reconstruction": model["original_color_reconstruction"],
        "original_color_bilinear_polynomials": model[
            "original_color_bilinear_polynomials"
        ],
        "canonical_color_linear_forms": model["normalized_color_linear_forms"],
        "inverse_reconstruction": model["inverse_reconstruction"],
        "original_prefix_reconstruction": model["original_prefix_reconstruction"],
        "original_cell_order": model["original_cell_order"],
        "free_canonical_prefix_indices": model["free_canonical_prefix_indices"],
        "selector_placement_cells": model["selector_placement_cells"],
        "selector_expression": model["selector_expression"],
        "source": str(model_path),
        "source_sha256": model_hash,
        "sign_model_source_sha256": model_hash,
        "input_sha256": input_hash,
        "sign_exporter_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "status": "PREPARED_NOT_RUN",
        "standard_basis_complete": False,
    }
    return text, metadata
