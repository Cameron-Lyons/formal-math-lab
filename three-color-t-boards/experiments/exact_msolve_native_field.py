#!/usr/bin/env python3
"""Export the exact natural-F3 palette model with independent field domains."""

import hashlib
import json
from pathlib import Path

SOURCE = Path(__file__).resolve().parent / "exact_f3_math_model.json"
SOURCE_SHA256 = "fe1321842be3bf5bdb8ff91cd5b9c38017d542968fe27a8d5a8952e344564cc4"
INPUT_SHA256 = "e9e1163bd047fdca4000333d917a26e37dbf711abebca29d27fae6d49a2c34ba"


def native_definitions():
    raw = SOURCE.read_bytes()
    if hashlib.sha256(raw).hexdigest() != SOURCE_SHA256:
        raise ValueError("natural-F3 source changed; independent audit required")
    data = json.loads(raw)
    if (
        data["variables"] != 96
        or data["coefficient_characteristic"] != 3
        or data["coefficient_field"] != "F3"
        or data["color_values"] != [0, 1, 2]
        or data["extension_variable"]
        or data["prefix"]
        or data["fixed_original_cells"]
        or data["symmetry_normalization"]
        or data["count_divisor"] != 1
        or data["count_multiplier"] != 1
        or len(data["domain_equations"]) != 96
        or len(data["moment_equations"]) != 76
        or data["pivot_domain_equations"] != 0
    ):
        raise ValueError("invalid natural-F3 model scope")
    equations = data["domain_equations"] + data["moment_equations"]
    polynomials = []
    for equation in equations:
        pieces, seen = [], set()
        for coefficient, encoded in equation["terms"]:
            word = int(encoded, 16)
            if (
                coefficient not in (1, 2)
                or word < 0
                or word >> (4 * 96)
                or word in seen
            ):
                raise ValueError("invalid natural-F3 coefficient or exponent encoding")
            seen.add(word)
            powers = [(word >> (4 * i)) & 15 for i in range(96)]
            if any(e > 3 for e in powers):
                raise ValueError("unexpected natural-F3 exponent")
            factors = [
                f"x{i + 1}" + (f"^{e}" if e != 1 else "")
                for i, e in enumerate(powers)
                if e
            ]
            pieces.append(
                (str(coefficient) + "*" if coefficient != 1 and factors else "")
                + ("*".join(factors) if factors else str(coefficient))
            )
        if not pieces:
            raise ValueError("unexpected zero retained equation")
        polynomials.append("+".join(pieces))
    text = (
        ",".join(f"x{i + 1}" for i in range(96))
        + "\n3\n"
        + ",\n".join(polynomials)
        + "\n"
    )
    digest = hashlib.sha256(text.encode()).hexdigest()
    if digest != INPUT_SHA256:
        raise ValueError("natural-F3 serialization differs from the frozen input")
    metadata = {
        "model": "ternary-native-field-f3",
        "mode": "all-80-power-moments",
        "variables": 96,
        "prime": 3,
        "field": "F3",
        "ring_type": "ordinary polynomial ring",
        "color_values": [0, 1, 2],
        "scope": "full labeled ternary boards",
        "count_scope": "full labeled boards",
        "count_divisor": 1,
        "count_multiplier": 1,
        "prefix": "",
        "fixed_prefix_rows": 0,
        "fixed_cell_count": 0,
        "fixed_original_cells": [],
        "symmetry_normalization": False,
        "extension_variable": False,
        "ternary_native_field": True,
        "generators": 172,
        "field_domain_equations": 96,
        "substituted_pivot_domain_equations": 0,
        "moment_equations": 80,
        "retained_moment_equations": 76,
        "eliminated_linear_moments": 4,
        "retained_unary_quadratic_moments": 4,
        "original_cell_order": data["original_cell_order"],
        "free_prefix_variables": data["free_prefix_variables"],
        "eliminated_prefix_variables": data["eliminated_prefix_variables"],
        "prefix_variable_substitutions": data["prefix_variable_substitutions"],
        "original_color_linear_forms": data["original_color_linear_forms"],
        "equation_labels": [e["label"] for e in equations],
        "source": str(SOURCE),
        "source_sha256": SOURCE_SHA256,
        "native_field_source_sha256": SOURCE_SHA256,
        "source_format": data["format"],
        "native_field_exporter_sha256": hashlib.sha256(
            Path(__file__).read_bytes()
        ).hexdigest(),
        "input_sha256": digest,
        "status": "PREPARED_NOT_RUN",
        "standard_basis_complete": False,
    }
    return text, metadata
