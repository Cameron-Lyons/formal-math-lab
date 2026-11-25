#!/usr/bin/env python3
"""Export the frozen ordinary-F2 prefix-coordinate counting ideal.

No solver is invoked. Free prefix coordinates may be zero; their defining
domains are transformed original color cubics, not individual cubics.
"""

import hashlib
import json
from pathlib import Path

SOURCE = (
    Path(__file__).resolve().parent
    / "exact_msolve_elementary_analysis_prefix_gray_model.json"
)
SOURCE_SHA256 = "7f8251ab52e8d6869c19cc861dc98b0c1e66904313b0d87920d9f95659700092"


def prefix_definitions(all_moments=False, histogram_e2=False, field_equations=False):
    if any(
        type(flag) is not bool for flag in (all_moments, histogram_e2, field_equations)
    ):
        raise ValueError("prefix-coordinate options must be booleans")
    raw = SOURCE.read_bytes()
    if hashlib.sha256(raw).hexdigest() != SOURCE_SHA256:
        raise ValueError("prefix-coordinate model changed; independent audit required")
    model = json.loads(raw)
    if (
        model["format"] != "t-board-prefix-sum-f2-v1"
        or model["variables"] != 96
        or model["coefficient_characteristic"] != 2
        or model["count_divisor"] != 1
        or model["count_multiplier"] != 1
        or model["symmetry_normalization"] is not False
        or len(model["domain_equations"]) != 100
        or len(model["moment_equations"]) != 72
        or len(model["elementary_equations"]) != 8
        or len(model["prefix_field_equations"]) != 96
    ):
        raise ValueError("invalid prefix-coordinate model scope")
    moments = []
    for eq in model["moment_equations"]:
        exponents = list(map(int, eq["label"].split(":")[1].split(",")))
        if (
            len(exponents) != 4
            or any(e not in (0, 1, 2) for e in exponents)
            or not any(exponents)
        ):
            raise ValueError("invalid Fourier exponent label")
        if all_moments or next(e for e in exponents if e) == 1:
            moments.append(eq)
    if len(moments) != (72 if all_moments else 36):
        raise ValueError("invalid Fourier representative count")
    equations = model["domain_equations"] + moments
    if histogram_e2:
        equations += model["elementary_equations"]
    if field_equations:
        equations += model["prefix_field_equations"]
    polys = []
    for eq in equations:
        terms = [int(s, 16) for s in eq["terms"]]
        if not terms or len(set(terms)) != len(terms):
            raise ValueError("empty or duplicate transformed terms")
        pieces = []
        for term in terms:
            if term < 0 or term >> (4 * 96):
                raise ValueError("monomial outside transformed ring")
            factors = []
            for i in range(96):
                exponent = (term >> (4 * i)) & 15
                if exponent > 8:
                    raise ValueError("unexpected transformed exponent")
                if exponent:
                    factors.append(
                        f"x{i + 1}" + (f"^{exponent}" if exponent != 1 else "")
                    )
            pieces.append("*".join(factors) or "1")
        polys.append("+".join(pieces))
    text = ",".join(f"x{i + 1}" for i in range(96)) + "\n2\n" + ",\n".join(polys) + "\n"
    metadata = {
        "model": "ternary-prefix-sums-f2-"
        + ("all" if all_moments else "representatives"),
        "mode": "all-80-moments" if all_moments else "40-Frobenius-representatives",
        "variables": 96,
        "prime": 2,
        "field": "F2",
        "ring_type": "ordinary polynomial ring",
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
        "ternary_prefix_sums": True,
        "free_prefix_variables": model["free_prefix_variables"],
        "original_cell_order": model["original_cell_order"],
        "eliminated_prefix_variables": model["eliminated_prefix_variables"],
        "prefix_variable_substitutions": model["prefix_variable_substitutions"],
        "original_color_linear_forms": model["original_color_linear_forms"],
        "transformed_original_cubic_domains": 100,
        "generators": len(equations),
        "moment_equations": 80 if all_moments else 40,
        "retained_moment_equations": len(moments),
        "eliminated_unary_moments": 8 if all_moments else 4,
        "histogram_e2": histogram_e2,
        "elementary_generators": 8 if histogram_e2 else 0,
        "prefix_field_equations": field_equations,
        "prefix_field_equation_count": 96 if field_equations else 0,
        "equation_labels": [eq["label"] for eq in equations],
        "source": str(SOURCE),
        "source_sha256": SOURCE_SHA256,
        "prefix_model_source_sha256": SOURCE_SHA256,
        "source_format": model["format"],
        "generator_sha256": model["generator_source_sha256"],
        "prefix_exporter_sha256": hashlib.sha256(
            Path(__file__).read_bytes()
        ).hexdigest(),
        "input_sha256": hashlib.sha256(text.encode()).hexdigest(),
        "status": "UNEVALUATED_GENERATING_IDEAL",
        "standard_basis_complete": False,
    }
    return text, metadata
