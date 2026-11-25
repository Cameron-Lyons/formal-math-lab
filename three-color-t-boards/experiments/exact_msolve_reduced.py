#!/usr/bin/env python3
"""Export the independently verified reduced F2 Fourier ideal to msolve.

The ring is ordinary: all 96 free variables retain x_i^3+1. The four
substituted pivot domains are also retained. Optional Frobenius partners
square only the 36 retained moments, reducing exponents modulo these cubes.
No solver process or count is produced by this module.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent
SOURCE = ROOT / "exact_parity_math_fourier_reduced.json"
VERIFIED_SOURCE_SHA256 = (
    "66e18148d574178bfdc09296635e43ebe327646beff90ab8c5a6d43e88729c78"
)
VARIABLES = 96
PIVOTS = (0, 81, 90, 99)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, "duplicate JSON key: " + key)
        result[key] = value
    return result


def validate_word(word, variables=VARIABLES):
    require(type(variables) is int and variables >= 0, "invalid variable count")
    require(
        type(word) is int and word >= 0, "packed monomial must be nonnegative integer"
    )
    require(word >> (2 * variables) == 0, "packed monomial exceeds variable count")
    require(
        all((word >> (2 * i) & 3) != 3 for i in range(variables)),
        "packed monomial contains forbidden exponent 3",
    )
    return word


def decode_monomial(encoded, variables=VARIABLES):
    require(
        isinstance(encoded, str)
        and re.fullmatch(r"0x[0-9a-fA-F]+", encoded) is not None,
        "monomial must be an unsigned hexadecimal string",
    )
    return validate_word(int(encoded, 16), variables)


def decode_polynomial(terms, variables=VARIABLES):
    require(
        isinstance(terms, list) and bool(terms),
        "polynomial terms must be a nonempty list",
    )
    decoded = [decode_monomial(term, variables) for term in terms]
    require(
        len(decoded) == len(set(decoded)), "duplicate packed monomial in polynomial"
    )
    return tuple(decoded)


def frobenius_word(word, variables=VARIABLES):
    word = validate_word(word, variables)
    return sum(((2 * (word >> (2 * i) & 3)) % 3) << (2 * i) for i in range(variables))


def monomial_text(word):
    factors = []
    for i in range(VARIABLES):
        exponent = word >> (2 * i) & 3
        if exponent:
            factors.append(f"x{i + 1}" + ("^2" if exponent == 2 else ""))
    return "*".join(factors) or "1"


def validate_document(data):
    require(
        isinstance(data, dict) and data.get("format") == "t-board-fourier-reduced-v1",
        "wrong reduced Fourier format",
    )
    require(
        type(data.get("variables")) is int
        and data["variables"] == VARIABLES
        and data.get("coefficient_field") == "F2",
        "wrong variable count or coefficient field",
    )
    free = [cell for cell in range(100) if cell not in PIVOTS]
    require(
        data.get("free_original_cells") == free
        and all(type(cell) is int for cell in data["free_original_cells"]),
        "wrong free-cell map",
    )
    require(
        data.get("free_domain_equations") == "z_i^3+1 for all 96 free variables",
        "missing ordinary free cubic domains",
    )
    substitutions = data.get("pivot_substitutions")
    require(
        isinstance(substitutions, dict)
        and set(substitutions) == {str(p) for p in PIVOTS},
        "wrong pivot substitution set",
    )
    for terms in substitutions.values():
        require(
            isinstance(terms, list)
            and terms
            and all(type(cell) is int and cell in free for cell in terms),
            "pivot substitution uses a non-free cell",
        )
        require(len(terms) == len(set(terms)), "duplicate term in pivot substitution")
    expected_moments = {
        "moment:" + ",".join(map(str, exponents))
        for exponents in itertools.product(range(3), repeat=4)
        if next((e for e in exponents if e), 0) == 1 and sum(exponents) > 1
    }
    expected_labels = expected_moments | {f"pivot_domain:{p}" for p in PIVOTS}
    equations = data.get("remaining_equations")
    require(
        isinstance(equations, list) and len(equations) == 40,
        "expected 36 moments and 4 pivot domains",
    )
    decoded = []
    seen = set()
    for equation in equations:
        require(
            isinstance(equation, dict) and set(equation) == {"label", "terms"},
            "invalid equation record",
        )
        label = equation["label"]
        require(
            isinstance(label, str) and label in expected_labels and label not in seen,
            "unknown or duplicate equation label",
        )
        seen.add(label)
        decoded.append((label, decode_polynomial(equation["terms"])))
    require(seen == expected_labels, "missing retained moment or pivot-domain equation")
    require(
        sum(len(terms) for _, terms in decoded) == 25070,
        "unexpected retained polynomial term count",
    )
    require(
        sum(len(terms) for label, terms in decoded if label.startswith("moment:"))
        == 11884,
        "unexpected retained moment term count",
    )
    return free, decoded


def reduced_definitions(all_moments=False):
    """Return (msolve text, metadata), with no prefix or symmetry restriction."""
    require(type(all_moments) is bool, "all_moments must be Boolean")
    raw = SOURCE.read_bytes()
    source_hash = hashlib.sha256(raw).hexdigest()
    require(
        source_hash == VERIFIED_SOURCE_SHA256,
        "reduced source differs from independently verified JSON; review it before use",
    )
    data = json.loads(raw, object_pairs_hook=unique_object)
    free, decoded = validate_document(data)
    equations = list(decoded)
    if all_moments:
        for label, terms in decoded:
            if label.startswith("moment:"):
                exponents = tuple(map(int, label.split(":", 1)[1].split(",")))
                partner_label = "moment:" + ",".join(str(2 * e % 3) for e in exponents)
                partner = tuple(sorted(frobenius_word(word) for word in terms))
                require(
                    len(partner) == len(set(partner)),
                    "Frobenius transform lost injectivity",
                )
                equations.append((partner_label, partner))
    require(
        len({label for label, _ in equations}) == len(equations),
        "duplicate exported equation label",
    )
    polynomials = [f"x{i + 1}^3+1" for i in range(VARIABLES)]
    polynomials += [
        "+".join(monomial_text(word) for word in terms) for _, terms in equations
    ]
    expected_generators, expected_terms = (172, 36954) if all_moments else (136, 25070)
    require(
        len(polynomials) == expected_generators
        and sum(len(terms) for _, terms in equations) == expected_terms,
        "incorrect export dimensions",
    )
    text = (
        ",".join(f"x{i + 1}" for i in range(VARIABLES))
        + "\n2\n"
        + ",\n".join(polynomials)
        + "\n"
    )
    metadata = {
        "model": "ternary-reduced-f2-all" if all_moments else "ternary-reduced-f2",
        "mode": "all-80-moments" if all_moments else "paired-40-moments",
        "source": str(SOURCE.resolve()),
        "source_sha256": source_hash,
        "reduced_source_sha256": source_hash,
        "generator_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "source_format": data["format"],
        "variables": VARIABLES,
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
        "free_original_cells": free,
        "eliminated_original_cells": list(PIVOTS),
        "free_board_variables": VARIABLES,
        "extension_variable": False,
        "generators": len(polynomials),
        "free_domain_equations": 96,
        "substituted_pivot_domain_equations": 4,
        "moment_equations": 80 if all_moments else 40,
        "retained_moment_equations": 72 if all_moments else 36,
        "eliminated_linear_moments": 4,
        "eliminated_unary_moments": 8 if all_moments else 4,
        "frobenius_partners_added": 36 if all_moments else 0,
        "terms_outside_free_domains": expected_terms,
        "equation_labels": [label for label, _ in equations],
        "input_sha256": hashlib.sha256(text.encode()).hexdigest(),
        "standard_basis_complete": False,
        "status": "PREPARED_NOT_RUN",
    }
    return text, metadata


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--all-moments", action="store_true")
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    text, metadata = reduced_definitions(args.all_moments)
    args.output.write_text(text)
    args.output.with_suffix(".json").write_text(json.dumps(metadata, indent=2) + "\n")
    print(
        json.dumps(
            {
                key: metadata[key]
                for key in (
                    "mode",
                    "variables",
                    "generators",
                    "terms_outside_free_domains",
                    "count_divisor",
                    "input_sha256",
                    "status",
                )
            },
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
