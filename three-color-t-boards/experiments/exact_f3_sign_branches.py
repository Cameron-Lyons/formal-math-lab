#!/usr/bin/env python3
"""Freeze four disjoint linear sign branches; no solver invocation."""

import argparse
import hashlib
import json
import re
from collections import Counter
from itertools import product
from pathlib import Path

import exact_f3_math as native
import exact_f3_order as ordering

HERE = Path(__file__).resolve().parent
SOURCE_SHA = "44e74446e0971a06a40d89fc18446d33e3355d3ef6e42b4197e3ac0686defee5"
MINFILL_SHA = "b73bf1f74eb55a2f7e5d2663471021bc8fa3e3250f208d955d8d97bdfa9190bd"
MODEL_SHA = "1e2dc884f8996c6bd1b5093f24fa6fe7d7f1002e97b69762baadfda5adf94a7f"
ORDER_SHA = "387d85417ffb7823ceef2984b506b39f6913169491d7ada2d75343ec1829bc3e"
SIX_PREFIX = (
    "100011101011000101010011112112211212021201221022121202020220010222002102100022222"
)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def dump(obj):
    return json.dumps(obj, indent=2) + "\n"


def encoded(poly, label):
    return native.polynomial_record(label, poly)


def remap(poly, mapping):
    return {ordering.remap_word(t, mapping): c for t, c in poly.items()}


def parse97(text):
    head, prime, body = text.split("\n", 2)
    assert head == ",".join(f"x{i + 1}" for i in range(97)) and prime == "3"
    polynomials = []
    for expression in body.strip().split(",\n"):
        p = {}
        for term in expression.split("+"):
            coefficient = 1
            word = 0
            for factor in term.split("*"):
                if factor in ("1", "2"):
                    coefficient = coefficient * int(factor) % 3
                else:
                    match = re.fullmatch(r"x([1-9][0-9]*)(?:\^([1-9][0-9]*))?", factor)
                    assert match, factor
                    v = int(match[1]) - 1
                    e = int(match[2] or "1")
                    assert 0 <= v < 97 and 0 < e < 16 and not (word >> (4 * v) & 15)
                    word += e << (4 * v)
            native.add_into(p, {word: coefficient})
        polynomials.append(p)
    return polynomials


def append_equations(source, extras):
    _, prime, body = source.split("\n", 2)
    assert prime == "3"
    text = (
        ",".join(f"x{i + 1}" for i in range(97))
        + "\n3\n"
        + body.rstrip("\n")
        + ",\n"
        + ",\n".join(native.expression(p) for p in extras)
        + "\n"
    )
    assert text.split("\n", 2)[2].startswith(body.rstrip("\n") + ",\n")
    assert text.split("\n", 2)[2].split(",\n")[:176] == body.rstrip("\n").split(",\n")
    return text


def delta(z, windows):
    return [(z[a] - z[b]) % 3 for a, b in zip(windows[0], windows[3], strict=False)]


def first_nonzero(values):
    return next(i for i, x in enumerate(values) if x)


def reflection(z):
    return [z[r * r + j] for r in range(10) for j in reversed(range(2 * r + 1))]


def build():
    source_raw = (HERE / "exact_f3_translation_e3.ms").read_bytes()
    minfill_raw = (HERE / "exact_f3_order_selected.ms").read_bytes()
    model_raw = (HERE / "exact_f3_translation_model.json").read_bytes()
    order_raw = (HERE / "exact_f3_order_selected.json").read_bytes()
    assert (sha(source_raw), sha(minfill_raw), sha(model_raw), sha(order_raw)) == (
        SOURCE_SHA,
        MINFILL_SHA,
        MODEL_SHA,
        ORDER_SHA,
    )
    source = source_raw.decode()
    minfill_source = minfill_raw.decode()
    model = json.loads(model_raw)
    order = json.loads(order_raw)
    mapping = order["old_index_to_new_index"] + [96]
    inverse = order["new_index_to_old_index"] + [96]
    assert sorted(mapping) == sorted(inverse) == list(range(97))
    assert all(inverse[mapping[i]] == i for i in range(97))
    assert mapping[95:] == inverse[95:] == [95, 96]
    base = ordering.parse_polynomials(source)
    base_minfill = ordering.parse_polynomials(minfill_source)
    assert len(base) == len(base_minfill) == 176
    assert [remap(p, mapping) for p in base] == base_minfill
    assert all(base[i] == {3 << (4 * i): 1, 1 << (4 * i): 2} for i in range(96))
    assert all(not t >> (4 * 95) for p in base[96:] for t in p)
    assert all(
        len({sum(e for _, e in native.unpack(t)) % 2 for t in p}) == 1
        for p in base[96:]
    )
    windows, _, _ = native.geometry()
    assert windows[0] == (0, 1, 2, 3) and windows[3] == (3, 6, 7, 8)
    forms = {
        int(c): {int(v): a for v, a in f.items()}
        for c, f in model["normalized_color_linear_forms"].items()
    }
    differences = []
    for a, b in zip(windows[0], windows[3], strict=False):
        p = forms[a].copy()
        native.add_into(p, forms[b], -1)
        differences.append(p)
    assert differences == [
        {0: 2},
        {70: 2, 71: 1, 15: 2, 93: 1},
        {7: 2, 8: 2, 9: 2},
        {0: 2, 1: 2},
    ]
    packed = [{1 << (4 * v): c for v, c in p.items()} for p in differences]
    rows = [[p.get(v, 0) for v in range(95)] for p in differences]
    linear_ranks = [native.field_rank(rows[: k + 1]) for k in range(4)]
    augmented_ranks = [
        native.field_rank([[*r, int(i == k)] for i, r in enumerate(rows[: k + 1])])
        for k in range(4)
    ]
    assert linear_ranks == augmented_ranks == [1, 2, 3, 4]
    sign_field = {3 << (4 * 96): 1, 1 << (4 * 96): 2}
    sign_square = {2 << (4 * 96): 1, 0: 2}
    assert {t + (1 << (4 * 96)): c for t, c in sign_square.items()} == sign_field
    actual = {
        str(cell): {
            1 << (4 * 95): 1,
            **{(1 << (4 * v)) + (1 << (4 * 96)): c for v, c in f.items()},
        }
        for cell, f in forms.items()
    }
    assert actual["0"] == {1 << (4 * 95): 1}
    actual_records = {c: encoded(p, "original-color:" + c) for c, p in actual.items()}
    renamed_actual_records = {
        c: encoded(remap(p, mapping), "original-color:" + c) for c, p in actual.items()
    }
    files = {}
    branch_polynomials = []
    branch_extras = []
    branches = []
    for k in range(4):
        constraints = [p.copy() for p in packed[: k + 1]]
        native.add_into(constraints[k], {0: 2})
        extras = [sign_field, sign_square, *constraints]
        branch_extras.append(extras)
        branch_polynomials.append(base + extras)
        assert len(base + extras) == 179 + k
        natural = append_equations(source, extras)
        renamed = append_equations(minfill_source, [remap(p, mapping) for p in extras])
        natural_parsed = parse97(natural)
        renamed_parsed = parse97(renamed)
        assert natural_parsed == base + extras
        assert renamed_parsed == [remap(p, mapping) for p in natural_parsed]
        assert [remap(p, inverse) for p in renamed_parsed] == natural_parsed
        assert all(
            {3 << (4 * v): 1, 1 << (4 * v): 2} in natural_parsed for v in range(97)
        )
        assert all(not t >> (4 * 95) for p in constraints for t in p)
        labels = ["sign-field", "sign-square"] + [
            f"delta:{i}:target:{int(i == k)}" for i in range(k + 1)
        ]
        common = {
            "format": "t-board-natural-f3-linear-sign-branch-v1",
            "branch_id": k,
            "coefficient_characteristic": 3,
            "coefficient_field": "F3",
            "ring_type": "ordinary polynomial ring",
            "variables": 97,
            "coupled_variables": 95,
            "generators": 179 + k,
            "scope": f"full labeled valid ternary boards whose first nonzero selected pattern difference is role {k}",
            "independent_offset_index": 95,
            "independent_sign_index": 96,
            "independent_factors": "F3[a]/(a^3-a) tensor F3[s]/(s^2-1); sign field cubic also retained",
            "count_divisor": 1,
            "count_multiplier": 1,
            "branch_count_status": "UNEVALUATED; no solver",
            "full_count_rule": "N=sum(branch_dimension[k] for k in 0,1,2,3), exactly once per branch",
            "prefix": "",
            "fixed_original_cells": [],
            "placement_indices": [0, 3],
            "placement_cells": [list(windows[0]), list(windows[3])],
            "role_order": ["T", "L", "M", "R"],
            "branch_original_condition": f"Delta_i(z)=0 for i<{k}, Delta_{k}(z)!=0",
            "branch_canonical_condition": f"Delta_i(d)=0 for i<{k}, Delta_{k}(d)=1",
            "inverse_reconstruction": f"a=z_apex; D=z-a; s=Delta_{k}(D); d=s*D; take Gray prefixes of d",
            "original_color_reconstruction": "z_cell=a+s*d_cell (bilinear)",
            "original_prefix_reconstruction": "Y_j=s*u_j+(j+1)*a modulo 3",
            "source_native_translation_model_sha256": MODEL_SHA,
            "source_natural_input_sha256": SOURCE_SHA,
            "source_minfill_input_sha256": MINFILL_SHA,
            "source_order_metadata_sha256": ORDER_SHA,
            "original_cell_order": model["original_cell_order"],
            "free_canonical_prefix_indices": model["free_normalized_prefix_variables"],
            "constraint_coefficient_rank": linear_ranks[k],
            "constraint_augmented_rank": augmented_ranks[k],
            "source_generator_count": 176,
            "source_generator_body_retained_byte_for_byte": True,
            "individual_field_domain_count": 97,
            "extra_sign_square_count": 1,
            "extra_branch_linear_constraint_count": k + 1,
            "quintic_selector_included": False,
            "monomial_encoding": "[coefficient,hex integer]; exponent of variable i occupies bits4i..4i+3",
            "exact_total_claimed": False,
        }
        stem = f"exact_f3_sign_branch{k}"
        natural_name = stem + "_natural.ms"
        minfill_name = stem + "_minfill.ms"
        natural_meta = dict(
            common,
            variable_order="original translated order then sign",
            normalized_color_linear_forms=model["normalized_color_linear_forms"],
            original_color_bilinear_polynomials=actual_records,
            additional_equations=[
                encoded(p, label) for p, label in zip(extras, labels, strict=False)
            ],
            branch_delta_linear_forms=differences,
            input_file=natural_name,
            input_sha256=sha(natural.encode()),
        )
        minfill_meta = dict(
            common,
            variable_order="frozen minfill order then sign",
            old_index_to_new_index=mapping,
            new_index_to_old_index=inverse,
            normalized_color_linear_forms={
                str(c): {str(mapping[v]): a for v, a in f.items()}
                for c, f in forms.items()
            },
            original_color_bilinear_polynomials=renamed_actual_records,
            additional_equations=[
                encoded(remap(p, mapping), label)
                for p, label in zip(extras, labels, strict=False)
            ],
            branch_delta_linear_forms=[
                {mapping[v]: c for v, c in p.items()} for p in differences
            ],
            input_file=minfill_name,
            input_sha256=sha(renamed.encode()),
        )
        files[natural_name] = natural
        files[minfill_name] = renamed
        files[stem + "_natural.json"] = dump(natural_meta)
        files[stem + "_minfill.json"] = dump(minfill_meta)
        branches.append(
            {
                "branch_id": k,
                "role": ("T", "L", "M", "R")[k],
                "generators": 179 + k,
                "linear_constraint_rank": linear_ranks[k],
                "extra_branch_constraint_terms": sum(map(len, constraints)),
                "natural_input": natural_name,
                "natural_sha256": sha(natural.encode()),
                "minfill_input": minfill_name,
                "minfill_sha256": sha(renamed.encode()),
                "count_status": "UNEVALUATED",
            }
        )

    # Entire nonzero difference space has one and only one branch/canonical pair.
    difference_counts = Counter()
    canonical_counts = Counter()
    for diff in product(range(3), repeat=4):
        if not any(diff):
            continue
        k = first_nonzero(diff)
        s = diff[k]
        canonical = tuple(s * x % 3 for x in diff)
        assert s in (1, 2) and all(x == 0 for x in canonical[:k]) and canonical[k] == 1
        assert tuple(s * x % 3 for x in canonical) == diff
        difference_counts[k] += 1
    for k in range(4):
        canonical_counts[k] = sum(
            all(x == 0 for x in diff[:k]) and diff[k] == 1
            for diff in product(range(3), repeat=4)
        )
    assert [difference_counts[k] for k in range(4)] == [54, 18, 6, 2]
    assert [canonical_counts[k] for k in range(4)] == [27, 9, 3, 1]

    fixtures = json.loads(
        (HERE / "exact_structure_gauge_certificate.json").read_text()
    )["boards"]
    witness_counts = Counter()
    reflection_transitions = Counter()
    reflection_certificates = {}
    full_checks = 0
    for entry_index, entry in enumerate(fixtures):
        z = list(map(int, entry["flat"]))
        assert len({tuple(z[c] for c in w) for w in windows}) == 81
        original_diff = delta(z, windows)
        k = first_nonzero(original_diff)
        a = z[0]
        s = original_diff[k]
        D = [(x - a) % 3 for x in z]
        d = [s * x % 3 for x in D]
        prefix = []
        acc = 0
        for cell in model["original_cell_order"]:
            acc = (acc + d[cell]) % 3
            prefix.append(acc)
        point = [prefix[i] for i in model["free_normalized_prefix_variables"]] + [a, s]
        assert all(native.evaluate(p, point) == 0 for p in branch_extras[k])
        assert all(native.evaluate(p, point) == z[int(c)] for c, p in actual.items())
        # Check the full input on five fixtures; all remaining roundtrips check
        # geometry, new equations and reconstruction, with homogeneous parity
        # and the already frozen source establishing affine invariance.
        if entry_index < 5:
            assert all(native.evaluate(p, point) == 0 for p in branch_polynomials[k])
            full_checks += 1
        for other in range(4):
            if other != k:
                assert any(
                    native.evaluate(p, point) != 0 for p in branch_extras[other][2:]
                )
        witness_counts[k] += 1
        for aa, ss in product(range(3), (1, 2)):
            board = [(aa + ss * x) % 3 for x in d]
            assert (
                first_nonzero(delta(board, windows)) == k
                and delta(board, windows)[k] == ss
            )
            q = [*point[:95], aa, ss]
            assert all(
                native.evaluate(p, q) == 0 for p in [base[95]] + branch_extras[k]
            )
            assert all(
                native.evaluate(p, q) == board[int(c)] for c, p in actual.items()
            )
        rz = reflection(z)
        j = first_nonzero(delta(rz, windows))
        assert len({tuple(rz[c] for c in w) for w in windows}) == 81
        reflection_transitions[k, j] += 1
        reflection_certificates.setdefault(
            (k, j),
            {
                "certificate_board_index": entry_index,
                "original_board": entry["flat"],
                "reflected_board": "".join(map(str, rz)),
                "original_delta": original_diff,
                "reflected_delta": delta(rz, windows),
            },
        )
    assert set(reflection_transitions) >= {(0, 0), (0, 1), (1, 0), (1, 1)}
    prefix = list(map(int, SIX_PREFIX))
    prefix_diff = delta(prefix, windows)
    assert prefix_diff == [1, 2, 0, 2] and first_nonzero(prefix_diff) == 0
    prefix_case = {
        "prefix": SIX_PREFIX,
        "original_apex": 1,
        "selected_difference": prefix_diff,
        "branch_id": 0,
        "forced_offset": 1,
        "forced_sign": 1,
        "expected_fixed_prefix_dimensions_by_branch": ["6", "0", "0", "0"],
        "prediction_provenance": "known six-completion prefix, plus direct first-nonzero classification; no branch solver run",
    }
    manifest = {
        "format": "t-board-four-linear-sign-branches-v1",
        "status": "EXPORTED_UNEVALUATED",
        "coefficient_characteristic": 3,
        "variables_per_branch": 97,
        "scope": "partition of every full labeled valid ternary board by first nonzero coordinate of P0-P3",
        "required_branch_ids": [0, 1, 2, 3],
        "branches": branches,
        "count_rule": "N=N0+N1+N2+N3, with one certified quotient dimension for each branch",
        "count_multiplier": 1,
        "count_divisor": 1,
        "completion_rule": "Do not report N until all four branch dimensions are certified for these exact complete inputs. Natural/minfill inputs are two representations of the same branch and must not both be added. Missing, partial or timed-out branches remain unknown, not zero.",
        "known_six_prefix_prediction": prefix_case,
        "no_count_proportionality_claim": "Difference-space sizes54,18,6,2 are not board-count ratios.",
        "full_count_status": "UNEVALUATED; no solver",
    }
    files["exact_f3_sign_branches_manifest.json"] = dump(manifest)
    audit = {
        "status": "PASS",
        "scope": "finite partition, exact branch exports, algebraic factorization and fixture roundtrips; no solver",
        "source176_generators_byte_preserved_in_all8_inputs": True,
        "all97_individual_field_domains_in_all8_inputs": True,
        "all_natural_minfill_polynomials_parsed_and_inverse_permuted": True,
        "independent_offset_and_sign_absent_from_coupled_equations": True,
        "source_coupled_polynomial_degree_parities_uniform": True,
        "sign_field_redundancy_ordinary_identity_checked": True,
        "coefficient_ranks": linear_ranks,
        "augmented_ranks": augmented_ranks,
        "delta_linear_expressions": [native.expression(p) for p in packed],
        "all80_nonzero_difference_inputs_partitioned": True,
        "difference_input_counts_by_branch": [difference_counts[k] for k in range(4)],
        "canonical_difference_input_counts_by_branch": [
            canonical_counts[k] for k in range(4)
        ],
        "existing_valid_boards_roundtripped": len(fixtures),
        "full_input_polynomial_fixture_checks": full_checks,
        "existing_witness_branch_counts": [witness_counts[k] for k in range(4)],
        "all6_affine_palettes_preserve_branch_on_every_fixture": True,
        "reflection_branch_transitions": [
            {"from": k, "to": j, "count": n}
            for (k, j), n in sorted(reflection_transitions.items())
        ],
        "reflection_nonuniformity_certificates": [
            dict(from_branch=k, to_branch=j, **entry)
            for (k, j), entry in sorted(reflection_certificates.items())
        ],
        "symmetry_reuse_scope": "Global palettes preserve each branch. Reflection does not uniformly map branch0 or branch1 to a single branch, as witnessed here. No branch-count equality or impossibility is asserted.",
        "known_six_prefix_prediction": prefix_case,
        "export_sha256": {name: sha(text.encode()) for name, text in files.items()},
        "generator_sha256": sha(Path(__file__).read_bytes()),
        "full_count_status": "UNEVALUATED",
    }
    files["exact_f3_sign_branches_audit.json"] = dump(audit)
    return files, audit


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    files, audit = build()
    for name, text in files.items():
        path = HERE / name
        if args.check:
            assert path.read_text() == text, name
        else:
            path.write_text(text)
    print(
        dump(
            {
                k: audit[k]
                for k in (
                    "status",
                    "coefficient_ranks",
                    "existing_witness_branch_counts",
                    "known_six_prefix_prediction",
                    "export_sha256",
                )
            }
        )
    )


if __name__ == "__main__":
    main()
