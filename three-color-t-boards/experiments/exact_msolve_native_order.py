#!/usr/bin/env python3
"""Apply the audited monomial-graph variable permutation to a complete model."""

import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
MAP = HERE / "exact_f3_order_selected.json"
MAP_SHA256 = "387d85417ffb7823ceef2984b506b39f6913169491d7ada2d75343ec1829bc3e"
BASE_SHA256 = "44e74446e0971a06a40d89fc18446d33e3355d3ef6e42b4197e3ac0686defee5"
ORDERED_SHA256 = "b73bf1f74eb55a2f7e5d2663471021bc8fa3e3250f208d955d8d97bdfa9190bd"


def reorder(source, metadata):
    if (
        metadata.get("prime") != 3
        or metadata.get("variables") != 96
        or metadata.get("native_translation") is not True
        or metadata.get("native_e3") is not True
        or metadata.get("offset_variable_index") != 95
        or metadata.get("count_divisor") != 1
        or metadata.get("count_multiplier") != 1
        or metadata.get("prefix") != ""
        or hashlib.sha256(source.encode()).hexdigest() != BASE_SHA256
    ):
        raise ValueError(
            "minimum-fill ordering requires the audited translated F3/e3 input"
        )
    raw = MAP.read_bytes()
    if hashlib.sha256(raw).hexdigest() != MAP_SHA256:
        raise ValueError("variable map changed; independent review required")
    data = json.loads(raw)
    forward = data["old_index_to_new_index"]
    inverse = data["new_index_to_old_index"]
    if (
        sorted(forward) != list(range(96))
        or sorted(inverse) != list(range(96))
        or forward[95] != 95
        or inverse[95] != 95
        or any(inverse[forward[i]] != i for i in range(96))
        or data["source_sha256"] != BASE_SHA256
        or data["renamed_sha256"] != ORDERED_SHA256
    ):
        raise ValueError("invalid variable bijection or model provenance")
    header, prime, body = source.split("\n", 2)
    pattern = re.compile(r"\bx([1-9][0-9]*)\b")

    def rename(text, mapping):
        def replacement(match):
            old = int(match.group(1)) - 1
            if old >= 96:
                raise ValueError("variable outside permutation")
            return f"x{mapping[old] + 1}"

        return pattern.sub(replacement, text)

    changed_body = rename(body, forward)
    result = header + "\n" + prime + "\n" + changed_body
    if (
        rename(changed_body, inverse) != body
        or hashlib.sha256(result.encode()).hexdigest() != ORDERED_SHA256
        or result != (HERE / "exact_f3_order_selected.ms").read_text()
    ):
        raise ValueError("variable renaming failed the exact roundtrip")

    def remap(forms):
        return {
            cell: {
                str(forward[int(index)]): coefficient
                for index, coefficient in form.items()
            }
            for cell, form in forms.items()
        }

    original_forms = remap(metadata["original_color_linear_forms"])
    if original_forms != data["original_color_linear_forms_in_new_variables"]:
        raise ValueError("reordered original-color reconstruction mismatch")
    updated = dict(metadata)
    updated.update(
        native_variable_order="minimum-fill",
        variable_order_source=str(MAP),
        variable_order_source_sha256=MAP_SHA256,
        variable_order_adapter_sha256=hashlib.sha256(
            Path(__file__).read_bytes()
        ).hexdigest(),
        old_index_to_new_index=forward,
        new_index_to_old_index=inverse,
        original_color_linear_forms=original_forms,
        normalized_color_linear_forms=remap(metadata["normalized_color_linear_forms"]),
        free_normalized_prefix_variables=[
            metadata["free_normalized_prefix_variables"][old] for old in inverse[:95]
        ],
        equation_labels=[
            f"field:{forward[int(label.split(':')[1])]}"
            if label.startswith("field:")
            else label
            for label in metadata["equation_labels"]
        ],
        pre_order_input_sha256=BASE_SHA256,
        input_sha256=ORDERED_SHA256,
        variable_order_scope="bijective renaming only; no count or decomposition claim",
    )
    return result, updated
