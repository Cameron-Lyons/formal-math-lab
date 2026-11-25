#!/usr/bin/env python3
"""Run a frozen natural-F3 model through the existing Singular backend.

This adapter changes only the model-definition provider in this process;
it does not edit the existing backend or any frozen input. Completed results
also pass a strict normal-exit/marker audit before being accepted here.
"""

import argparse
import hashlib
import json
import re
from pathlib import Path
from unittest.mock import patch

import exact_algebra_backend as backend

HERE = Path(__file__).resolve().parent
INPUTS = {
    "minimum-fill": (
        "exact_f3_order_selected.ms",
        "b73bf1f74eb55a2f7e5d2663471021bc8fa3e3250f208d955d8d97bdfa9190bd",
        176,
    ),
    "six": (
        "exact_f3_translation_six.ms",
        "3781763a4a35be2f5dc3f2e0da2ea0cecca805e84ccf38a07f6913fafa0f5b1c",
        257,
    ),
}


def definition(case):
    filename, expected, count = INPUTS[case]
    path = HERE / filename
    raw = path.read_bytes()
    if hashlib.sha256(raw).hexdigest() != expected:
        raise ValueError("frozen native-F3 input changed")
    header, prime, body = raw.decode("ascii").split("\n", 2)
    if header != ",".join(f"x{i}" for i in range(1, 97)) or prime != "3":
        raise ValueError("unexpected coefficient field or variables")
    polys = body.strip().split(",\n")
    if len(polys) != count or any(not re.fullmatch(r"[0-9x+*^]+", p) for p in polys):
        raise ValueError("unexpected polynomial grammar or generator count")
    text = "ring R=3,(" + header + "),dp;\nideal I=" + body.strip() + ";\n"
    metadata = {
        "model": "native-F3-" + case,
        "field": "F3",
        "prime": 3,
        "variables": 96,
        "generators": count,
        "count_divisor": 1,
        "count_multiplier": 1,
        "count_scope": "full labeled boards"
        if case == "minimum-fill"
        else "known nine-row prefix",
        "fixed_cell_count": 0 if case == "minimum-fill" else 81,
        "native_translation": True,
        "native_e3": True,
        "independent_offset_variable": 95,
        "input_file": str(path),
        "input_sha256": expected,
        "definition_sha256": hashlib.sha256(text.encode()).hexdigest(),
        "native_adapter_sha256": hashlib.sha256(
            Path(__file__).read_bytes()
        ).hexdigest(),
        "backend_sha256": hashlib.sha256(
            Path(backend.__file__).read_bytes()
        ).hexdigest(),
        "executable_sha256": hashlib.sha256(backend.SINGULAR.read_bytes()).hexdigest(),
    }
    return text, metadata


def strict_completion(result, log, case):
    required = [
        "GB_STARTED",
        "GB_COMPLETE",
        "LM_COMPLETE",
        "HILB_STARTED",
        "BACKEND_COMPLETE",
    ]
    lines = log.splitlines()
    if result.get("returncode") != 0 or result.get("wall_timeout_reached"):
        raise ValueError("completion requires a normal child exit")
    if any(lines.count(marker) != 1 for marker in required):
        raise ValueError("missing or duplicate completion marker")
    if [lines.index(marker) for marker in required] != sorted(
        lines.index(marker) for marker in required
    ):
        raise ValueError("completion markers out of order")
    for field in [
        "BASIS_IS_STANDARD",
        "KRULL_DIM",
        "BASIS_SIZE",
        "HILB_TYPE",
        "HILB_DIM",
    ]:
        if sum(line.startswith(field + "=") for line in lines) != 1:
            raise ValueError("missing or duplicate output field: " + field)
    if "BASIS_IS_STANDARD=1" not in lines or "HILB_TYPE=bigintvec" not in lines:
        raise ValueError("missing exact-basis or bigint attestation")
    if not all(
        result.get(k)
        for k in [
            "basis_complete",
            "standard_basis_complete",
            "leading_export_complete",
            "dimension_complete",
        ]
    ):
        raise ValueError("incomplete basis or dimension metadata")
    value = result["quotient_dimension"]
    if any(
        result.get(k) != value
        for k in [
            "monomial_dimension",
            "independent_monomial_dimension",
            "hilbert_dimension",
        ]
    ):
        raise ValueError("three exact counts do not agree")
    if case == "six" and value != 6:
        raise ValueError("known prefix count is not six")
    if case == "minimum-fill" and (value < 45083592 or value % 12):
        raise ValueError(
            "unrestricted count violates the certified lower bound or symmetry"
        )


def run(
    case, output, seconds=180, memory_mb=3072, algorithm="slimgb", prepare_only=False
):
    output = Path(output)
    if any(
        output.with_suffix(suffix).exists()
        for suffix in [".sing", ".json", ".log", ".leading.json"]
    ):
        raise FileExistsError("refusing to overwrite a preserved Singular trial")
    model_definition, metadata = definition(case)

    def supply(model, prefix="", field="F2", normalize_apex=False):
        if (model, prefix, field, normalize_apex) != (
            "frozen-native-F3",
            "",
            "F2",
            False,
        ):
            raise ValueError("unexpected internal backend model request")
        return model_definition, dict(metadata)

    with patch.object(backend, "definitions", supply):
        result = backend.run(
            "frozen-native-F3",
            output,
            timeout=seconds,
            memory_mb=memory_mb,
            algorithm=algorithm,
            prepare_only=prepare_only,
        )
    if result["status"].startswith("COMPLETE"):
        try:
            strict_completion(result, output.with_suffix(".log").read_text(), case)
            result["strict_native_completion_audit"] = "PASS"
        except (KeyError, ValueError) as exc:
            result.update(
                status="NATIVE_COMPLETION_REJECTED",
                dimension_complete=False,
                strict_native_completion_audit=str(exc),
            )
    output.with_suffix(".json").write_text(json.dumps(result, indent=2) + "\n")
    return result


if __name__ == "__main__":
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--case", choices=INPUTS, required=True)
    p.add_argument("--output", type=Path, required=True)
    p.add_argument("--seconds", type=float, default=180)
    p.add_argument("--memory-mb", type=int, default=3072)
    p.add_argument("--algorithm", choices=["std", "slimgb"], default="slimgb")
    p.add_argument("--prepare-only", action="store_true")
    args = p.parse_args()
    result = run(
        args.case,
        args.output,
        args.seconds,
        args.memory_mb,
        args.algorithm,
        args.prepare_only,
    )
    print(
        json.dumps(
            {
                k: result.get(k)
                for k in [
                    "status",
                    "count_scope",
                    "quotient_dimension",
                    "child_cpu_seconds",
                    "elapsed_seconds",
                    "strict_native_completion_audit",
                ]
            },
            indent=2,
        )
    )
    raise SystemExit(0 if result["status"] in ("COMPLETE", "PREPARED_NOT_RUN") else 1)
