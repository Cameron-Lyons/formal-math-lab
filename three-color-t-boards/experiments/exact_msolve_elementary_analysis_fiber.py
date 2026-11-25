#!/usr/bin/env python3
"""One authorized, bounded fixed-prefix validation of the transformed model."""

import hashlib
import json
import os
import re
import resource
import subprocess
import time
from pathlib import Path

from exact_algebra_backend import monomial_dimension
from exact_msolve_backend import parse_leading
from exact_msolve_prefix_sums import prefix_definitions
from exact_standard_monomials import count_standard_monomials

ROOT = Path(__file__).resolve().parent
STEM = ROOT / "exact_msolve_elementary_analysis_six_fiber"
EXE = ROOT / "exact_msolve_f2_bitset_tools/msolve"
PREFIX = (
    "100011101011000101010011112112211212021201221022121202020220010222002102100022222"
)


def parse_extension_export(raw):
    headers = re.findall(r"^#variable order:\s*(.*?)\s*$", raw, re.MULTILINE)
    expected = [f"x{i + 1}" for i in range(96)] + ["a"]
    if (
        len(headers) != 1
        or [name.strip() for name in headers[0].split(",")] != expected
    ):
        raise ValueError("unexpected actual auxiliary-variable order")
    # Pure identifier alias for the shared parser; preserve the raw export.
    return parse_leading(re.sub(r"\ba\b", "x97", raw), 97, 2)


def limits():
    resource.setrlimit(resource.RLIMIT_AS, (2048 * 1024**2, 2048 * 1024**2))
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))


def main():
    assert len(PREFIX) == 81
    assert not STEM.with_suffix(".json").exists(), "refusing to replace result"
    text, metadata = prefix_definitions(
        all_moments=True, histogram_e2=True, field_equations=True
    )
    lines = text.splitlines()
    lines[0] += ",a"
    fixed = []
    indices = {v: i + 1 for i, v in enumerate(metadata["free_prefix_variables"])}
    for cell, color in enumerate(PREFIX):
        sources = metadata["original_color_linear_forms"][str(cell)]
        terms = [f"x{indices[y]}" for y in sources]
        terms += {"0": ["1"], "1": ["a"], "2": ["a", "1"]}[color]
        fixed.append("+".join(terms))
    transformed = (
        "\n".join(lines).rstrip() + ",\n" + ",\n".join([*fixed, "a^2+a+1"]) + "\n"
    )
    source, basis, logfile = (
        STEM.with_suffix(".ms"),
        STEM.with_suffix(".basis"),
        STEM.with_suffix(".log"),
    )
    source.write_text(transformed)
    command = [
        str(EXE),
        "-f",
        str(source),
        "-o",
        str(basis),
        "-g",
        "1",
        "-l",
        "2",
        "-t",
        "1",
        "-r",
        "1",
        "-c",
        "0",
        "-v",
        "2",
        "-m",
        "16",
    ]
    metadata.update(
        status="RUNNING",
        variables=97,
        generators=358,
        prefix=PREFIX,
        scope="fixed nine-row ternary prefix, transformed coordinates",
        count_scope="fixed prefix completions",
        fixed_cell_count=81,
        fixed_prefix_rows=9,
        fixed_original_cells=list(range(81)),
        equation_labels=metadata["equation_labels"]
        + [f"fixed_color:{i}" for i in range(81)]
        + ["extension_domain:a"],
        count_divisor=2,
        extension_variable=True,
        extension_polynomial="a^2+a+1",
        base_input_sha256=metadata["input_sha256"],
        input_sha256=hashlib.sha256(transformed.encode()).hexdigest(),
        input_file=str(source),
        basis_file=str(basis),
        log_file=str(logfile),
        command=command,
        timeout_seconds=60,
        memory_mb=2048,
        executable_sha256=hashlib.sha256(EXE.read_bytes()).hexdigest(),
        standard_basis_complete=False,
        basis_complete=False,
    )
    STEM.with_suffix(".json").write_text(json.dumps(metadata, indent=2) + "\n")
    start = time.monotonic()
    before = resource.getrusage(resource.RUSAGE_CHILDREN)
    try:
        with logfile.open("w") as log:
            process = subprocess.run(
                command,
                stdout=log,
                stderr=subprocess.STDOUT,
                env=dict(
                    os.environ,
                    LD_LIBRARY_PATH=str(ROOT / "exact_algebra_backend_root/usr/lib"),
                ),
                preexec_fn=limits,
                timeout=60,
                check=False,
            )
        code = process.returncode
        metadata["status"] = "BACKEND_ERROR"
    except subprocess.TimeoutExpired:
        code = None
        metadata["status"] = "TIMEOUT"
    after = resource.getrusage(resource.RUSAGE_CHILDREN)
    metadata.update(
        returncode=code,
        child_wall_seconds=time.monotonic() - start,
        child_cpu_seconds=after.ru_utime
        + after.ru_stime
        - before.ru_utime
        - before.ru_stime,
    )
    log = logfile.read_text()
    marker = log.splitlines().count("MSOLVE_PRIME_GB_EXPORT_COMPLETE")
    metadata["export_marker_count"] = marker
    metadata["error_diagnostics"] = [
        line
        for line in log.splitlines()
        if any(
            word in line.lower()
            for word in [
                "error",
                "segmentation",
                "allocation failed",
                "cannot allocate",
                "out of memory",
            ]
        )
    ]
    STEM.with_suffix(".json").write_text(json.dumps(metadata, indent=2) + "\n")
    if code == 0 and marker == 1 and not metadata["error_diagnostics"]:
        leading = parse_extension_export(basis.read_text())
        metadata.update(
            basis_complete=True,
            standard_basis_complete=True,
            status="BASIS_COMPLETE_COUNT_PENDING",
        )
        document = {
            "format": "leading-monomial-ideal-v1",
            "variables": 97,
            "standard_basis_complete": True,
            "leading_monomials": leading,
            "provenance": {
                "input_sha256": metadata["input_sha256"],
                "executable_sha256": metadata["executable_sha256"],
                "basis_sha256": hashlib.sha256(basis.read_bytes()).hexdigest(),
            },
        }
        Path(str(STEM) + ".leading.json").write_text(
            json.dumps(document, indent=2) + "\n"
        )
        STEM.with_suffix(".json").write_text(json.dumps(metadata, indent=2) + "\n")
        first = monomial_dimension(leading, 97)[0]
        second = count_standard_monomials(leading, 97, standard_basis_complete=True)
        assert first == second == 12, (first, second)
        metadata.update(
            status="COMPLETE",
            quotient_dimension=str(first),
            independent_count=str(second),
            board_count=str(first // 2),
            expected_board_count="6",
            basis_sha256=hashlib.sha256(basis.read_bytes()).hexdigest(),
        )
    metadata["elapsed_seconds"] = time.monotonic() - start
    STEM.with_suffix(".json").write_text(json.dumps(metadata, indent=2) + "\n")
    print(
        json.dumps(
            {
                k: metadata[k]
                for k in [
                    "status",
                    "child_cpu_seconds",
                    "child_wall_seconds",
                    "basis_complete",
                    "export_marker_count",
                ]
            },
            indent=2,
        )
    )
    assert metadata["status"] == "COMPLETE"


if __name__ == "__main__":
    main()
