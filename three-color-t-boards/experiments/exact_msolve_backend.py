#!/usr/bin/env python3
"""Deterministic prime-field F4 basis calculation and exact staircase counting.

This never counts prime-field rational points: quotient dimensions count
geometric roots after scalar extension. A quadratic coefficient extension for
a fixed prefix is represented by one extra variable, with a recorded factor 2.
"""

import argparse
import hashlib
import json
import math
import os
import re
import resource
import subprocess
import time
from pathlib import Path

from exact_algebra_backend import monomial_dimension
from exact_prime_fourier import generate_model
from exact_standard_monomials import count_standard_monomials

ROOT = Path(__file__).resolve().parent
EXECUTABLE = ROOT / "exact_msolve_tools/msolve"


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def poly_text(terms, prime):
    pieces = []
    for exponents, coefficient in sorted(terms.items()):
        coefficient %= prime
        if not coefficient:
            continue
        factors = [
            f"x{i + 1}" + (f"^{e}" if e != 1 else "")
            for i, e in enumerate(exponents)
            if e
        ]
        pieces.append(str(coefficient) + ("*" + "*".join(factors) if factors else ""))
    return "+".join(pieces) or "0"


def base_definitions(
    prime=29,
    prefix="",
    binary=False,
    fixture=None,
    pivot_order=False,
    ternary_reduced=None,
):
    if ternary_reduced is not None:
        if ternary_reduced not in ("representatives", "all"):
            raise ValueError("unknown reduced Fourier generator selection")
        if prime != 2 or prefix or binary or fixture or pivot_order:
            raise ValueError(
                "reduced Fourier export requires F2 and no other model options"
            )
        from exact_msolve_reduced import reduced_definitions

        return reduced_definitions(all_moments=ternary_reduced == "all")
    if pivot_order and (binary or fixture):
        raise ValueError(
            "dispersed variable order is supported only for ternary models"
        )
    metadata = {"prime": prime, "prefix": prefix, "count_divisor": 1}
    if fixture:
        if prefix or binary:
            raise ValueError("fixture cannot be combined with board restrictions")
        fixtures = {
            "domain": (1, ["x1^3-1"]),
            "domain-pair": (2, ["x1^3-1", "x2^3-1"]),
            "sum-three": (3, ["x1^3-1", "x2^3-1", "x3^3-1", "x1+x2+x3"]),
            "unit": (1, ["x1^3-1", "1"]),
            "bigint": (10, [f"x{i + 1}^100-1" for i in range(10)]),
        }
        n, polynomials = fixtures[fixture]
        metadata.update(scope="arithmetic fixture", fixture=fixture)
    elif binary:
        if prefix:
            raise ValueError("binary reduced model does not accept a prefix")
        source = ROOT / "exact_parity_math_reduced_2.json"
        data = json.loads(source.read_text())
        prime = 2
        n = data["variables"]
        polynomials = [f"x{i + 1}^2+x{i + 1}" for i in range(n)]
        for equation in data["equations"]:
            terms = {}
            for encoded in equation["terms"]:
                bits = int(encoded, 16)
                if bits >> n:
                    raise ValueError("binary monomial exceeds ring")
                term = tuple((bits >> i) & 1 for i in range(n))
                terms[term] = (terms.get(term, 0) + 1) % 2
            polynomials.append(poly_text(terms, prime))
        metadata.update(
            scope="all binary boards",
            source=str(source),
            source_sha256=sha256(source.read_bytes()),
        )
    else:
        height = math.isqrt(len(prefix))
        if height * height != len(prefix) or any(c not in "012" for c in prefix):
            raise ValueError("prefix must consist of complete ternary rows")
        rows = [prefix[r * r : (r + 1) ** 2] for r in range(height)]
        model = generate_model(prime, rows, all_moments=True)
        free = model["variables"]
        free_cells = model["free_original_cells"]
        preferred = (
            [free_cells.index(cell) for cell in (0, 81, 90, 99) if cell in free_cells]
            if pivot_order
            else []
        )
        variable_order = preferred + [i for i in range(free) if i not in preferred]
        variable_index = {old: new for new, old in enumerate(variable_order)}
        extension = model["requires_quadratic_coefficients"]
        n = max(1, free + int(extension))
        polynomials = [f"x{i + 1}^3-1" for i in range(free)]
        if extension:
            polynomials.append(f"x{free + 1}^2+x{free + 1}+1")
        elif not free:
            polynomials.append("x1")
        for equation in model["moment_equations"]:
            terms = {}
            for term in equation["terms"]:
                u, v = term["coefficient"]
                powers = [0] * n
                for i, e in term["monomial"]:
                    powers[variable_index[i]] = e
                key = tuple(powers)
                terms[key] = (terms.get(key, 0) + u) % prime
                if v:
                    if not extension:
                        raise ValueError("quadratic coefficient without extension")
                    powers[free] = 1
                    key = tuple(powers)
                    terms[key] = (terms.get(key, 0) + v) % prime
            text = poly_text(terms, prime)
            if text != "0":
                polynomials.append(text)
        metadata.update(
            scope=model["count_scope"],
            free_board_variables=free,
            extension_variable=extension,
            count_divisor=2 if extension else 1,
            dispersed_variable_order=pivot_order,
            variable_original_cells=[free_cells[i] for i in variable_order],
            model_data_sha256=sha256(json.dumps(model, sort_keys=True).encode()),
            moment_equations=80,
            generator_sha256=sha256((ROOT / "exact_prime_fourier.py").read_bytes()),
        )
        if not prefix:
            assert n == 100 and len(polynomials) == 180 and not extension
    metadata.update(
        variables=n,
        generators=len(polynomials),
        prime=prime,
        field=f"F{prime}",
        ring_type="ordinary polynomial ring",
    )
    text = ",".join(f"x{i + 1}" for i in range(n)) + "\n" + str(prime) + "\n"
    text += ",\n".join(polynomials) + "\n"
    return text, metadata


def definitions(
    prime=29,
    prefix="",
    binary=False,
    fixture=None,
    pivot_order=False,
    ternary_reduced=None,
    histogram_e2=False,
    ternary_prefix_sums=None,
    prefix_field_equations=False,
    histogram_e4=False,
    ternary_native_field=False,
    native_e3=False,
    native_translation=False,
    native_order=None,
    native_sign=False,
    native_sign_branch=None,
    native_branch_elimination=False,
):
    if native_branch_elimination and native_sign_branch is None:
        raise ValueError("branch elimination requires a selected linear sign branch")
    if ternary_native_field:
        if (
            prime != 3
            or prefix
            or binary
            or fixture
            or pivot_order
            or ternary_reduced
            or ternary_prefix_sums
            or histogram_e2
            or prefix_field_equations
            or histogram_e4
        ):
            raise ValueError(
                "native-field coordinates require F3 and no other model options"
            )
        if native_sign_branch is not None:
            if native_sign or not native_translation or not native_e3:
                raise ValueError(
                    "linear sign branch requires translation/e3 and excludes quintic sign gauge"
                )
            if native_branch_elimination:
                from exact_msolve_native_branch_elimination import (
                    eliminated_branch_definitions,
                )

                return eliminated_branch_definitions(native_sign_branch, native_order)
            from exact_msolve_native_sign_branch import branch_definitions

            return branch_definitions(native_sign_branch, native_order)
        if native_sign:
            if not native_translation or not native_e3:
                raise ValueError(
                    "native sign factorization requires translation and e3"
                )
            from exact_msolve_native_sign import sign_definitions

            return sign_definitions(native_order)
        if native_translation:
            from exact_msolve_translation import translation_definitions

            source, metadata = translation_definitions(e3=native_e3)
            if native_order is not None:
                if native_order != "minimum-fill" or not native_e3:
                    raise ValueError(
                        "minimum-fill ordering requires the translated native e3 model"
                    )
                from exact_msolve_native_order import reorder

                source, metadata = reorder(source, metadata)
            return source, metadata
        if native_order is not None:
            raise ValueError(
                "native variable ordering requires translation factorization"
            )
        from exact_msolve_native_field import native_definitions

        source, metadata = native_definitions()
        if native_e3:
            from exact_msolve_native_e3 import augment

            source, metadata = augment(source, metadata)
        return source, metadata
    if native_sign_branch is not None:
        raise ValueError("linear sign branch requires the natural-F3 model")
    if native_sign:
        raise ValueError("sign factorization requires the natural-F3 model")
    if native_e3:
        raise ValueError("native e3 requires the natural-F3 model")
    if native_translation:
        raise ValueError("translation factorization requires the natural-F3 model")
    if native_order is not None:
        raise ValueError("native variable ordering requires the natural-F3 model")
    if ternary_prefix_sums is not None:
        if ternary_prefix_sums not in ("representatives", "all"):
            raise ValueError("unknown prefix-sum Fourier generator selection")
        if prime != 2 or prefix or binary or fixture or pivot_order or ternary_reduced:
            raise ValueError(
                "prefix-sum coordinates require F2 and no other model options"
            )
        from exact_msolve_prefix_sums import prefix_definitions

        source, metadata = prefix_definitions(
            all_moments=ternary_prefix_sums == "all",
            histogram_e2=histogram_e2,
            field_equations=prefix_field_equations,
        )
        if histogram_e4:
            from exact_msolve_prefix_e4 import augment

            source, metadata = augment(source, metadata)
        return source, metadata
    if histogram_e4:
        raise ValueError(
            "e4 augmentation requires prefix-sum coordinates and e2 equations"
        )
    if prefix_field_equations:
        raise ValueError("prefix field equations require prefix-sum coordinates")
    if histogram_e2 and (prime != 2 or prefix or binary or fixture):
        raise ValueError(
            "elementary augmentation requires an unrestricted ternary F2 model"
        )
    source, metadata = base_definitions(
        prime, prefix, binary, fixture, pivot_order, ternary_reduced
    )
    if histogram_e2:
        from exact_msolve_elementary import augment

        source, metadata = augment(
            source, metadata, reduced=ternary_reduced is not None
        )
    return source, metadata


def parse_leading(output, variables, prime):
    """Parse only complete, explicitly described leading-ideal output."""
    if re.search(
        r"\berror\b|out of memory|cannot allocate|segmentation|aborted",
        output,
        re.IGNORECASE,
    ):
        raise ValueError("diagnostic in leading-ideal output")
    lines = output.splitlines()
    if sum(line.strip() == "#Leading ideal data" for line in lines) != 1:
        raise ValueError("missing or duplicate leading-ideal marker")
    headers = {}
    labels = [
        "field characteristic",
        "length of basis",
        "variable order",
        "monomial order",
    ]
    for line in lines:
        if not line.lstrip().startswith("#") or line.strip() in (
            "#---",
            "#Leading ideal data",
        ):
            continue
        header = re.fullmatch(r"\s*#\s*([^:]+):\s*(.*?)\s*", line)
        if not header or header.group(1) not in labels or header.group(1) in headers:
            raise ValueError("unknown or duplicated basis metadata")
        headers[header.group(1)] = header.group(2)
    if set(headers) != set(labels) or headers["field characteristic"] != str(prime):
        raise ValueError("missing or inconsistent basis metadata")
    count = re.fullmatch(
        r"(\d+) elements?(?: sorted by increasing leading monomials)?",
        headers["length of basis"],
    )
    if not count:
        raise ValueError("invalid basis length metadata")
    names = [v.strip() for v in headers["variable order"].split(",")]
    if names != [f"x{i + 1}" for i in range(variables)]:
        raise ValueError("variable order mismatch")
    if headers["monomial order"] != "graded reverse lexicographical":
        raise ValueError("unexpected monomial ordering")
    payload = "\n".join(
        line for line in output.splitlines() if not line.lstrip().startswith("#")
    )
    match = re.fullmatch(r"\s*\[(.*?)\]\s*:\s*", payload, re.DOTALL)
    if not match:
        raise ValueError("incomplete leading-monomial list")
    monomials = (
        [s.strip() for s in match.group(1).split(",")] if match.group(1).strip() else []
    )
    if len(monomials) != int(count.group(1)):
        raise ValueError("leading-monomial count mismatch")
    leading = []
    for term in monomials:
        exponents = [0] * variables
        if term != "1":
            for factor in term.split("*"):
                piece = re.fullmatch(r"x([1-9]\d*)(?:\^([1-9]\d*))?", factor.strip())
                if not piece or int(piece.group(1)) > variables:
                    raise ValueError("invalid leading monomial: " + term)
                i = int(piece.group(1)) - 1
                if exponents[i]:
                    raise ValueError("repeated variable in leading monomial")
                exponents[i] = int(piece.group(2) or 1)
        leading.append(exponents)
    return leading


def run(
    output,
    *,
    prime=29,
    prefix="",
    binary=False,
    fixture=None,
    seconds=90,
    memory_mb=2048,
    prepare_only=False,
    executable=EXECUTABLE,
    library_dir=None,
    max_pairs=0,
    require_export_marker=False,
    pivot_order=False,
    ternary_reduced=None,
    histogram_e2=False,
    ternary_prefix_sums=None,
    prefix_field_equations=False,
    histogram_e4=False,
    ternary_native_field=False,
    native_e3=False,
    native_translation=False,
    native_order=None,
    native_sign=False,
    native_sign_branch=None,
    native_branch_elimination=False,
):
    if seconds <= 0 or memory_mb <= 0 or max_pairs < 0:
        raise ValueError("invalid resource limit or pair batch size")
    output = Path(output)
    source, metadata = definitions(
        prime,
        prefix,
        binary,
        fixture,
        pivot_order,
        ternary_reduced,
        histogram_e2,
        ternary_prefix_sums,
        prefix_field_equations,
        histogram_e4,
        ternary_native_field,
        native_e3,
        native_translation,
        native_order,
        native_sign,
        native_sign_branch,
        native_branch_elimination,
    )
    input_path = output.with_suffix(".ms")
    basis_path = output.with_suffix(".basis")
    log_path = output.with_suffix(".log")
    if any(
        output.with_suffix(suffix).exists()
        for suffix in (".ms", ".basis", ".json", ".log", ".leading.json")
    ):
        raise ValueError("refusing to overwrite prior run artifacts")
    input_path.write_text(source)
    executable = Path(executable).resolve()
    command = [
        str(executable),
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
        str(max_pairs),
        "-f",
        str(input_path),
        "-o",
        str(basis_path),
    ]
    metadata.update(
        command=command,
        source_sha256=sha256(source.encode()),
        adapter_sha256=sha256(Path(__file__).read_bytes()),
        input_file=str(input_path),
        linear_algebra="exact sparse (-l 2)",
        log_file=str(log_path),
        log_streaming=True,
        threads=1,
        timeout_seconds=seconds,
        memory_mb=memory_mb,
        require_export_marker=require_export_marker,
        basis_complete=False,
        status="PREPARED_NOT_RUN",
    )
    if prepare_only:
        output.with_suffix(".json").write_text(json.dumps(metadata, indent=2) + "\n")
        return metadata
    metadata["executable_sha256"] = sha256(executable.read_bytes())
    started = time.monotonic()
    before = resource.getrusage(resource.RUSAGE_CHILDREN)

    def limits():
        resource.setrlimit(
            resource.RLIMIT_AS, (memory_mb * 1024**2, memory_mb * 1024**2)
        )
        resource.setrlimit(resource.RLIMIT_CORE, (0, 0))

    env = os.environ.copy()
    library_dirs = ([str(Path(library_dir).resolve())] if library_dir else []) + [
        str(ROOT / "exact_msolve_tools/usr/lib"),
        str(ROOT / "exact_algebra_backend_root/usr/lib"),
    ]
    env["LD_LIBRARY_PATH"] = ":".join(library_dirs)
    metadata["library_dirs"] = library_dirs
    metadata["local_shared_libraries"] = {
        str(path): sha256(path.read_bytes())
        for folder in library_dirs
        for path in Path(folder).glob("lib*.so*")
        if path.is_file() and not path.is_symlink()
    }
    # The child writes directly to the fresh log, so flushed solver progress
    # remains readable during execution and survives a timeout or interruption.
    with log_path.open("x", encoding="utf-8") as log_file:
        try:
            process = subprocess.run(
                command,
                stdout=log_file,
                stderr=subprocess.STDOUT,
                text=True,
                timeout=seconds,
                preexec_fn=limits,
                env=env,
                check=False,
            )
            metadata["returncode"] = process.returncode
            metadata["status"] = "BACKEND_ERROR"
        except subprocess.TimeoutExpired:
            metadata["status"] = "INCOMPLETE_TIMEOUT"
    log = log_path.read_text(encoding="utf-8", errors="replace")
    after = resource.getrusage(resource.RUSAGE_CHILDREN)
    metadata["child_cpu_seconds"] = (
        after.ru_utime + after.ru_stime - before.ru_utime - before.ru_stime
    )
    metadata["child_wall_seconds"] = time.monotonic() - started
    metadata["error_diagnostics"] = [
        line
        for line in log.splitlines()
        if re.search(
            r"\berror\b|out of memory|cannot allocate|segmentation|aborted",
            line,
            re.IGNORECASE,
        )
    ]
    metadata["export_marker_count"] = sum(
        line.strip() == "MSOLVE_PRIME_GB_EXPORT_COMPLETE" for line in log.splitlines()
    )
    if require_export_marker and metadata["export_marker_count"] != 1:
        metadata["error_diagnostics"].append(
            "missing or duplicate patched export-completion marker"
        )
    if metadata.get("returncode") == 0 and not metadata["error_diagnostics"]:
        try:
            result = basis_path.read_text()
            leading = parse_leading(result, metadata["variables"], metadata["prime"])
            metadata.update(
                basis_complete=True,
                standard_basis_complete=True,
                basis_size=len(leading),
                basis_sha256=sha256(result.encode()),
            )
            record = {
                "format": "leading-monomial-ideal-v1",
                "variables": metadata["variables"],
                "standard_basis_complete": True,
                "leading_monomials": leading,
                "provenance": {
                    "backend": "msolve F4",
                    "input_sha256": metadata["source_sha256"],
                    "executable_sha256": metadata["executable_sha256"],
                    "field": metadata["field"],
                    "linear_algebra": "exact sparse",
                },
            }
            output.with_suffix(".leading.json").write_text(
                json.dumps(record, indent=2) + "\n"
            )
            first, first_stats = monomial_dimension(
                leading, metadata["variables"], seconds=seconds
            )
            second_stats = {}
            second = count_standard_monomials(
                leading,
                metadata["variables"],
                standard_basis_complete=True,
                max_states=1000000,
                stats=second_stats,
            )
            if first != second:
                raise ValueError("independent monomial counts disagree")
            if first % metadata["count_divisor"]:
                raise ValueError("quotient dimension violates extension degree")
            metadata.update(
                status="COMPLETE",
                dimension_decimal=str(first),
                board_count_decimal=str(first // metadata["count_divisor"]),
                monomial_counter=first_stats,
                independent_counter=second_stats,
            )
        except (
            ValueError,
            OSError,
            RuntimeError,
            MemoryError,
            RecursionError,
        ) as error:
            metadata.update(
                status="POSTPROCESS_ERROR",
                postprocess_error=f"{type(error).__name__}: {error}",
            )
    metadata["elapsed_seconds"] = time.monotonic() - started
    output.with_suffix(".json").write_text(json.dumps(metadata, indent=2) + "\n")
    return metadata


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--prime", type=int, default=29)
    parser.add_argument("--prefix", default="")
    parser.add_argument("--binary", action="store_true")
    parser.add_argument(
        "--fixture", choices=["domain", "domain-pair", "sum-three", "unit", "bigint"]
    )
    parser.add_argument("--seconds", type=float, default=90)
    parser.add_argument("--memory-mb", type=int, default=2048)
    parser.add_argument("--prepare-only", action="store_true")
    parser.add_argument("--executable", type=Path, default=EXECUTABLE)
    parser.add_argument("--library-dir", type=Path)
    parser.add_argument("--max-pairs", type=int, default=0)
    parser.add_argument("--require-export-marker", action="store_true")
    parser.add_argument("--pivot-order", action="store_true")
    parser.add_argument("--ternary-reduced", choices=["representatives", "all"])
    parser.add_argument("--histogram-e2", action="store_true")
    parser.add_argument("--ternary-prefix-sums", choices=["representatives", "all"])
    parser.add_argument("--prefix-field-equations", action="store_true")
    parser.add_argument("--histogram-e4", action="store_true")
    parser.add_argument("--ternary-native-field", action="store_true")
    parser.add_argument("--native-e3", action="store_true")
    parser.add_argument("--native-translation", action="store_true")
    parser.add_argument("--native-order", choices=["minimum-fill"])
    parser.add_argument("--native-sign", action="store_true")
    parser.add_argument("--native-sign-branch", type=int, choices=range(4))
    parser.add_argument("--native-branch-elimination", action="store_true")
    args = parser.parse_args()
    result = run(**vars(args))
    print(json.dumps(result, indent=2))
    if result["status"] not in ("COMPLETE", "PREPARED_NOT_RUN"):
        raise SystemExit(1)


if __name__ == "__main__":
    main()
