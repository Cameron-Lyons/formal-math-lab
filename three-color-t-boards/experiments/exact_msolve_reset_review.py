#!/usr/bin/env python3
"""Audit the existing eighth build's -u option; tiny existing inputs only."""

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
from exact_msolve_sparse_review import parse_full_basis
from exact_standard_monomials import count_standard_monomials

HERE = Path(__file__).resolve().parent
TOOLS = HERE / "exact_msolve_byte_exponent_tools"
SOURCE = TOOLS / "msolve-cc044551f8e202d00691990fd3fd0b1226a88ea2/src"
EXE_SHA = "63e52125aba520101ccc7f4f188c626824cf867ebbd80390fbd03ec8c606da76"


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def main():
    assert digest((TOOLS / "msolve").read_bytes()) == EXE_SHA
    calls = []
    for p in SOURCE.rglob("*"):
        if p.suffix not in (".c", ".h"):
            continue
        for i, line in enumerate(p.read_text().splitlines(), 1):
            if re.search(r"\breset_hash_table\s*\(", line):
                calls.append((str(p.relative_to(SOURCE)), i, line.strip()))
    calls.sort()
    assert calls == [
        ("neogb/hash.c", 1668, "static void reset_hash_table("),
        ("neogb/modular.c", 459, "reset_hash_table(bht, bs, ps, st);"),
    ], calls
    modular = (SOURCE / "neogb/modular.c").read_text()
    call = modular.index("reset_hash_table(bht, bs, ps, st);")
    saturation = modular.index("bs_t *f4sat_trace_application_test_phase(")
    next_function = modular.index("\nbs_t *", saturation + 10)
    assert saturation < call < next_function
    f4 = (SOURCE / "neogb/f4.c").read_text()
    ordinary = f4[
        f4.index("bs_t *core_f4(") : f4.index("int64_t export_results_from_f4(")
    ]
    assert "reset_ht" not in ordinary and "reset_hash_table" not in ordinary
    assert (
        "st->reset_ht = reset_hash_table > 0 ? reset_hash_table : 2147483647"
        in (SOURCE / "neogb/io.c").read_text()
    )
    output = HERE / "exact_msolve_reset_review_runs"
    output.mkdir(exist_ok=False)
    env = dict(
        os.environ, LD_LIBRARY_PATH=str(HERE / "exact_algebra_backend_root/usr/lib")
    )
    old = json.loads((HERE / "exact_msolve_byte_review_results.json").read_text())
    expected = {r["name"]: int(r["quotient_dimension_decimal"]) for r in old["results"]}
    fixtures = [
        (
            name,
            HERE / f"exact_msolve_byte_review_runs/{name}_byte_g1.ms",
            expected[name],
        )
        for name in ("mixed-chain", "dense-chain")
    ]
    fixtures.append(
        ("known-six-prefix", HERE / "exact_native_field_probe_runs/ternary_six.ms", 6)
    )

    def limits():
        resource.setrlimit(resource.RLIMIT_AS, (2 * 1024**3, 2 * 1024**3))
        resource.setrlimit(resource.RLIMIT_CORE, (0, 0))

    records = []
    for name, input_source, count in fixtures:
        source = input_source.read_bytes()
        variables = len(source.splitlines()[0].split(b","))
        input_path = output / (name + ".ms")
        input_path.write_bytes(source)
        for mode in (1, 2):
            reference = None
            event_reference = None
            for interval in (0, 1, 5):
                stem = output / f"{name}_g{mode}_u{interval}"
                command = [
                    str(TOOLS / "msolve"),
                    "-g",
                    str(mode),
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
                    "-s",
                    "4",
                    "-u",
                    str(interval),
                    "-f",
                    str(input_path),
                    "-o",
                    str(stem.with_suffix(".basis")),
                ]
                before = resource.getrusage(resource.RUSAGE_CHILDREN)
                start = time.monotonic()
                q = subprocess.run(
                    command,
                    capture_output=True,
                    text=True,
                    timeout=15,
                    env=env,
                    preexec_fn=limits,
                    check=False,
                )
                elapsed = time.monotonic() - start
                after = resource.getrusage(resource.RUSAGE_CHILDREN)
                log = q.stdout + q.stderr
                stem.with_suffix(".log").write_text(log)
                assert (
                    q.returncode == 0
                    and log.splitlines().count("MSOLVE_PRIME_GB_EXPORT_COMPLETE") == 1
                )
                assert not re.search(
                    r"\berror\b|failed|cannot allocate|segmentation|out of memory",
                    log,
                    re.IGNORECASE,
                )
                basis = stem.with_suffix(".basis").read_bytes()
                if mode == 1:
                    leading = parse_leading(basis.decode(), variables, 3)
                    assert (
                        count_standard_monomials(
                            leading, variables, standard_basis_complete=True
                        )
                        == count
                    )
                    assert (
                        monomial_dimension(leading, variables, seconds=10)[0] == count
                    )
                else:
                    assert parse_full_basis(basis.decode(), variables, 3)
                if reference is None:
                    reference = basis
                else:
                    assert basis == reference, (name, mode, interval)
                event_lines = [
                    line
                    for line in log.splitlines()
                    if line.startswith("MSOLVE_") and "EXPORT_COMPLETE" not in line
                ]
                events = "\n".join(event_lines)
                if event_reference is None:
                    event_reference = events
                else:
                    assert events == event_reference, (
                        name,
                        mode,
                        interval,
                        "capacity/promotion sequence changed",
                    )
                advertised = re.search(
                    r"^basis hash table resetting\s+(\S+)\s*$", log, re.MULTILINE
                )
                assert advertised and advertised[1] == (
                    "OFF" if interval == 0 else str(interval)
                )
                rht = re.search(
                    r"^rht\s+(\d+\.\d+) sec\s+(\d+\.\d+)%", log, re.MULTILINE
                )
                if interval == 0:
                    assert rht is None
                else:
                    assert rht and float(rht[1]) == float(rht[2]) == 0
                records.append(
                    {
                        "fixture": name,
                        "scope": "fixed known-six prefix"
                        if name == "known-six-prefix"
                        else "small arithmetic fixture",
                        "variables": variables,
                        "mode": mode,
                        "reset_option": interval,
                        "status": "COMPLETE",
                        "returncode": q.returncode,
                        "input_sha256": digest(source),
                        "basis_sha256": digest(basis),
                        "command": command,
                        "log_sha256": digest(log.encode()),
                        "basis_byte_identical_to_u0": True,
                        "allocation_promotion_event_sequence_sha256": digest(
                            events.encode()
                        ),
                        "allocation_promotion_events": len(event_lines),
                        "option_advertised": advertised[1],
                        "printed_reset_seconds": float(rht[1]) if rht else None,
                        "quotient_dimension_decimal": str(count) if mode == 1 else None,
                        "child_wall_seconds": elapsed,
                        "child_cpu_seconds": after.ru_utime
                        + after.ru_stime
                        - before.ru_utime
                        - before.ru_stime,
                    }
                )
    result = {
        "status": "PASS_NO_ORDINARY_RESET_CALL",
        "executable_sha256": EXE_SHA,
        "source_hashes": {
            p: digest((SOURCE / p).read_bytes())
            for p in (
                "neogb/hash.c",
                "neogb/modular.c",
                "neogb/f4.c",
                "neogb/engine.c",
                "neogb/io.c",
                "neogb/meta_data.c",
                "msolve/main.c",
                "msolve/msolve.c",
            )
        },
        "reset_identifier_call_or_definition_sites": calls,
        "sole_call_enclosing_function": "f4sat_trace_application_test_phase",
        "ordinary_core_has_no_reset_call": True,
        "scope_of_sole_caller_excluded_by_byte_guards": True,
        "ordinary_flag_effect": "stored and printed; not used to reset tables in ordinary core_f4",
        "tiny_complete_runs": len(records),
        "unrestricted_solver_runs": 0,
        "source_changes": 0,
        "memory_semantics": "No observed allocator-event difference. No RSS saving claimed. If invoked, reset retains esz/hsz and temporarily holds old+new exponent slabs and pointer arrays.",
        "results": records,
    }
    (HERE / "exact_msolve_reset_review_results.json").write_text(
        json.dumps(result, indent=2) + "\n"
    )
    print(
        json.dumps(
            {k: v for k, v in result.items() if k not in ("results", "source_hashes")},
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
