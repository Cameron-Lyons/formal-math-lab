#!/usr/bin/env python3
"""Exercise integrated fallback routes without changing the frozen kernel."""

import hashlib
import json
import os
import resource
import subprocess
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent
BASE = ROOT.parent / "exact_msolve_rounded_promotion_tools"
ENV = dict(
    os.environ, LD_LIBRARY_PATH=str(ROOT.parent / "exact_algebra_backend_root/usr/lib")
)
TEXT = "x1,x2,x3,x4\n2\nx1^3+1,x2^3+1,x3^3+1,x4^3+1,x1*x2+x3,x2*x3+x4\n"


def limits():
    resource.setrlimit(resource.RLIMIT_AS, (2048 * 1024**2, 2048 * 1024**2))
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))


def main():
    results = []
    for name, la, threads, extra, characteristic in (
        ("sparse_dense", 1, 1, [], 2),
        ("thread_count_two", 2, 2, [], 2),
        ("elimination_block", 2, 1, ["-e", "1"], 2),
        ("characteristic_five", 2, 1, [], 5),
    ):
        exports = []
        runs = []
        for kind, directory in (("fourth", BASE), ("fifth", ROOT)):
            stem = ROOT / ("fallback_" + name + "_" + kind)
            assert not stem.with_suffix(".ms").exists(), "refuse overwrite"
            stem.with_suffix(".ms").write_text(
                TEXT.replace("\n2\n", f"\n{characteristic}\n")
            )
            command = [
                str(directory / "msolve"),
                "-f",
                str(stem.with_suffix(".ms")),
                "-o",
                str(stem.with_suffix(".basis")),
                "-g",
                "2",
                "-s",
                "4",
                "-l",
                str(la),
                "-t",
                str(threads),
                "-r",
                "1",
                "-c",
                "0",
                "-v",
                "2",
                *extra,
            ]
            before = resource.getrusage(resource.RUSAGE_CHILDREN)
            started = time.monotonic()
            process = subprocess.run(
                command,
                capture_output=True,
                text=True,
                env=ENV,
                preexec_fn=limits,
                timeout=30,
                check=False,
            )
            after = resource.getrusage(resource.RUSAGE_CHILDREN)
            log = process.stdout + process.stderr
            stem.with_suffix(".log").write_text(log)
            assert (
                process.returncode == 0
                and log.splitlines().count("MSOLVE_PRIME_GB_EXPORT_COMPLETE") == 1
            )
            assert "MSOLVE_F2_BITSET " not in log, (name, kind)
            data = stem.with_suffix(".basis").read_bytes()
            exports.append(data)
            runs.append(
                {
                    "command": command,
                    "returncode": process.returncode,
                    "wall_seconds": time.monotonic() - started,
                    "cpu_seconds": after.ru_utime
                    + after.ru_stime
                    - before.ru_utime
                    - before.ru_stime,
                    "executable_sha256": hashlib.sha256(
                        (directory / "msolve").read_bytes()
                    ).hexdigest(),
                    "export_sha256": hashlib.sha256(data).hexdigest(),
                    "bitset_kernel_entered": False,
                }
            )
        assert exports[0] == exports[1], name
        results.append(
            {
                "name": name,
                "status": "PASS",
                "exports_byte_identical": True,
                "runs": runs,
            }
        )
    (ROOT / "mode_validation.json").write_text(
        json.dumps({"status": "PASS", "cases": results}, indent=2) + "\n"
    )
    print("PASS", len(results), "integrated fallback comparisons")


if __name__ == "__main__":
    main()
