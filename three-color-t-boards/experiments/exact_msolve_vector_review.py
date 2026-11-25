#!/usr/bin/env python3
"""Independent 9a review: ordinary complete bases, point counts and byte boundaries."""

import hashlib
import itertools
import json
import math
import os
import re
import resource
import subprocess
from pathlib import Path

from exact_algebra_backend import monomial_dimension
from exact_msolve_backend import parse_leading
from exact_msolve_sparse_review import (
    buchberger,
    leading,
    parse_full_basis,
    parse_polynomial,
    reduce_polynomial,
)
from exact_standard_monomials import count_standard_monomials

HERE = Path(__file__).resolve().parent
TREE = "msolve-cc044551f8e202d00691990fd3fd0b1226a88ea2"
OLD = HERE / "exact_msolve_byte_exponent_tools"
NEW = HERE / "exact_msolve_vector_api_tools"
EXE_SHA = "317aeae6e3c82c81fe105b5ef4fc90f65880836f7ce17297f00d495015fd44be"
PATCH_SHA = "82c8810eab2d175aaffb794593da4c0a30c1073eb8f7d3d5ba367f5076382e51"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def limits():
    resource.setrlimit(resource.RLIMIT_AS, (2 * 1024**3, 2 * 1024**3))
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))


def main():
    target = HERE / "exact_msolve_vector_review_runs"
    target.mkdir(exist_ok=False)
    manifest = json.loads((NEW / "source.json").read_text())
    assert sha(NEW / "msolve") == manifest["executable_sha256"] == EXE_SHA
    assert (
        sha(NEW / "typed-byte-vectors.patch") == manifest["patch_sha256"] == PATCH_SHA
    )
    changed = []
    for entry in manifest["source_files"]:
        path = NEW / TREE / entry["path"]
        assert sha(path) == entry["candidate_sha256"], entry["path"]
        old = OLD / TREE / entry["path"]
        assert (sha(old) if old.exists() else hashlib.sha256(b"").hexdigest()) == entry[
            "baseline_sha256"
        ]
        if entry["changed"]:
            changed.append(entry["path"])
    assert len(changed) == 16
    unchanged = []
    for path in (NEW / TREE / "src").rglob("*"):
        if path.is_file() and (
            path.name.startswith("la_")
            or path.name in ("byte_input_guard.h", "byte_model_guard.h")
        ):
            assert (
                path.read_bytes()
                == (OLD / TREE / path.relative_to(NEW / TREE)).read_bytes()
            )
            unchanged.append(str(path.relative_to(NEW / TREE)))
    old_report = json.loads(
        (HERE / "exact_msolve_byte_review_results.json").read_text()
    )
    env = dict(
        os.environ, LD_LIBRARY_PATH=str(HERE / "exact_algebra_backend_root/usr/lib")
    )
    events = re.compile(
        r"^MSOLVE_(?:SYMBOLIC_ROW_RESERVE|SYMBOLIC_STAGING|PROMOTION_RESERVATION|PROMOTION_CAPACITY_REQUEST|PROMOTION_COLUMNS)\b.*$",
        re.MULTILINE,
    )

    def run(label, text, exe, mode=2, extra=()):
        stem = target / label
        inp = stem.with_suffix(".ms")
        inp.write_text(text)
        command = [
            str(exe),
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
            "-f",
            str(inp),
            "-o",
            str(stem.with_suffix(".basis")),
            *extra,
        ]
        done = subprocess.run(
            command,
            capture_output=True,
            text=True,
            env=env,
            timeout=15,
            preexec_fn=limits,
            check=False,
        )
        log = done.stdout + done.stderr
        stem.with_suffix(".log").write_text(log)
        return stem, done, log, command

    results = []
    for fixture in old_report["results"]:
        name = fixture["name"]
        n = fixture["variables"]
        old_input = HERE / "exact_msolve_byte_review_runs" / f"{name}_byte_g2.ms"
        text = old_input.read_text()
        assert sha(old_input) == fixture["input_sha256"]
        polys = [
            parse_polynomial(s, n, 3)
            for s in text.split("\n", 2)[2].strip().split(",\n")
        ]
        reference = buchberger(polys, 3)
        assert all(not reduce_polynomial(p, reference, 3) for p in polys)
        direct = sum(
            all(
                sum(
                    c * math.prod(pow(x, e, 3) for x, e in zip(point, m, strict=False))
                    for m, c in p.items()
                )
                % 3
                == 0
                for p in polys
            )
            for point in itertools.product(range(3), repeat=n)
        )
        lm = [leading(p) for p in reference]
        a = count_standard_monomials(lm, n, standard_basis_complete=True)
        b, _ = monomial_dimension(lm, n)
        assert a == b == direct
        records = []
        for mode in (1, 2):
            bodies = []
            diagnostics = []
            for label, exe in [("eight", OLD / "msolve"), ("nine_a", NEW / "msolve")]:
                stem, done, log, command = run(
                    f"{name}_{label}_g{mode}", text, exe, mode
                )
                assert done.returncode == 0, (name, label, log[-2000:])
                assert log.splitlines().count("MSOLVE_PRIME_GB_EXPORT_COMPLETE") == 1
                assert not re.search(
                    r"\berror\b|failed|out of memory|segmentation|cannot allocate",
                    log,
                    re.IGNORECASE,
                )
                body = stem.with_suffix(".basis").read_text()
                if mode == 2:
                    assert parse_full_basis(body, n, 3) == reference, (name, label)
                else:
                    assert sorted(map(tuple, parse_leading(body, n, 3))) == sorted(
                        lm
                    ), (name, label)
                bodies.append(body)
                diagnostics.append(events.findall(log))
                records.append(
                    {
                        "label": label,
                        "mode": mode,
                        "input_sha256": sha(stem.with_suffix(".ms")),
                        "basis_sha256": sha(stem.with_suffix(".basis")),
                        "command": command,
                        "returncode": done.returncode,
                        "reservation_events": diagnostics[-1],
                    }
                )
            assert bodies[0] == bodies[1] and diagnostics[0] == diagnostics[1], name
        results.append(
            {
                "name": name,
                "variables": n,
                "direct_F3_count": direct,
                "both_bigint_counts_decimal": str(a),
                "independent_full_basis_matches": True,
                "exports_and_diagnostics_identical": True,
                "runs": records,
            }
        )
    rejected = []
    for old_rejection in old_report["rejections"]:
        cmd = old_rejection["command"]
        text = Path(cmd[cmd.index("-f") + 1]).read_text()
        extra = cmd[cmd.index("-o") + 2 :]
        stem, done, log, command = run(
            "reject-" + old_rejection["name"], text, NEW / "msolve", 1, extra
        )
        assert done.returncode != 0 and re.search(r"\bError\b", log)
        assert "MSOLVE_PRIME_GB_EXPORT_COMPLETE" not in log
        assert (
            not stem.with_suffix(".basis").exists()
            or stem.with_suffix(".basis").stat().st_size == 0
        )
        rejected.append(
            {
                "name": old_rejection["name"],
                "returncode": done.returncode,
                "command": command,
            }
        )
    report = {
        "status": "PASS",
        "scope": "independent small ordinary-F3 regression and source comparison; no packing/full solve",
        "executable_sha256": EXE_SHA,
        "patch_sha256": PATCH_SHA,
        "source_tree_sha256": manifest["source_tree_sha256"],
        "source_hashes_verified": len(manifest["source_files"]),
        "changed_source_files": changed,
        "unchanged_coefficient_and_guard_files": unchanged,
        "fixtures": len(results),
        "complete_native_runs": 4 * len(results),
        "independent_Python_bases": len(results),
        "exhaustive_F3_point_counts": len(results),
        "both_bigint_counters_agree": True,
        "inherited_scope_rejections": len(rejected),
        "full_board_solver_runs": 0,
        "results": results,
        "rejections": rejected,
        "review_source_sha256": sha(Path(__file__)),
    }
    (HERE / "exact_msolve_vector_review_results.json").write_text(
        json.dumps(report, indent=2) + "\n"
    )
    print(
        json.dumps(
            {
                k: v
                for k, v in report.items()
                if k
                not in (
                    "results",
                    "rejections",
                    "unchanged_coefficient_and_guard_files",
                )
            },
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
