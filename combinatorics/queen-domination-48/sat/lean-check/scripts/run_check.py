#!/usr/bin/env python3
"""Run qdcheck on a complete certificate directory and write a summary file.

    python3 -I scripts/run_check.py n k CERTDIR --jobs N --log LOG.jsonl --summary SUMMARY.json [--out STDOUT.txt]

Runs `.lake/build/bin/qdcheck n k CERTDIR --jobs N --log LOG.jsonl`, copies its standard output to
--out (default: SUMMARY.json with the suffix .stdout.txt) and writes to SUMMARY.json:
n, k, the number of cases / verified / failed, the final line of qdcheck verbatim, its exit code, wall
and CPU seconds, peak memory, the toolchain, and the SHA-256 of the qdcheck binary and of every
Lean source and Lake configuration file of the packages lean-check and lean-sat (so that the run can
be tied to the sources without git).  The exit code of this script is the exit code of qdcheck.
"""

import argparse
import hashlib
import json
import os
import resource
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
PKG = os.path.dirname(HERE)
REPO = os.path.dirname(PKG)
Q = os.path.join(PKG, ".lake", "build", "bin", "qdcheck")


def sha(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for blk in iter(lambda: f.read(1 << 20), b""):
            h.update(blk)
    return h.hexdigest()


def rel(path):
    return os.path.relpath(os.path.abspath(path), REPO)


def sources():
    out = {}
    for pkg in ("lean-check", "lean-sat"):
        root = os.path.join(REPO, pkg)
        for d, dirs, files in os.walk(root):
            dirs[:] = sorted(x for x in dirs if x not in (".lake", "__pycache__"))
            for f in sorted(files):
                if f.endswith(".lean") or f in (
                    "lakefile.toml",
                    "lake-manifest.json",
                    "lean-toolchain",
                ):
                    p = os.path.join(d, f)
                    out[os.path.relpath(p, REPO)] = sha(p)
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("n", type=int)
    ap.add_argument("k", type=int)
    ap.add_argument("certdir")
    ap.add_argument("--jobs", type=int, default=5)
    ap.add_argument("--log", required=True)
    ap.add_argument("--summary", required=True)
    ap.add_argument("--out", default="")
    a = ap.parse_args()
    out_path = a.out or (a.summary.removesuffix(".json")) + ".stdout.txt"
    cmd = [Q, str(a.n), str(a.k), a.certdir, "--jobs", str(a.jobs), "--log", a.log]
    binary_sha = sha(Q)
    src = sources()
    lean_version = subprocess.run(
        ["lean", "--version"], capture_output=True, text=True, cwd=PKG, check=False
    ).stdout.strip()
    zstd_version = subprocess.run(
        ["zstd", "--version"], capture_output=True, text=True, check=False
    ).stdout.strip()
    started = time.strftime("%Y-%m-%dT%H:%M:%S%z")
    t0 = time.time()
    r0 = resource.getrusage(resource.RUSAGE_CHILDREN)
    with open(out_path, "w") as f:
        rc = subprocess.run(cmd, stdout=f, check=False).returncode
    wall = time.time() - t0
    r1 = resource.getrusage(resource.RUSAGE_CHILDREN)
    with open(out_path) as f:
        lines = f.read().splitlines()
    # the status line must be the last line of the output and the only line that starts with `s `
    status = [l for l in lines if l.startswith("s ")]
    final = lines[-1] if lines and status == [lines[-1]] else ""
    summ = {}
    cases = verified = failed = 0
    failures = []
    with open(a.log) as f:
        for l in f:
            rec = json.loads(l)
            if "summary" in rec:
                summ = rec["summary"]
            elif "case" in rec:
                cases += 1
                if rec["verdict"] == "verified":
                    verified += 1
                else:
                    failed += 1
                    failures.append(
                        {"case": rec["case"], "reason": rec.get("reason", "")}
                    )
    with open(os.path.join(PKG, "lean-toolchain")) as f:
        toolchain = f.read().strip()
    result = {
        "n": a.n,
        "k": a.k,
        "statement": summ.get("statement", "none"),
        "all_verified": (
            rc == 0
            and final == f"s ALL VERIFIED n={a.n:d} k={a.k:d} cases={cases:d}"
            and cases > 0
            and verified == cases
            and summ.get("all_verified") is True
        ),
        "final_line": final,
        "exit_code": rc,
        "case_list": summ.get("case_list"),
        "cases": cases,
        "verified": verified,
        "failed": failed,
        "failures": failures,
        "jobs": a.jobs,
        "wall_seconds": round(wall, 1),
        "cpu_seconds": round(
            (r1.ru_utime - r0.ru_utime) + (r1.ru_stime - r0.ru_stime), 1
        ),
        "cpu_user_seconds": round(r1.ru_utime - r0.ru_utime, 1),
        "cpu_system_seconds": round(r1.ru_stime - r0.ru_stime, 1),
        "cpu_note": "cpu_seconds: user + system time of qdcheck and all its child processes (decompression servers, zstd), from getrusage(RUSAGE_CHILDREN)",
        "checker_process_cpu_seconds": round(summ.get("process_cpu_ms", 0) / 1000, 1),
        "checker_worker_threads_cpu_seconds": round(
            summ.get("worker_cpu_ms", 0) / 1000, 1
        ),
        "decompression_cpu_seconds": round(summ.get("decompress_cpu_ms", 0) / 1000, 1),
        "peak_rss_kb": summ.get("peak_rss_kb"),
        "peak_rss_note": "VmHWM of the qdcheck process (all worker threads), as reported by itself; max_rss_kb_any_process is ru_maxrss over qdcheck and its children",
        "max_rss_kb_any_process": r1.ru_maxrss,
        "lrat_bytes": summ.get("lrat_bytes"),
        "zst_bytes": summ.get("zst_bytes"),
        "lemmas": summ.get("lemmas"),
        "hints": summ.get("hints"),
        "zstd_warnings": summ.get("zstd_warnings"),
        "base_formulas_built": summ.get("base_formulas_built"),
        "toolchain": toolchain,
        "lean_version": lean_version,
        "zstd_version": zstd_version,
        "command": " ".join(
            [
                "lean-check/.lake/build/bin/qdcheck",
                str(a.n),
                str(a.k),
                rel(a.certdir),
                "--jobs",
                str(a.jobs),
                "--log",
                rel(a.log),
            ]
        ),
        "paths_relative_to": "the queen-domination checkout",
        "started": started,
        "finished": time.strftime("%Y-%m-%dT%H:%M:%S%z"),
        "log": rel(a.log),
        "log_sha256": sha(a.log),
        "stdout": rel(out_path),
        "qdcheck_sha256": binary_sha,
        "source_sha256": src,
    }
    with open(a.summary, "w") as f:
        json.dump(result, f, indent=1)
        f.write("\n")
    print(final)
    sys.exit(rc)


main()
