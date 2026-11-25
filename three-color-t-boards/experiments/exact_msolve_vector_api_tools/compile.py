#!/usr/bin/env python3
import hashlib
import json
import os
import shutil
import subprocess
import time
from pathlib import Path

R = Path(__file__).resolve().parent
M = json.loads((R / "source.json").read_text())
S = Path(M["source_directory"])
attempt = 1
while (R / f"compile_pass{attempt}.log").exists():
    attempt += 1
env = dict(os.environ, **M["build_environment"])
start = time.monotonic()
with (R / f"compile_pass{attempt}.log").open("x") as out:
    p = subprocess.run(
        ["make", "-j1"],
        cwd=S,
        env=env,
        stdout=out,
        stderr=subprocess.STDOUT,
        check=False,
    )
record = {
    "attempt": attempt,
    "returncode": p.returncode,
    "wall_seconds": time.monotonic() - start,
}
(R / f"compile_pass{attempt}.json").write_text(json.dumps(record, indent=2) + "\n")
print(record)
if p.returncode == 0:
    shutil.copy2(S / "msolve", R / "msolve")
    M["status"] = "UNVALIDATED_BYTE_API_CANDIDATE"
    M["executable"] = str(R / "msolve")
    M["executable_sha256"] = hashlib.sha256((R / "msolve").read_bytes()).hexdigest()
    (R / "source.json").write_text(json.dumps(M, indent=2) + "\n")
    print(M["executable_sha256"])
raise SystemExit(p.returncode)
