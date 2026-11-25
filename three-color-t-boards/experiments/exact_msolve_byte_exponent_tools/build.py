#!/usr/bin/env python3
import hashlib
import json
import os
import shutil
import subprocess
import time
from pathlib import Path

R = Path(__file__).resolve().parent
m = json.loads((R / "source.json").read_text())
s = Path(m["source_directory"])
env = dict(os.environ, **m["build_environment"])
for name, command in zip(
    ["autogen", "configure", "make"], m["build_commands"], strict=False
):
    start = time.monotonic()
    with (R / (name + ".log")).open("w") as log:
        p = subprocess.run(
            command, cwd=s, env=env, stdout=log, stderr=subprocess.STDOUT, check=False
        )
    m[name] = {"returncode": p.returncode, "wall_seconds": time.monotonic() - start}
    (R / "source.json").write_text(json.dumps(m, indent=2) + "\n")
    print(name, p.returncode, flush=True)
    assert p.returncode == 0
shutil.copy2(s / "msolve", R / "msolve")
m["executable"] = str(R / "msolve")
m["executable_sha256"] = hashlib.sha256((R / "msolve").read_bytes()).hexdigest()
m["version_output"] = subprocess.check_output(
    [str(R / "msolve"), "-V"], text=True, env=env
).strip()
(R / "source.json").write_text(json.dumps(m, indent=2) + "\n")
print(m["executable_sha256"])
