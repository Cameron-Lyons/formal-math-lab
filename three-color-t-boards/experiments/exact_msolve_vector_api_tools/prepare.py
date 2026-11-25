#!/usr/bin/env python3
import hashlib
import json
import subprocess
import tarfile
from pathlib import Path

R = Path(__file__).resolve().parent
E = R.parent
B = E / "exact_msolve_byte_exponent_tools"
base = json.loads((B / "source.json").read_text())
S = R / Path(base["source_directory"]).name
assert not S.exists()
assert (
    hashlib.sha256((B / "msolve").read_bytes()).hexdigest() == base["executable_sha256"]
)
with tarfile.open(base["source_archive"]) as t:
    t.extractall(R, filter="data")
patches = base["predecessor_patches"] + [
    {
        "path": str(B / "checked-byte-exponents.patch"),
        "sha256": base["checked_byte_patch_sha256"],
    }
]
for item in patches:
    p = Path(item["path"])
    assert hashlib.sha256(p.read_bytes()).hexdigest() == item["sha256"]
    subprocess.run(
        ["patch", "-p1", "-i", str(p)], cwd=S, check=True, capture_output=True
    )
for path in (Path(base["source_directory"]) / "src").rglob("*"):
    if path.is_file() and path.suffix in (".c", ".h"):
        rel = path.relative_to(base["source_directory"])
        if str(rel) == "src/msolve/msolve-version.h":
            continue  # configure-generated header
        assert (S / rel).read_bytes() == path.read_bytes(), rel
env = base["build_environment"].copy()
env["CFLAGS"] = "-O2 -g0 -Werror=incompatible-pointer-types -Werror=int-conversion"
metadata = {
    k: base[k]
    for k in [
        "repository",
        "tag",
        "commit",
        "archive_sha256",
        "source_archive",
        "compiler_version",
        "runtime_library_sha256",
    ]
}
metadata.update(
    status="UNBUILT_API_REFACTOR",
    source_directory=str(S),
    predecessor_patches=patches,
    baseline_executable=str(B / "msolve"),
    baseline_executable_sha256=base["executable_sha256"],
    build_environment=env,
    build_commands=[
        ["./autogen.sh"],
        ["./configure", "--disable-shared", "--enable-static", "--disable-openmp"],
        ["make", "-j1"],
    ],
    physical_representation="unchanged one byte per logical exponent lane",
    nibble_packing=False,
)
(R / "source.json").write_text(json.dumps(metadata, indent=2) + "\n")
print(S)
