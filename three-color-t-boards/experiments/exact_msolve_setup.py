#!/usr/bin/env python3
"""Reproduce the locally extracted, checksum-pinned stock msolve package."""

import hashlib
import json
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent
DEST = ROOT / "exact_msolve_tools"


def main():
    record = json.loads((DEST / "package.json").read_text())
    archive = DEST / "msolve-0.11.0-1-x86_64.pkg.tar.zst"
    if not archive.exists():
        temporary = archive.with_suffix(archive.suffix + ".part")
        subprocess.run(
            [
                "curl",
                "--fail",
                "--location",
                "--max-time",
                "60",
                "--output",
                str(temporary),
                record["url"],
            ],
            check=True,
        )
        temporary.rename(archive)
    if hashlib.sha256(archive.read_bytes()).hexdigest() != record["archive_sha256"]:
        raise ValueError("stock msolve archive checksum mismatch")
    subprocess.run(
        [
            "bsdtar",
            "-xf",
            str(archive),
            "-C",
            str(DEST),
            "usr/bin/msolve",
            "usr/lib",
            "usr/include",
        ],
        check=True,
    )
    executable = DEST / "usr/bin/msolve"
    if (
        hashlib.sha256(executable.read_bytes()).hexdigest()
        != record["executable_sha256"]
    ):
        raise ValueError("stock msolve executable checksum mismatch")
    link = DEST / "msolve"
    if not link.exists():
        link.symlink_to("usr/bin/msolve")
    print("Verified local stock msolve 0.11.0-1; no system installation performed.")
    print("Runtime dependencies are supplied by exact_algebra_backend_setup.py.")


if __name__ == "__main__":
    main()
