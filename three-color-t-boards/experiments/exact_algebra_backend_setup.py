#!/usr/bin/env python3
"""Extract checksum-verified repository packages locally; never install system packages."""

import hashlib
import json
import subprocess
import tarfile
import urllib.request
from pathlib import Path

ROOT = Path(__file__).resolve().parent
DEST = ROOT / "exact_algebra_backend_root"
PACKAGES = ROOT / "exact_algebra_backend_packages"
MANIFEST = ROOT / "exact_algebra_backend_packages.json"


def read_desc(text):
    chunks = text.strip().split("\n\n")
    return {c.splitlines()[0].strip("%"): c.splitlines()[1:] for c in chunks}


def main():
    if MANIFEST.exists():
        manifest = json.loads(MANIFEST.read_text())
    else:
        output = subprocess.run(
            ["pacman", "-Sp", "--print-format", "%n %v %l", "singular"],
            capture_output=True,
            text=True,
            check=True,
        ).stdout
        wanted = [line.split(" ", 2) for line in output.splitlines() if line.strip()]
        metadata = {}
        for database in Path("/var/lib/pacman/sync").glob("*.db"):
            with tarfile.open(database) as archive:
                for member in archive:
                    if member.name.endswith("/desc"):
                        extracted = archive.extractfile(member)
                        if extracted is None:
                            continue
                        desc = read_desc(extracted.read().decode())
                        name = desc.get("NAME", [""])[0]
                        if any(name == w[0] for w in wanted):
                            metadata[name] = desc
        manifest = []
        for name, version, url in wanted:
            desc = metadata[name]
            assert desc["VERSION"] == [version]
            manifest.append(
                {
                    "name": name,
                    "version": version,
                    "url": url,
                    "sha256": desc["SHA256SUM"][0],
                    "archive": str((PACKAGES / desc["FILENAME"][0]).relative_to(ROOT)),
                    "repository": "configured official Arch repository",
                }
            )
    DEST.mkdir(exist_ok=True)
    PACKAGES.mkdir(exist_ok=True)
    for record in manifest:
        name, version, url = (record[k] for k in ("name", "version", "url"))
        expected = record["sha256"]
        target = ROOT / record["archive"]
        if not target.exists():
            print("Downloading", name, version, flush=True)
            urllib.request.urlretrieve(url, target)
        actual = hashlib.sha256(target.read_bytes()).hexdigest()
        if actual != expected:
            raise RuntimeError("Checksum mismatch: " + str(target))
        subprocess.run(["bsdtar", "-xf", str(target), "-C", str(DEST)], check=True)
    MANIFEST.write_text(json.dumps(manifest, indent=2) + "\n")
    print("Extracted locally:", DEST, flush=True)


if __name__ == "__main__":
    main()
