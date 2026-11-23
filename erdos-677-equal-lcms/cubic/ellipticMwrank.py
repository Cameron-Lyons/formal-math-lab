"""Recompute the full rational bases used in ellipticHeight.py with mwrank."""
import os
import re
import subprocess

from ellipticHeight import MODELS


def main():
    program = os.environ.get("MWRANK", "mwrank")
    print(subprocess.check_output([program, "-V"], text=True).strip())
    for u, v, _, (a2, a4, a6), generators in MODELS:
        coeff = [0, a2, 0, a4, a6]
        result = subprocess.run([program, "-q", "-v", "1", "-p", "180", "-S", "-1"],
                                input=f"{coeff}\n", capture_output=True,
                                text=True, check=True)
        output = result.stdout + result.stderr
        assert "The rank and full Mordell-Weil basis have been determined unconditionally." in output
        points = re.findall(r"Generator \d+ is \[(-?\d+):(-?\d+):(\d+)\]", output)
        assert all(z == "1" for x, y, z in points)
        assert [(int(x), int(y)) for x, y, z in points] == generators
        print(f"{u}/{v}: full Mordell-Weil basis {generators}")


if __name__ == "__main__":
    main()
