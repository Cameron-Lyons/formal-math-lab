"""Discover sampled binary-cap families at a palindromic row-five pivot.

Each group records a row6_sample with a modulus, a list of residues and a salt.
The C++ search admits a row-six word when either orientation hashes to a listed
residue. Every saved board is an explicit witness, independently of the sampling.
"""
import argparse
from functools import cache
from itertools import product
import json
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory

from verify_splice import split_rows


ROOT = Path(__file__).resolve().parent


@cache
def binary_caps():
    from reproduce_splice import upper_sections

    binary_patterns = set(product("01", repeat=4))
    caps = [cap for bottom in product("01", repeat=9)
            for cap in upper_sections("".join(bottom), binary_patterns)]
    if len(set(caps)) != 168 or len(caps) != 168:
        raise ValueError("unexpected binary upper-cap count")
    return tuple(sorted(caps))


def seam_mask(cap, pivot):
    codes = {int(color + pivot[j:j+3], 3) for j, color in enumerate(cap[16:])}
    return sum(1 << code for code in codes) if len(codes) == 9 else None


@cache
def canonical_groups(pivot):
    if len(pivot) != 11 or set(pivot) != set("012") or pivot != pivot[::-1]:
        raise ValueError("expected an eleven-digit palindromic pivot with all three colors")
    if any("2" not in pivot[j:j+3] for j in range(9)):
        return {}
    groups = {}
    for cap in binary_caps():
        mask = seam_mask(cap, pivot)
        if mask is None:
            continue
        reflected = "".join(row[::-1] for row in split_rows(cap, 0, 5))
        other = seam_mask(reflected, pivot)
        if other is None or cap == reflected:
            raise ValueError("unexpected reflection of a valid binary cap")
        # Compare masks first so that a whole reflected class can be represented
        # by one search. For an invariant mask choose one cap from each pair.
        if (mask, cap) < (other, reflected):
            groups.setdefault(mask, []).append(cap)
    return groups


def find_tails(binary, prefix, sample):
    modulus, residues, salt = (sample[key] for key in ("modulus", "residues", "salt"))
    if (type(modulus) is not int or not 0 < modulus < 2**32 or
            type(salt) is not int or not 0 <= salt < 2**32 or
            not isinstance(residues, list) or not residues or
            any(type(value) is not int or not 0 <= value < modulus for value in residues) or
            residues != sorted(set(residues))):
        raise ValueError("invalid row6_sample parameters")
    result = subprocess.run([binary, prefix, "0", str(modulus),
                             ",".join(map(str, residues)), str(salt)],
                            text=True, stdout=subprocess.PIPE, check=True)
    lines = result.stdout.splitlines()
    if any(len(line) != 100 or not line.startswith(prefix) for line in lines):
        raise ValueError("search output disagrees with its six-row prefix")
    return [line[36:] for line in lines]


def replay_group(binary, group):
    pivot, prefix = group["pivot"], group["prefix"]
    groups = canonical_groups(pivot)
    if (len(prefix) != 36 or prefix[25:] != pivot or
            prefix[:25] not in group["caps"] or
            groups.get(seam_mask(prefix[:25], pivot)) != group["caps"]):
        raise ValueError("sampled group disagrees with its canonical upper caps")
    if find_tails(binary, prefix, group["row6_sample"]) != group["tails"]:
        raise ValueError("sampled lower tails differ from the certificate")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("pivot", help="eleven ternary digits")
    parser.add_argument("output", type=Path)
    parser.add_argument("--modulus", type=int, default=64)
    parser.add_argument("--residues", type=int, nargs="+", default=[0])
    parser.add_argument("--salt", type=int, default=847235)
    args = parser.parse_args()
    sample = dict(modulus=args.modulus, residues=sorted(set(args.residues)), salt=args.salt)
    groups = []
    with TemporaryDirectory() as work:
        binary = Path(work) / "splice_search"
        subprocess.run(["c++", "-O3", "-std=c++23", "-Wall", "-Wextra", "-Wpedantic", "-Werror", str(ROOT / "splice_search.cpp"),
                        "-o", str(binary)], check=True)
        for caps in sorted(canonical_groups(args.pivot).values(), key=lambda items: items[0]):
            prefix = caps[0] + args.pivot
            tails = find_tails(binary, prefix, sample)
            if tails:
                groups.append(dict(prefix=prefix, pivot=args.pivot, caps=caps,
                                   tails=tails, row6_sample=sample))
    args.output.write_text(json.dumps(dict(cut=5, groups=groups), indent=2) + "\n")


if __name__ == "__main__":
    main()
