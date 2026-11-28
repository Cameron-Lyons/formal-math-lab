"""Verify seven-color certificates for punctured subsets of {1,...,78}."""

import argparse
import subprocess
from pathlib import Path


def canonical(word):
    names = {}
    return "".join(names.setdefault(color, str(len(names))) for color in word)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--check-repairs",
        type=Path,
        metavar="EXECUTABLE",
        help="also run the compiled repair verifier on the certificate words and their fillings",
    )
    parser.add_argument("--radius", type=int, default=14)
    args = parser.parse_args()
    n = 78
    positions = range(n)
    progressions = [
        (a, a + d, a + 2 * d, a + 3 * d)
        for a in positions
        for d in range(1, (n - 1 - a) // 3 + 1)
    ]
    words = Path(__file__).with_name("colorings.txt").read_text().splitlines()
    certified = set()
    seeds = set()
    for number, word in enumerate(words, 1):
        if len(word) != n or set(word) - set("0123456"):
            raise ValueError(f"Malformed coloring on line {number}")
        for oriented in (word, word[::-1]):
            bad = [p for p in progressions if len({oriented[i] for i in p}) < 3]
            holes = {i for i in positions if all(i in p for p in bad)}
            certified.update(holes)
            if args.check_repairs and oriented == word:
                seeds.add(canonical(word))
                for i in holes:
                    for color in "0123456":
                        seeds.add(canonical(word[:i] + color + word[i + 1 :]))
    singles = [i + 1 for i in positions if i not in certified]
    if singles:
        raise ValueError(f"Uncertified one-position deletions: {singles}")
    print(
        f"{len(words)} colorings, both orientations, {len(progressions)} progressions"
    )
    print(f"All {n} one-position deletions certified")
    if args.check_repairs:
        for seed in sorted(seeds):
            result = subprocess.run(
                [args.check_repairs.resolve(), str(args.radius), seed],
                check=True,
                capture_output=True,
                text=True,
            )
            if not result.stdout.rstrip().endswith("valid_repair=no"):
                raise RuntimeError(
                    f"Repair search for {seed} returned\n{result.stdout}"
                )
        print(
            f"No valid repair within {args.radius} changes of any of the {len(seeds)} words"
        )


if __name__ == "__main__":
    main()
