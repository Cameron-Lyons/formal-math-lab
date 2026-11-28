"""Prove a lower bound for the number of progressions that can force eight colors."""

from pathlib import Path


def verify(path):
    progressions = [
        (a, a + d, a + 2 * d, a + 3 * d)
        for d in range(1, 26)
        for a in range(78 - 3 * d)
    ]
    loads = [0] * len(progressions)
    total = 0
    for row in path.read_text().splitlines():
        weight, word = row.split()
        weight = int(weight)
        if weight <= 0 or len(word) != 78 or set(word) - set("0123456"):
            raise ValueError(f"invalid certificate row: {row}")
        for orientation in (word, word[::-1]):
            total += weight
            for i, (a, b, c, d) in enumerate(progressions):
                if (
                    len(
                        {orientation[a], orientation[b], orientation[c], orientation[d]}
                    )
                    < 3
                ):
                    loads[i] += weight
    if total == 0:
        raise ValueError("empty certificate")
    maximum = max(loads)
    if maximum == 0:
        print("Every witness satisfies all 975 progressions.")
        return len(progressions)
    # For m selected progressions, at most m * maximum weight can fail any
    # one of them. If this is less than total, some word satisfies them all.
    guaranteed = (total - 1) // maximum
    print(f"Total weight {total}, maximum weight failing one progression {maximum}.")
    print(f"Every family of at most {guaranteed} progressions admits seven colors.")
    return guaranteed


if __name__ == "__main__":
    if verify(Path(__file__).with_name("progression_families.txt")) < 330:
        raise SystemExit("certificate falls short of the claimed 330 progressions")
