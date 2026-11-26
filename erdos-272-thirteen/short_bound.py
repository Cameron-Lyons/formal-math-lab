"""Check the finite incidence and rank computations in the proof for n = 13.

Run with Python 3.10 or later. Only the standard library is used.
"""

from itertools import combinations

N = 13
FULL = (1 << N) - 1


def progressions():
    result = set()
    for start in range(N):
        for step in range(1, N + 1):
            mask = 0
            for i in range(start, N, step):
                mask |= 1 << i
                result.add(mask)
    return result


def rank_mod_two(rows):
    pivots = {}
    for value in rows:
        while value:
            lead = value.bit_length() - 1
            if lead not in pivots:
                pivots[lead] = value
                break
            value ^= pivots[lead]
    return len(pivots)


def verify_short_bound(aps):
    seven = [p for p in aps if p.bit_count() == 7]
    short = [a for a in range(1, FULL + 1) if all(a & p != p for p in seven)]

    # The empty coordinate has weight +1. The five-term APs have weight 0.
    weight = [1, -1, 1, -1, -1, 0, -1]
    coords = [0]
    coords.extend(
        sorted(p for p in aps if p.bit_count() <= 6 and weight[p.bit_count()])
    )
    positive = sum(weight[p.bit_count()] > 0 for p in coords)
    ap_rows = {}
    for a in short:
        inside = [j for j, p in enumerate(coords) if a & p == p]
        diagonal = sum(weight[coords[j].bit_count()] for j in inside)
        if a in aps:
            assert diagonal == 0
            if a.bit_count() >= 2:
                ap_rows[a] = sum(1 << j for j in inside)
        else:
            assert diagonal > 0

    # A pairwise-intersecting family of pairs lies in a triangle or a star.
    for triple in combinations(range(N), 3):
        t = sum(1 << i for i in triple)
        rows = [row for p, row in ap_rows.items() if p.bit_count() != 2 or p & t == p]
        assert rank_mod_two(rows) == len(rows)

    # In the star case there is a member b of the original family missing
    # the centre. Any short AP in the family must have AP intersection with b.
    # If b is itself one of these APs, the same test retains it.
    for i in range(N):
        centre = 1 << i
        allowed = [
            (p, row) for p, row in ap_rows.items() if p.bit_count() != 2 or p & centre
        ]
        for b in range(1, FULL + 1):
            if b & centre:
                continue
            rows = [row for p, row in allowed if p & b in aps]
            assert rank_mod_two(rows) == len(rows)

    assert len(seven) == 8 and FULL - len(short) == 300 and positive == 79
    print(f"{len(short)} short nonempty masks, {FULL - len(short)} long masks")
    print(f"{len(coords)} nonzero coordinates, {positive} positive coordinates")
    print("All tested short AP row families have full rank over F_2")


def assign_triple(progression, triples, match, seen):
    """Find an augmenting path for this AP in the AP-to-triple matching."""
    for triple in triples:
        if triple & progression != triple or triple in seen:
            continue
        seen.add(triple)
        if triple not in match or assign_triple(match[triple], triples, match, seen):
            match[triple] = progression
            return True
    return False


def verify_star_bound(aps):
    # Direct finite check of the starred bound; independent of the general theorem.
    deficits = []
    for i in range(N):
        centre = 1 << i
        triples = [
            t
            for t in range(1, FULL + 1)
            if t & centre and t.bit_count() == 3 and t not in aps
        ]
        hull = dict.fromkeys(triples, FULL)
        for t in triples:
            for p in aps:
                if t & p == t:
                    hull[t] &= p

        # Such a triple cannot occur in any other member: an AP intersection
        # containing t would also have to contain every point in hull[t].
        for a in range(1, FULL + 1):
            if a & centre and a.bit_count() >= 4 and a not in aps:
                assert any(a & t == t and a & hull[t] != hull[t] for t in triples)

        big_aps = sorted(p for p in aps if p & centre and p.bit_count() >= 4)
        match = {}

        for p in big_aps:
            assign_triple(p, triples, match, set())
        assert len(set(match.values())) == len(match)
        assert all(t & p == t for t, p in match.items())
        deficits.append(len(big_aps) - len(match))
    assert max(deficits) == 3
    print("Unmatched large APs by star centre:", deficits)


def verify_construction(aps):
    # Zero-based centre 6 represents the element 7.
    centre = 6
    family = {a for a in range(1, FULL + 1) if a & (1 << centre) and a.bit_count() <= 3}

    def offsets(d, steps):
        return sum(1 << (centre + d * j) for j in steps)

    for d in (1, 2, 3):
        family.remove(offsets(d, [-2, 0, 1]))
        family.remove(offsets(d, [-1, 0, 2]))
        for steps in [range(-2, 3), range(-2, 2), range(-1, 3)]:
            family.add(offsets(d, steps))
    assert len(family) == 82
    assert all(a & b in aps for a, b in combinations(family, 2))
    print("82-set construction verified on all 3321 pairs")


if __name__ == "__main__":
    if not __debug__:
        raise SystemExit("Run with assertions enabled (remove -O or PYTHONOPTIMIZE).")
    aps = progressions()
    verify_short_bound(aps)
    verify_star_bound(aps)
    verify_construction(aps)
