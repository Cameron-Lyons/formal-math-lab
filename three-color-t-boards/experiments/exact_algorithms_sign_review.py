#!/usr/bin/env python3
"""Independent tuple-polynomial/finite-field audit; never runs a solver."""

import collections
import hashlib
import itertools
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent


def add(a, b, scale=1):
    out = a.copy()
    for m, c in b.items():
        v = (out.get(m, 0) + scale * c) % 3
        if v:
            out[m] = v
        else:
            out.pop(m, None)
    return out


def mul(a, b, reduce=False):
    out = {}
    for x, c in a.items():
        for y, d in b.items():
            e = dict(x)
            for v, p in y:
                e[v] = e.get(v, 0) + p
            if reduce:
                e = {v: 1 + (p - 1) % 2 for v, p in e.items() if p}
            m = tuple(sorted(e.items()))
            out = add(out, {m: c * d})
    return out


def val(p, x):
    return sum(c * prod(pow(x[v], e, 3) for v, e in m) for m, c in p.items()) % 3


def prod(a):
    z = 1
    for x in a:
        z = z * x % 3
    return z


def parse(text):
    header, prime, body = text.split("\n", 2)
    n = len(header.split(","))
    assert header == ",".join(f"x{i + 1}" for i in range(n)) and prime == "3"
    polys = []
    for expr in body.strip().split(","):
        p = {}
        for term in re.findall(r"[+-]?[^+-]+", expr.replace("\n", "")):
            c = 1
            if term[0] == "-":
                c = -1
                term = term[1:]
            elif term[0] == "+":
                term = term[1:]
            e = {}
            for factor in term.split("*"):
                if factor.isdigit():
                    c *= int(factor)
                else:
                    match = re.fullmatch(r"x([1-9][0-9]*)(?:\^([0-9]+))?", factor)
                    assert match, factor
                    v = int(match[1]) - 1
                    assert v < n
                    e[v] = e.get(v, 0) + int(match[2] or 1)
            p = add(p, {tuple(sorted((v, k) for v, k in e.items() if k)): c})
        polys.append(p)
    return n, polys


def packed(rec):
    out = {}
    for c, word in rec["terms"]:
        v = int(word, 16)
        pairs = []
        i = 0
        while v:
            if v & 15:
                pairs.append((i, v & 15))
            v >>= 4
            i += 1
        out = add(out, {tuple(pairs): c})
    return out


def rename(p, perm):
    return {tuple(sorted((perm[v], e) for v, e in m)): c for m, c in p.items()}


def linear(f):
    return {((int(v), 1),): c for v, c in f.items()}


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    model = json.loads((HERE / "exact_f3_sign_model.json").read_text())
    source = json.loads((HERE / "exact_f3_translation_model.json").read_text())
    modulus = model["field_modulus_low_to_high"]
    assert modulus == [1, 0, 2, 2, 1, 1]

    def remainder(a, b):
        a = a[:]
        while a and a[-1] == 0:
            a.pop()
        while len(a) >= len(b):
            k = len(a) - len(b)
            c = a[-1]
            for i, v in enumerate(b):
                a[k + i] = (a[k + i] - c * v) % 3
            while a and a[-1] == 0:
                a.pop()
        return a

    for degree in [1, 2]:
        for low in itertools.product(range(3), repeat=degree):
            assert remainder(modulus, [*list(low), 1])

    def digits(a):
        return [(a // 3**i) % 3 for i in range(5)]

    def enc(v):
        return sum(a * 3**i for i, a in enumerate(v))

    def fmul(a, b):
        aa = digits(a)
        bb = digits(b)
        r = [0] * 9
        for i, c in enumerate(aa):
            for j, d in enumerate(bb):
                r[i + j] = (r[i + j] + c * d) % 3
        return enc(remainder(r, modulus))

    def fadd(a, b):
        return enc([(x + y) % 3 for x, y in zip(digits(a), digits(b), strict=False)])

    def fpow(a, k):
        out = 1
        while k:
            if k & 1:
                out = fmul(out, a)
            a = fmul(a, a)
            k //= 2
        return out

    for a in range(243):
        assert fpow(a, 243) == a
        if a:
            assert fpow(a, 242) == 1
    embedding = [enc(x) for x in model["embedding_basis_by_role"]]
    assert embedding == [3, 10, 40, 1]
    selector = {
        tuple((i, e) for i, e in enumerate(t["exponents"]) if e): t["coefficient"]
        for t in model["selector_terms"]
    }
    # Independently expand the five Frobenius-conjugate linear forms overF243.
    norm = {(): 1}
    for k in range(5):
        q = {}
        for mon, c in norm.items():
            for i, b in enumerate(embedding):
                e = dict(mon)
                e[i] = e.get(i, 0) + 1
                m = tuple(sorted(e.items()))
                v = fadd(q.get(m, 0), fmul(c, fpow(b, 3**k)))
                if v:
                    q[m] = v
                else:
                    q.pop(m, None)
        norm = q
    assert len(norm) == 38 and all(c in (1, 2) for c in norm.values())
    expected_norm = {
        tuple((i, e) for i, e in enumerate(exps) if e): c
        for c, exps in model["original_norm_homogeneous_terms"]
    }
    assert norm == expected_norm
    reduced = {}
    for m, c in norm.items():
        reduced = add(reduced, {tuple((v, 1 + (e - 1) % 2) for v, e in m): c})
    assert reduced == selector and len(selector) == 17
    images = []
    hist = collections.Counter()
    for point in itertools.product(range(3), repeat=4):
        a = 0
        for c, b in zip(point, embedding, strict=False):
            a = fadd(a, fmul(c, b))
        images.append(a)
        h = val(selector, point)
        assert fpow(a, 121) == h
        assert (h == 0) == (point == (0, 0, 0, 0))
        assert val(selector, tuple(-x % 3 for x in point)) == (-h) % 3
        hist[h] += 1
    assert len(set(images)) == 81 and hist == {0: 1, 1: 40, 2: 40}
    indicator = {(): 1}
    for i in range(4):
        indicator = mul(indicator, {(): 1, ((i, 2),): 2}, True)
    assert mul(selector, selector, True) == add({(): 1}, indicator, -1)
    # Recover canonical cell forms from adjacentprefix differences, independently.
    order = source["original_cell_order"]
    u = {int(j): linear(f) for j, f in source["normalized_prefix_linear_forms"].items()}
    forms = {cell: add(u[j], u.get(j - 1, {}), -1) for j, cell in enumerate(order)}
    assert (
        forms
        == {
            int(c): linear(f) for c, f in model["normalized_color_linear_forms"].items()
        }
        and forms[0] == {}
    )
    windows = [
        (r * r + c, (r + 1) ** 2 + c, (r + 1) ** 2 + c + 1, (r + 1) ** 2 + c + 2)
        for r in range(9)
        for c in range(2 * r + 1)
    ]
    assert (
        len(windows) == 81
        and list(windows[0]) == model["selector_placement_cells"][0]
        and list(windows[3]) == model["selector_placement_cells"][1]
    )
    delta = [
        add(forms[a], forms[b], -1)
        for a, b in zip(windows[0], windows[3], strict=False)
    ]
    composition = {}
    for mon, c in selector.items():
        q = {(): c}
        for i, e in mon:
            for _ in range(e):
                q = mul(q, delta[i], True)
        composition = add(composition, q)
    constraint = add(composition, {(): 2})
    assert len(constraint) == 180 and constraint == packed(
        model["selector_zero_polynomial"]
    )
    ns, base = parse((HERE / "exact_f3_translation_e3.ms").read_text())
    assert ns == 96 and len(base) == 176
    assert (
        sha(HERE / "exact_f3_translation_e3.ms")
        == model["source_augmented_input_sha256"]
    )
    assert (
        sha(HERE / "exact_f3_translation_model.json")
        == model["source_translation_model_sha256"]
    )
    for i in range(96):
        assert base[i] == {((i, 3),): 1, ((i, 1),): 2}
    expected = [
        *base,
        {((96, 3),): 1, ((96, 1),): 2},
        {((96, 2),): 1, (): 2},
        constraint,
    ]
    assert mul(expected[-2], {((96, 1),): 1}) == expected[-3]
    actual = {
        c: add({((95, 1),): 1}, mul(p, {((96, 1),): 1})) for c, p in forms.items()
    }
    assert actual == {
        int(c): packed(p)
        for c, p in model["original_color_bilinear_polynomials"].items()
    }
    assert actual[0] == {((95, 1),): 1}
    for p in base[96:]:
        assert (
            all(v < 95 for m in p for v, _ in m)
            and len({sum(e for _, e in m) % 2 for m in p}) == 1
        )
    checked = []
    for stem in ["exact_f3_sign_model", "exact_f3_sign_minfill"]:
        meta = json.loads((HERE / (stem + ".json")).read_text())
        n, polys = parse((HERE / (stem + ".ms")).read_text())
        assert n == 97 and len(polys) == 179
        perm = meta.get("old_index_to_new_index", list(range(97)))
        assert sorted(perm) == list(range(97)) and perm[95:] == [95, 96]
        assert polys == [rename(p, perm) for p in expected]
        assert {
            int(c): packed(p)
            for c, p in meta["original_color_bilinear_polynomials"].items()
        } == {c: rename(p, perm) for c, p in actual.items()}
        assert (
            meta["count_divisor"] == meta["count_multiplier"] == 1
            and meta["prefix"] == ""
            and meta["fixed_original_cells"] == []
            and not meta["exact_total_claimed"]
        )
        assert (
            meta["input_sha256"] == sha(HERE / (stem + ".ms"))
            and meta["variables"] == 97
            and meta["generators"] == 179
            and meta["domain_count"] == 97
        )
        fields = {
            next(v for v, e in next(m for m in p if sum(e for _, e in m) == 3))
            for p in polys
            if len(p) == 2 and any(len(m) == 1 and m[0][1] == 3 for m in p)
        }
        assert fields == set(range(97))
        checked.append(
            {
                "stem": stem,
                "input_sha256": sha(HERE / (stem + ".ms")),
                "all179_polynomials_match": True,
            }
        )
    boards = json.loads((HERE / "exact_structure_gauge_certificate.json").read_text())[
        "boards"
    ]
    tested = 0
    for fixture in boards:
        z = list(map(int, fixture["flat"]))
        assert len(z) == 100 and len({tuple(z[c] for c in w) for w in windows}) == 81
        a = z[0]
        D = [(v - a) % 3 for v in z]
        s = val(
            selector,
            [(D[x] - D[y]) % 3 for x, y in zip(windows[0], windows[3], strict=False)],
        )
        assert s in [1, 2]
        d = [s * x % 3 for x in D]
        pref = []
        acc = 0
        for cell in order:
            acc = (acc + d[cell]) % 3
            pref.append(acc)
        point = [pref[i] for i in source["free_normalized_prefix_variables"]] + [a, s]
        assert len(point) == 97 and all(val(p, point) == d[c] for c, p in forms.items())
        assert (
            all(val(p, point) == z[c] for c, p in actual.items())
            and val(constraint, point) == 0
        )
        if tested < 5:
            assert all(val(p, point) == 0 for p in expected)
        recovered = []
        for aa, ss in itertools.product(range(3), (1, 2)):
            pt = [*point[:95], aa, ss]
            zz = [val(actual[c], pt) for c in range(100)]
            assert zz == [(aa + ss * x) % 3 for x in d]
            dd = [(x - zz[0]) % 3 for x in zz]
            assert (
                val(
                    selector,
                    [
                        (dd[x] - dd[y]) % 3
                        for x, y in zip(windows[0], windows[3], strict=False)
                    ],
                )
                == ss
            )
            recovered.append(tuple(zz))
        assert len(set(recovered)) == 6
        tested += 1
    # Check the actual adapter definitions with all source bytes and scopes.
    import exact_msolve_backend as backend

    valid = {
        "prime": 3,
        "ternary_native_field": True,
        "native_translation": True,
        "native_e3": True,
        "native_sign": True,
    }
    adapters = []
    for ordername, stem in [
        (None, "exact_f3_sign_model"),
        ("minimum-fill", "exact_f3_sign_minfill"),
    ]:
        text, meta = backend.definitions(**valid, native_order=ordername)
        assert text == (HERE / (stem + ".ms")).read_text()
        assert (
            meta["variables"] == 97
            and meta["generators"] == 179
            and meta["count_divisor"] == meta["count_multiplier"] == 1
        )
        assert (
            not meta.get("original_color_linear_forms")
            and len(meta["original_color_bilinear_polynomials"]) == 100
        )
        assert (
            meta["offset_variable_index"] == 95
            and meta["sign_variable_index"] == 96
            and not meta["prefix"]
            and not meta["extension_variable"]
        )
        assert (
            not meta["standard_basis_complete"] and meta["status"] == "PREPARED_NOT_RUN"
        )
        adapters.append(ordername or "natural")
    bad = [
        {"ternary_native_field": False},
        {"prime": 2},
        {"prime": 29},
        {"native_translation": False},
        {"native_e3": False},
        {"prefix": "0"},
        {"binary": True},
        {"fixture": "domain"},
        {"pivot_order": True},
        {"ternary_reduced": "all"},
        {"ternary_prefix_sums": "all"},
        {"histogram_e2": True},
        {"prefix_field_equations": True},
        {"histogram_e4": True},
        {"native_order": "invalid"},
    ]
    for changes in bad:
        try:
            backend.definitions(**dict(valid, **changes))
        except ValueError:
            pass
        else:
            raise AssertionError(changes)
    result = {
        "status": "PASS",
        "scope": "independent finitefield/tuple-polynomial and adapter audit; no solver",
        "irreducibility_divisors": 12,
        "field_elements": 243,
        "selector_inputs": 81,
        "selector_histogram": dict(hist),
        "ordinary_norm_terms": len(norm),
        "selector_terms": len(selector),
        "expanded_constraint_terms": len(constraint),
        "models": checked,
        "bilinear_reconstructions": 100,
        "known_board_roundtrips": tested,
        "affine_palette_reconstructions": 6 * tested,
        "all179_polynomials_evaluated_on_boards": 5,
        "adapter_variants": adapters,
        "invalid_adapter_scopes": len(bad),
        "count_divisor": 1,
        "count_multiplier": 1,
        "reviewer_source_sha256": sha(Path(__file__)),
        "generator_imported": False,
        "full_solver_runs": 0,
    }
    (HERE / "exact_algorithms_sign_review.json").write_text(
        json.dumps(result, indent=2) + "\n"
    )
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
