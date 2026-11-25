#!/usr/bin/env python3
"""Compare the Lean transcription of the CNF encoder (lean-sat/QueenDomSat) with code/frame/enc.py and
code/frame/geom.py.  No third-party packages.  Exit status 0 iff every comparison succeeds.

usage:  cd lean-sat && lake build && python3 -I scripts/compare_enc.py [options]

Groups of checks (every formula is compared by the SHA-256 of its complete DIMACS text):
  (i)   ALL cases of geom.cases_by_frame(n, k) for the small boards SMALL: `dumpcnf --batch` against
        enc.dimacs(B, *enc.case_extra(B, case)).
  (ii)  a stratified random sample (fixed seed, at least --samples cases) of each board of LARGE: every
        (box shape, deficit vector) class that occurs in the case list is represented (by three cases if
        it has that many), box shape being "square" (ml+mr == mb+mt), "w>h" or "h>w".
  (iii) the hashes of the sampled cases against the hashes RECORDED by the original runs
        (data/frame/d_<n>_<k>.jsonl.xz, field cnf_sha256), where such a file exists.
  (iv)  `listcases n k` against geom.cases_by_frame(n, k) (small boards, (26, 13) and (32, 16)) and against
        run_cases48.cases_fast(n, k) (the same list, enumerated faster; the larger boards, for which
        geom.cases_by_frame takes very long).
  (v)   single cases: `dumpcnf n k <case>` (stdout) against enc.py, and `dumpcnf --std`: the formula
        converted by QueenDomSat.caseCNF/toCNF to Std.Sat.CNF Nat and printed by Std.Sat.CNF.dimacs has the
        same clauses, in the same order, as the text of enc.py.
  (vi)  the hashes recorded so far by the (48, 24) run (runs/d_48_24.jsonl, read only), if it is there.
  --full: in addition ALL cases of the boards of FULL against the recorded hashes (Lean only).
  --all N,K (repeatable): in addition ALL cases of the board (N, K): `dumpcnf --stream` against enc.py.
"""

import argparse
import contextlib
import hashlib
import json
import lzma
import os
import random
import shutil
import subprocess
import sys
import time

sys.dont_write_bytecode = True  # do not write __pycache__ into code/frame

HERE = os.path.dirname(os.path.abspath(__file__))
PKG = os.path.dirname(HERE)
ROOT = os.path.dirname(PKG)
FRAME = os.path.join(ROOT, "code", "frame")
DATA = os.path.join(ROOT, "data", "frame")
BIN = os.path.join(PKG, ".lake", "build", "bin")
DUMP = os.path.join(BIN, "dumpcnf")
LIST = os.path.join(BIN, "listcases")
sys.path.insert(0, FRAME)
import enc  # noqa: E402
import geom  # noqa: E402
import run_cases48  # noqa: E402

SMALL = [
    (4, 2),
    (6, 3),
    (8, 4),
    (10, 5),
    (12, 6),
    (5, 3),
    (7, 4),
    (9, 5),
    (11, 5),
    (13, 7),
    (15, 8),
]
LARGE = [(32, 16), (35, 18), (46, 23), (48, 24)]
LISTS_SLOW = [
    (26, 13),
    (32, 16),
]  # large boards for which geom.cases_by_frame is still fast enough
LISTS_FAST = [(35, 18), (46, 23), (48, 24)]  # compared with run_cases48.cases_fast only
RECORDED = {
    (26, 13): ["d_26_13.jsonl.xz"],
    (32, 16): ["d_32_16.jsonl.xz"],
    (35, 18): ["d_35_18.jsonl.xz", "d_35_18_sq.jsonl.xz"],
    (46, 23): ["d_46_23.jsonl.xz"],
}
MUST_BE_RECORDED = [
    (32, 16),
    (46, 23),
]  # every sampled case of these boards must have a recorded hash
FULL = [(26, 13), (32, 16), (46, 23)]
RUN48 = os.path.join(ROOT, "runs", "d_48_24.jsonl")

FAIL = []  # messages of failed comparisons
SUMMARY = []  # one line per group


def note_fail(msg):
    FAIL.append(msg)
    if len(FAIL) <= 40:
        print("  MISMATCH: " + msg, flush=True)


def tag(case):
    return "_".join(map(str, case))


def shape(case):
    p, q = case[0] + case[1], case[2] + case[3]  # w = n-1-p, h = n-1-q
    return "square" if p == q else ("w>h" if p < q else "h>w")


class PyEnc:
    """enc.py, keeping only the Base of the current deficit vector"""

    def __init__(self, n, k):
        self.n, self.k, self.dv, self.B = n, k, None, None

    def sha(self, case):
        dv = tuple(case[4:])
        if dv != self.dv:
            self.B = None
            self.B = enc.Base(self.n, self.k, dv)
            self.dv = dv
        extra, nv = enc.case_extra(self.B, tuple(case))
        return enc.sha(enc.dimacs(self.B, extra, nv))

    def text(self, case):
        self.sha(case)
        extra, nv = enc.case_extra(self.B, tuple(case))
        return enc.dimacs(self.B, extra, nv), nv


def lean_batch(n, k, cases, tmp):
    """`dumpcnf --batch n k OUTDIR` on the given cases; returns {case: sha256 of the file}"""
    out = os.path.join(tmp, f"batch_{n:d}_{k:d}")
    if os.path.exists(out):
        shutil.rmtree(out)
    inp = "".join(" ".join(map(str, c)) + "\n" for c in cases)
    r = subprocess.run(
        [DUMP, "--batch", str(n), str(k), out],
        input=inp,
        text=True,
        capture_output=True,
        check=False,
    )
    if r.returncode != 0:
        raise SystemExit(f"dumpcnf --batch failed: {r.stderr}")
    res = {}
    for c in cases:
        f = os.path.join(out, tag(c) + ".cnf")
        with open(f, "rb") as fh:
            res[tuple(c)] = hashlib.sha256(fh.read()).hexdigest()
        os.remove(f)
    left = os.listdir(out)
    if left:
        note_fail(f"dumpcnf --batch {n:d} {k:d} wrote unexpected files: {left[:5]}")
    shutil.rmtree(out)
    return res


def lean_stream(n, k, cases, tmp):
    """`dumpcnf --stream n k` on the given cases; yields (case, sha256 of the text)"""
    lf = os.path.join(tmp, f"cases_{n:d}_{k:d}.txt")
    with open(lf, "w") as f:
        f.write("".join(" ".join(map(str, c)) + "\n" for c in cases))
    with open(lf) as fin:
        p = subprocess.Popen(
            [DUMP, "--stream", str(n), str(k)], stdin=fin, stdout=subprocess.PIPE
        )
        assert p.stdout is not None
        for c in cases:
            hdr = p.stdout.readline().split()
            if len(hdr) != 3 or hdr[0] != b"c" or hdr[1].decode() != tag(c):
                p.kill()
                raise SystemExit(
                    f"dumpcnf --stream: unexpected header {hdr!r} for case {tag(c)}"
                )
            nb = int(hdr[2])
            h = hashlib.sha256()
            while nb:
                blk = p.stdout.read(min(nb, 1 << 22))
                if not blk:
                    p.kill()
                    raise SystemExit("dumpcnf --stream: truncated output")
                h.update(blk)
                nb -= len(blk)
            yield tuple(c), h.hexdigest()
        rest = p.stdout.read()
        if p.wait() != 0 or rest:
            raise SystemExit("dumpcnf --stream failed")
    os.remove(lf)


def chunks(xs, m):
    for i in range(0, len(xs), m):
        yield xs[i : i + m]


def load_records(path):
    """{case: cnf_sha256} of a (possibly xz-compressed, possibly still growing) jsonl file of a run"""
    op = lzma.open if path.endswith(".xz") else open
    rec = {}
    with op(path, "rt") as f:
        for line in f:
            try:
                r = json.loads(line)
            except ValueError:
                continue
            if (
                isinstance(r, dict)
                and "case" in r
                and "cnf_sha256" in r
                and "cube" not in r
            ):
                rec[tuple(r["case"])] = r["cnf_sha256"]
    return rec


def sample(cases, m, rng):
    """stratified sample: (up to) three random cases of every (shape, deficit vector) class, a few extreme
    cases, then random cases up to m"""
    strata = {}
    for c in cases:
        strata.setdefault((shape(c), tuple(c[4:])), []).append(c)
    chosen = set()
    for _, v in sorted(strata.items()):
        chosen.update(rng.sample(v, min(3, len(v))))
    chosen.update(
        [
            cases[0],
            cases[-1],
            max(cases, key=lambda c: (c[0] + c[1], c[2] + c[3])),
            max(cases, key=lambda c: (c[2] + c[3], c[0] + c[1])),
            max(cases, key=lambda c: sum(c[:4])),
            max(cases, key=lambda c: sum(c[4:])),
        ]
    )
    rest = [c for c in cases if c not in chosen]
    rng.shuffle(rest)
    chosen = sorted(chosen) + rest[: max(0, m - len(chosen))]
    cov = {
        s
        for s in strata
        if any(shape(c) == s[0] and tuple(c[4:]) == s[1] for c in chosen)
    }
    return sorted(chosen, key=lambda c: (c[4:], c[:4])), len(strata), len(cov)


def group_i(a):
    print("(i) all cases of the small boards: dumpcnf --batch vs enc.py", flush=True)
    tot = 0
    for n, k in SMALL:
        t0 = time.time()
        cases = sorted(geom.cases_by_frame(n, k), key=lambda c: (c[4:], c[:4]))
        py = PyEnc(n, k)
        bad = 0
        for ch in chunks(cases, 400):
            lean = lean_batch(n, k, ch, a.tmp)
            for c in ch:
                if lean[c] != py.sha(c):
                    bad += 1
                    note_fail(
                        f"(i) n={n:d} k={k:d} case {tag(c)}: lean {lean[c][:16]} != enc.py"
                    )
        dvs = {c[4:] for c in cases}
        nozero = sum(1 for c in cases if 0 not in c[4:])
        sh = {
            s: sum(1 for c in cases if shape(c) == s) for s in ("square", "w>h", "h>w")
        }
        tot += len(cases)
        line = (
            f"  (i) n={n:d} k={k:d}: {len(cases):d} cases compared, {bad:d} mismatches  "
            f"[deficit vectors {len(dvs):d}, cases with no zero deficit {nozero:d}, "
            f"square {sh['square']:d}, w>h {sh['w>h']:d}, h>w {sh['h>w']:d}]  "
            f"{time.time() - t0:.1f}s"
        )
        print(line, flush=True)
        SUMMARY.append(line)
    return tot


def group_ii_iii(a):
    print(
        "(ii) stratified random samples of the large boards: dumpcnf --batch vs enc.py;  (iii) vs recorded hashes",
        flush=True,
    )
    stdcases = {}
    for n, k in LARGE:
        t0 = time.time()
        cases = run_cases48.cases_fast(n, k)
        rng = random.Random(f"{a.seed:d}/{n:d}/{k:d}")
        smp, nstrata, ncov = sample(cases, a.samples, rng)
        stdcases[(n, k)] = [smp[0], smp[len(smp) // 2], smp[-1]]
        rec = {}
        for f in RECORDED.get((n, k), []):
            rec.update(load_records(os.path.join(DATA, f)))
        py = PyEnc(n, k)
        bad = badrec = nrec = 0
        for ch in chunks(smp, 40):
            lean = lean_batch(n, k, ch, a.tmp)
            for c in ch:
                if lean[c] != py.sha(c):
                    bad += 1
                    note_fail(
                        f"(ii) n={n:d} k={k:d} case {tag(c)}: lean {lean[c][:16]} != enc.py"
                    )
                if c in rec:
                    nrec += 1
                    if lean[c] != rec[c]:
                        badrec += 1
                        note_fail(
                            f"(iii) n={n:d} k={k:d} case {tag(c)}: lean {lean[c][:16]} != recorded {rec[c][:16]}"
                        )
                elif (n, k) in MUST_BE_RECORDED:
                    badrec += 1
                    note_fail(
                        f"(iii) n={n:d} k={k:d} case {tag(c)} has no recorded hash"
                    )
        sh = {s: sum(1 for c in smp if shape(c) == s) for s in ("square", "w>h", "h>w")}
        dvs = {c[4:] for c in smp}
        all_dvs = len({c[4:] for c in cases})
        nozero = sum(1 for c in smp if 0 not in c[4:])
        line = (
            f"  (ii) n={n:d} k={k:d}: {len(smp):d} of {len(cases):d} cases sampled and compared, {bad:d} mismatches  "
            f"[square {sh['square']:d}, w>h {sh['w>h']:d}, h>w {sh['h>w']:d}; "
            f"deficit vectors {len(dvs):d} of {all_dvs:d}; "
            f"(shape, deficits) classes {ncov:d} of {nstrata:d}; no zero deficit {nozero:d}]  "
            f"{time.time() - t0:.1f}s"
        )
        print(line, flush=True)
        SUMMARY.append(line)
        if ncov != nstrata or len(smp) < a.samples:
            note_fail(f"(ii) n={n:d} k={k:d}: sample does not cover all classes")
        if (n, k) in RECORDED:
            rec_files = ", ".join(RECORDED[(n, k)])
            line = (
                f"  (iii) n={n:d} k={k:d}: {nrec:d} sampled cases compared with the recorded cnf_sha256 ({rec_files}), "
                f"{badrec:d} mismatches"
            )
            print(line, flush=True)
            SUMMARY.append(line)
    return stdcases


def group_iv(a):
    print(
        "(iv) case lists: listcases vs geom.cases_by_frame / run_cases48.cases_fast",
        flush=True,
    )
    for n, k in SMALL + LISTS_SLOW + LISTS_FAST:
        t0 = time.time()
        r = subprocess.run(
            [LIST, str(n), str(k)], capture_output=True, text=True, check=False
        )
        if r.returncode != 0:
            raise SystemExit(f"listcases failed: {r.stderr}")
        lean = [tuple(map(int, l.split())) for l in r.stdout.splitlines()]
        if (n, k) in SMALL + LISTS_SLOW:
            py = geom.cases_by_frame(n, k)
            src = "geom.cases_by_frame"
            if py != run_cases48.cases_fast(n, k):
                note_fail(
                    f"(iv) n={n:d} k={k:d}: cases_fast differs from cases_by_frame"
                )
        else:
            py = run_cases48.cases_fast(n, k)
            src = "run_cases48.cases_fast"
        same = lean == py
        if not same:
            note_fail(
                f"(iv) n={n:d} k={k:d}: case lists differ (lean {len(lean):d}, python {len(py):d})"
            )
        nframes = len({c[:4] for c in py})
        line = (
            f"  (iv) n={n:d} k={k:d}: lean {len(lean):d} cases, {src} {len(py):d} cases, "
            f"frames {nframes:d}, identical lists: {same}  {time.time() - t0:.1f}s"
        )
        print(line, flush=True)
        SUMMARY.append(line)


def group_v(a, stdcases):
    print(
        "(v) single cases: dumpcnf n k <case> vs enc.py; toCNF: Std.Sat.CNF.dimacs (caseCNF ...) vs enc.py, "
        "clause by clause",
        flush=True,
    )
    todo = []
    for n, k in SMALL:
        cs = geom.cases_by_frame(n, k)
        todo += [(n, k, c) for c in {cs[0], cs[len(cs) // 3], cs[len(cs) // 2], cs[-1]}]
    for (n, k), cs in stdcases.items():
        todo += [(n, k, c) for c in cs]
    ncl = bad = bad1 = 0
    for n, k, c in sorted(todo):
        txt, _nv = PyEnc(n, k).text(c)
        r = subprocess.run(
            [DUMP, str(n), str(k)] + [str(v) for v in c],
            capture_output=True,
            check=False,
        )
        if r.returncode != 0:
            raise SystemExit(f"dumpcnf failed: {r.stderr}")
        if hashlib.sha256(r.stdout).hexdigest() != enc.sha(txt):
            bad1 += 1
            note_fail(
                f"(v) n={n:d} k={k:d} case {tag(c)}: dumpcnf (single case) differs from enc.py"
            )
        r = subprocess.run(
            [DUMP, "--std", str(n), str(k)] + [str(v) for v in c],
            capture_output=True,
            text=True,
            check=False,
        )
        if r.returncode != 0:
            raise SystemExit(f"dumpcnf --std failed: {r.stderr}")
        pl = txt.split("\n")
        ll = r.stdout.split("\n")
        ph = pl[0].split()
        lh = ll[0].split()
        # Std prints the largest variable that occurs and "0" for the empty clause; enc.py prints nv and " 0"
        ok = (
            len(pl) == len(ll)
            and lh[:2] == ["p", "cnf"]
            and lh[3] == ph[3]
            and int(lh[2]) <= int(ph[2])
            and all(x.strip() == y for x, y in zip(pl[1:], ll[1:], strict=False))
        )
        ncl += len(pl) - 2
        if not ok:
            bad += 1
            note_fail(
                f"(v) n={n:d} k={k:d} case {tag(c)}: Std.Sat.CNF.dimacs (caseCNF ..) differs from enc.py"
            )
    line = (
        f"  (v) {len(todo):d} cases: dumpcnf single-case output vs enc.py, {bad1:d} mismatches; "
        f"the same {len(todo):d} cases ({ncl:d} clauses) printed "
        f"through Std.Sat.CNF.dimacs (toCNF), {bad:d} mismatches"
    )
    print(line, flush=True)
    SUMMARY.append(line)


def group_vi(a):
    if not os.path.exists(RUN48):
        return
    print("(vi) hashes recorded so far by the (48, 24) run", flush=True)
    t0 = time.time()
    rec = load_records(RUN48)
    cases = sorted(rec, key=lambda c: (c[4:], c[:4]))[: a.run48]
    bad = 0
    for c, h in lean_stream(48, 24, cases, a.tmp):
        if h != rec[c]:
            bad += 1
            note_fail(
                f"(vi) n=48 k=24 case {tag(c)}: lean {h[:16]} != recorded {rec[c][:16]}"
            )
    line = (
        f"  (vi) n=48 k=24: {len(cases):d} cases of runs/d_48_24.jsonl ({len(rec):d} records at this time) "
        f"compared with the recorded cnf_sha256, {bad:d} mismatches  {time.time() - t0:.1f}s"
    )
    print(line, flush=True)
    SUMMARY.append(line)


def group_full(a):
    print(
        "(full) all cases of the recorded runs: dumpcnf --stream vs recorded cnf_sha256",
        flush=True,
    )
    for n, k in FULL:
        t0 = time.time()
        rec = {}
        for f in RECORDED[(n, k)]:
            rec.update(load_records(os.path.join(DATA, f)))
        cases = run_cases48.cases_fast(n, k)
        miss = [c for c in cases if c not in rec]
        if miss:
            note_fail(
                f"(full) n={n:d} k={k:d}: {len(miss):d} cases without recorded hash"
            )
        todo = sorted((c for c in cases if c in rec), key=lambda c: (c[4:], c[:4]))
        bad = 0
        for c, h in lean_stream(n, k, todo, a.tmp):
            if h != rec[c]:
                bad += 1
                note_fail(
                    f"(full) n={n:d} k={k:d} case {tag(c)}: lean {h[:16]} != recorded {rec[c][:16]}"
                )
        line = (
            f"  (full) n={n:d} k={k:d}: {len(todo):d} of {len(cases):d} cases compared with the recorded cnf_sha256, "
            f"{bad:d} mismatches  {time.time() - t0:.1f}s"
        )
        print(line, flush=True)
        SUMMARY.append(line)


def group_all(a, n, k):
    print(f"(all) all cases of ({n:d}, {k:d}): dumpcnf --stream vs enc.py", flush=True)
    t0 = time.time()
    cases = sorted(run_cases48.cases_fast(n, k), key=lambda c: (c[4:], c[:4]))
    py = PyEnc(n, k)
    bad = 0
    for done, (c, h) in enumerate(lean_stream(n, k, cases, a.tmp), start=1):
        if h != py.sha(c):
            bad += 1
            note_fail(f"(all) n={n:d} k={k:d} case {tag(c)}: lean {h[:16]} != enc.py")
        if done % 5000 == 0:
            print(
                f"  ... {done:d} of {len(cases):d} cases, {bad:d} mismatches, {time.time() - t0:.0f}s",
                flush=True,
            )
    sh = {s: sum(1 for c in cases if shape(c) == s) for s in ("square", "w>h", "h>w")}
    ndvs = len({c[4:] for c in cases})
    line = (
        f"  (all) n={n:d} k={k:d}: ALL {len(cases):d} cases compared (dumpcnf --stream vs enc.py), {bad:d} mismatches  "
        f"[square {sh['square']:d}, w>h {sh['w>h']:d}, "
        f"h>w {sh['h>w']:d}; deficit vectors {ndvs:d}]  {time.time() - t0:.1f}s"
    )
    print(line, flush=True)
    SUMMARY.append(line)


def main():
    ap = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    ap.add_argument(
        "--tmp",
        default=os.path.join(PKG, ".lake", "compare_enc_tmp"),
        help="directory for temporary CNF files (default: lean-sat/.lake/compare_enc_tmp; not /tmp)",
    )
    ap.add_argument(
        "--samples",
        type=int,
        default=300,
        help="sample size per large board (default 300)",
    )
    ap.add_argument("--seed", type=int, default=20261124)
    ap.add_argument(
        "--run48",
        type=int,
        default=200,
        help="maximal number of records of the (48, 24) run to compare",
    )
    ap.add_argument(
        "--full",
        action="store_true",
        help=f"also compare ALL cases of {FULL} with the recorded hashes",
    )
    ap.add_argument(
        "--all",
        action="append",
        default=[],
        metavar="N,K",
        help="also compare ALL cases of the board (N, K) with enc.py (repeatable)",
    )
    ap.add_argument(
        "--only",
        default="",
        help="comma-separated subset of i,ii,iv,v,vi,full (ii includes iii); 'none' "
        "runs only what --full / --all ask for",
    )
    a = ap.parse_args()
    for b in (DUMP, LIST):
        if not os.path.exists(b):
            raise SystemExit(f"{b} not found: run `lake build` in {PKG} first")
    os.makedirs(a.tmp, exist_ok=True)
    only = set(a.only.split(",")) if a.only else {"i", "ii", "iv", "v", "vi"}
    if a.full:
        only.add("full")
    t0 = time.time()
    stdcases = {}
    if "i" in only:
        group_i(a)
    if "ii" in only:
        stdcases = group_ii_iii(a)
    if "iv" in only:
        group_iv(a)
    if "v" in only:
        group_v(a, stdcases)
    if "vi" in only:
        group_vi(a)
    if "full" in only:
        group_full(a)
    for nk in a.all:
        n, k = map(int, nk.split(","))
        group_all(a, n, k)
    with contextlib.suppress(OSError):
        os.rmdir(a.tmp)
    print("\nSUMMARY (%.0fs)" % (time.time() - t0))
    for line in SUMMARY:
        print(line)
    if FAIL:
        print(f"\nFAILED: {len(FAIL):d} mismatches")
        sys.exit(1)
    print("\nALL IDENTICAL")
    sys.exit(0)


if __name__ == "__main__":
    main()
