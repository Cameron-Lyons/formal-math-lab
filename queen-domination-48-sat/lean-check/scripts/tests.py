#!/usr/bin/env python3
"""Tests of qdcheck.

    python3 -I scripts/tests.py WORKDIR [--proto LRATCHECK --certs48 DIR --records48 FILE [--sample N]]

WORKDIR is created and filled (a few MB; do not use a small tmpfs for the (48,24) part).

 (a) complete instance (n,k) = (8,4) [gamma(Q_8) = 5: all 195 cases are UNSAT]: the certificates are
     produced on the spot with the tools of the real run (code/frame/run_cases48.py: cadical,
     drat-trim -L, zstd); `qdcheck 8 4` must print `s ALL VERIFIED n=8 k=4 cases=195` and exit with 0,
     for several numbers of threads and chunk sizes; subset runs must exit with 3 and not claim it;
 (b) satisfiable instance (6,3): one case has a model, hence no certificate: exit 1, no success
     line, also when the missing certificate is replaced by the certificate of another case;
 (c) negative tests on (8,4): missing / damaged / truncated / mutated / swapped certificates;
 (e) a formula that contains the empty clause (drat-trim answers with an LRAT file of 0 bytes);
 (f) the status line cannot be forged: text given from outside (a path of the command line, the error
     output of the decompressor) that contains a newline followed by a success line does not produce
     a line starting with `s `; an empty case list gives `cases=0`;
 (d) with --proto: agreement with the prototype `lratcheck --stream` (which parses the DIMACS file
     written by enc.py) on a sample of the (48,24) cases, including swapped certificates.
"""

import argparse
import json
import os
import random
import shutil
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
PKG = os.path.dirname(HERE)
REPO = os.path.dirname(PKG)
Q = os.path.join(PKG, ".lake", "build", "bin", "qdcheck")
RUN = os.path.join(REPO, "code", "frame", "run_cases48.py")
DUMPCNF = os.path.join(REPO, "lean-sat", ".lake", "build", "bin", "dumpcnf")
CAD = os.path.join(REPO, "tools", "cadical")
DRAT = os.path.join(REPO, "tools", "drat-trim")

fails = 0
count = 0


def check(cond, what):
    global fails, count
    count += 1
    print(("ok    " if cond else "FAIL  ") + what, flush=True)
    if not cond:
        fails += 1


def tag(case):
    return "_".join(map(str, case))


def qd(n, k, certs, *opts, log=None):
    """run qdcheck; returns (exit code, stdout lines, log records)"""
    cmd = [Q, str(n), str(k), certs, "--progress", "0", *list(opts)]
    if log:
        cmd += ["--log", log]
    r = subprocess.run(cmd, capture_output=True, text=True, check=False)
    if log:
        with open(log) as f:
            recs = [json.loads(l) for l in f]
    else:
        recs = []
    return r.returncode, r.stdout.splitlines(), recs


def status(lines):
    s = [l for l in lines if l.startswith("s ")]
    return s[-1] if len(s) == 1 else f"NO-OR-SEVERAL-STATUS-LINES {s!r}"


def generate(n, k, out):
    """certificates of all UNSAT cases of (n, k), with the tools of the real run"""
    has_summary = False
    if os.path.exists(out):
        with open(out) as f:
            has_summary = "summary" in f.read()
    if not has_summary:
        for p in (out, out + ".lrat", out + ".wd"):
            if os.path.isdir(p):
                shutil.rmtree(p)
            elif os.path.exists(p):
                os.remove(p)
        subprocess.run(
            [sys.executable, "-I", RUN, str(n), str(k), "--jobs", "2", "--out", out],
            check=True,
            capture_output=True,
        )
    with open(out) as f:
        recs = [json.loads(l) for l in f]
    return [r for r in recs if "case" in r], [r for r in recs if "summary" in r][-1][
        "summary"
    ]


def zst_write(path, data):
    subprocess.run(["zstd", "-q", "-f", "-3", "-o", path], input=data, check=True)


def zst_read(path):
    return subprocess.run(["zstd", "-dc", path], check=True, capture_output=True).stdout


def copy_certs(src, dst):
    if os.path.isdir(dst):
        shutil.rmtree(dst)
    shutil.copytree(src, dst)


def test_a(W):
    print("--- (a) complete instance (8,4)")
    recs, summ = generate(8, 4, os.path.join(W, "d_8_4.jsonl"))
    certs = os.path.join(W, "d_8_4.jsonl.lrat")
    check(
        summ["cases"] == 195 and summ["UNSAT"] == 195 and summ["verified"] == 195,
        "run_cases48.py 8 4: 195 cases, all UNSAT with a drat-trim-verified proof",
    )
    check(len(os.listdir(certs)) == 195, "195 certificate files")
    for opts in (
        ["--jobs", "1"],
        ["--jobs", "2"],
        ["--jobs", "5"],
        ["--jobs", "2", "--chunk-bytes", "1"],
        ["--jobs", "2", "--chunk-bytes", "7"],
        ["--jobs", "3", "--chunk-bytes", "4096"],
        ["--jobs", "1", "--direct-zstd"],
        ["--jobs", "4", "--direct-zstd"],
        ["--jobs", "2", "--direct-zstd", "--chunk-bytes", "5"],
    ):
        log = os.path.join(W, "a.jsonl")
        rc, out, lr = qd(8, 4, certs, *opts, log=log)
        cases = [r for r in lr if "case" in r]
        s = lr[-1].get("summary", {})
        byc = {tuple(r["case"]): r for r in cases}
        same = all(byc[tuple(r["case"])]["bytes"] == r["lrat_bytes"] for r in recs)
        check(
            rc == 0
            and status(out) == "s ALL VERIFIED n=8 k=4 cases=195"
            and len(cases) == 195
            and all(r["verdict"] == "verified" for r in cases)
            and len(byc) == 195
            and same
            and s.get("all_verified") is True
            and s.get("verified") == 195
            and s.get("failed") == 0,
            "qdcheck 8 4 {}: exit 0, ALL VERIFIED, 195 log lines, bytes equal to the records".format(
                " ".join(opts)
            ),
        )
    for m in (0, 1, 10, 195, 500):
        rc, out, _ = qd(8, 4, certs, "--limit", str(m), "--jobs", "2")
        check(
            rc == 3
            and status(out).startswith(
                f"s SUBSET VERIFIED n=8 k=4 cases={min(m, 195):d} of 195"
            )
            and not any("ALL VERIFIED" in l for l in out),
            f"--limit {m:d}: exit 3, SUBSET VERIFIED, no ALL VERIFIED",
        )
    cf = os.path.join(W, "a_cases.txt")
    with open(cf, "w") as f:
        f.write("[0, 0, 0, 0, 0, 0, 0, 0]\n0 0 0 1 0 0 0 0\n\n")
    rc, out, _ = qd(8, 4, certs, "--cases", cf)
    check(
        rc == 3 and status(out).startswith("s SUBSET VERIFIED n=8 k=4 cases=2 of 195"),
        "--cases (2 cases): exit 3, SUBSET VERIFIED",
    )
    with open(cf, "w") as f:
        f.write("".join(json.dumps(r["case"]) + "\n" for r in recs))
    rc, out, _ = qd(8, 4, certs, "--cases", cf)
    check(
        rc == 3 and not any("ALL VERIFIED" in l for l in out),
        "--cases with all 195 cases: still exit 3, no ALL VERIFIED",
    )
    with open(cf, "w") as f:
        f.write("0 0 0 1 0 0 0\n")
    rc, out, _ = qd(8, 4, certs, "--cases", cf)
    check(rc == 2, "--cases with a malformed line: exit 2")
    rc, out, _ = qd(8, 4, os.path.join(W, "no-such-dir"), "--jobs", "2")
    check(
        rc == 1
        and status(out).startswith("s NOT VERIFIED n=8 k=4 verified=0 failed=195"),
        "certificate directory missing: exit 1, 195 failed",
    )
    for mode in ([], ["--direct-zstd"]):
        r = subprocess.run(
            [
                Q,
                "8",
                "4",
                certs,
                "--zstd",
                "/nonexistent/zstd",
                "--progress",
                "0",
                *mode,
            ],
            capture_output=True,
            text=True,
            check=False,
        )
        check(
            r.returncode == 1
            and status(r.stdout.splitlines()).startswith(
                "s NOT VERIFIED n=8 k=4 verified=0 failed=195"
            ),
            "decompressor missing {}: exit 1, 195 failed".format(" ".join(mode)),
        )
    # a decompressor that produces nothing / garbage
    for fake, what in (("true", "prints nothing"), ("echo", "prints its arguments")):
        r = subprocess.run(
            [Q, "8", "4", certs, "--zstd", fake, "--progress", "0"],
            capture_output=True,
            text=True,
            check=False,
        )
        check(
            r.returncode == 1
            and status(r.stdout.splitlines()).startswith(
                "s NOT VERIFIED n=8 k=4 verified=0 failed=195"
            ),
            f"a decompressor that {what}: exit 1, 195 failed",
        )
    return recs, certs


def test_b(W):
    print("--- (b) satisfiable instance (6,3)")
    recs, summ = generate(6, 3, os.path.join(W, "d_6_3.jsonl"))
    certs = os.path.join(W, "d_6_3.jsonl.lrat")
    sat = [r["case"] for r in recs if r["result"] == "SAT"]
    check(
        summ["verdict"] == "SAT" and len(sat) >= 1,
        f"run_cases48.py 6 3: {len(sat):d} SAT case(s) of {summ['cases']:d}: {sat}",
    )
    log = os.path.join(W, "b.jsonl")
    rc, out, lr = qd(6, 3, certs, "--jobs", "2", log=log)
    failed = sorted(r["case"] for r in lr if r.get("verdict") == "failed")
    check(
        rc == 1
        and status(out).startswith("s NOT VERIFIED n=6 k=3")
        and failed == sorted(sat)
        and not any("VERIFIED" in l and "NOT VERIFIED" not in l for l in out)
        and lr[-1]["summary"]["all_verified"] is False,
        "qdcheck 6 3: exit 1, NOT VERIFIED, the failed cases are exactly the SAT cases",
    )
    # a certificate of another case for the satisfiable case(s)
    neg = os.path.join(W, "b_fake")
    copy_certs(certs, neg)
    donors = sorted(
        os.listdir(certs), key=lambda f: -os.path.getsize(os.path.join(certs, f))
    )
    for c in sat:
        shutil.copy(
            os.path.join(certs, donors[0]), os.path.join(neg, tag(c) + ".lrat.zst")
        )
    rc, out, lr = qd(6, 3, neg, "--jobs", "2", log=log)
    failed = sorted(r["case"] for r in lr if r.get("verdict") == "failed")
    check(
        rc == 1 and failed == sorted(sat) and status(out).startswith("s NOT VERIFIED"),
        "qdcheck 6 3 with a foreign certificate for the SAT case: exit 1 (%s)"
        % [r.get("reason") for r in lr if r.get("verdict") == "failed"],
    )
    # every other certificate tried on the satisfiable case: none may be accepted
    c = sat[0]
    cf = os.path.join(W, "b_cases.txt")
    with open(cf, "w") as f:
        f.write(json.dumps(c) + "\n")
    accepted = 0
    for d in donors:
        shutil.copy(os.path.join(certs, d), os.path.join(neg, tag(c) + ".lrat.zst"))
        rc, out, _ = qd(6, 3, neg, "--cases", cf)
        accepted += rc != 1
    check(
        accepted == 0,
        f"the SAT case {c} rejects each of the {len(donors):d} certificates of the other cases",
    )


def test_c(W, recs, certs):
    print("--- (c) negative tests on (8,4)")
    log = os.path.join(W, "c.jsonl")
    order = [r["case"] for r in recs]
    big = sorted(recs, key=lambda r: -r["lrat_bytes"])
    A, B = big[0]["case"], big[1]["case"]  # the two cases with the longest proofs

    def run(neg, expect_failed, what):
        res = []
        for mode in (
            [],
            ["--direct-zstd"],
        ):  # through the decompression servers / zstd spawned directly
            rc, out, lr = qd(8, 4, neg, "--jobs", "2", *mode, log=log)
            failed = sorted(r["case"] for r in lr if r.get("verdict") == "failed")
            reasons = [r.get("reason") for r in lr if r.get("verdict") == "failed"]
            ok = (
                rc == 1
                and status(out).startswith("s NOT VERIFIED n=8 k=4")
                and not any("ALL VERIFIED" in l or "SUBSET" in l for l in out)
                and lr[-1]["summary"]["all_verified"] is False
            )
            if expect_failed is not None:
                ok = ok and failed == sorted(expect_failed)
            res.append((ok, failed, reasons))
        reason_note = (": " + res[0][2][0][:100]) if len(res[0][2]) == 1 else ""
        check(
            res[0][0] and res[1][0] and res[0][1] == res[1][1],
            f"{what}: exit 1, NOT VERIFIED, {len(res[0][1]):d} case(s) failed, in both decompression modes{reason_note}",
        )
        return res[0][1]

    neg = os.path.join(W, "c_neg")

    def fa(d=None):
        return os.path.join(d or neg, tag(A) + ".lrat.zst")

    text = zst_read(fa(certs))
    lines = text.split(b"\n")
    assert lines[-1] == b"" and len(lines) > 20

    copy_certs(certs, neg)
    os.remove(fa())
    run(neg, [A], "missing certificate")
    copy_certs(certs, neg)
    open(fa(), "wb").close()
    run(neg, [A], "certificate file of 0 bytes (not a zstd frame)")
    copy_certs(certs, neg)
    zst_write(fa(), b"")
    run(neg, [A], "empty proof")
    copy_certs(certs, neg)
    with open(fa(certs), "rb") as f:
        raw = bytearray(f.read())
    for i in range(len(raw) // 2, len(raw) // 2 + 16):
        raw[i] ^= 0x5A
    with open(fa(), "wb") as f:
        f.write(bytes(raw))
    run(neg, [A], "compressed file damaged (16 bytes flipped)")
    copy_certs(certs, neg)
    with open(fa(certs), "rb") as f:
        trunc = f.read()[:-20]
    with open(fa(), "wb") as f:
        f.write(trunc)
    run(neg, [A], "compressed file truncated")
    copy_certs(certs, neg)
    zst_write(fa(), b"\n".join(lines[:-2]) + b"\n")
    run(neg, [A], "proof without its last line (the empty clause)")
    copy_certs(certs, neg)
    zst_write(fa(), text[: len(text) // 2])
    run(neg, [A], "proof cut in the middle")
    # the final empty clause without its hints
    last = lines[-2].split()
    assert last[1] == b"0" and last[-1] == b"0"
    copy_certs(certs, neg)
    zst_write(fa(), b"\n".join([*lines[:-2], last[0] + b" 0 0"]) + b"\n")
    run(neg, [A], "empty clause without hints")
    copy_certs(certs, neg)
    zst_write(fa(), b"\n".join([*lines[:-2], b" ".join([*last[:-2], b"0"])]) + b"\n")
    run(neg, [A], "empty clause without its last hint")
    # a lemma that later steps refer to is removed
    lemma_idx = [i for i, l in enumerate(lines) if l and b" d " not in l]
    used = None
    for i in lemma_idx[:-1]:
        lid = lines[i].split()[0]
        if any(
            lid in lines[j].split()[lines[j].split().index(b"0") + 1 :]
            for j in lemma_idx
            if j > i
        ):
            used = i
            break
    assert used is not None
    copy_certs(certs, neg)
    zst_write(fa(), b"\n".join(lines[:used] + lines[used + 1 :]) + b"\n")
    run(neg, [A], "a lemma that is used later removed")
    t = lines[used].split()
    z = t.index(b"0")
    copy_certs(certs, neg)
    zst_write(
        fa(),
        b"\n".join([*lines[:used], b" ".join([*t[: z + 1], b"0"]), *lines[used + 1 :]])
        + b"\n",
    )
    run(
        neg,
        None,
        "all hints of a lemma removed (checked as a RAT step without candidates)",
    )
    copy_certs(certs, neg)
    zst_write(
        fa(),
        b"\n".join(
            [
                *lines[:used],
                b" ".join(t[: z + 1] + t[z + 1 : -1][::-1] + [b"0"]),
                *lines[used + 1 :],
            ]
        )
        + b"\n",
    )
    if len(t) - z > 4:
        run(neg, None, "hints of a lemma reversed")
    copy_certs(certs, neg)
    zst_write(fa(), b"\n".join([*lines[:5], b"12 x 0 1 0", *lines[5:]]) + b"\n")
    run(neg, [A], "garbage line in the proof")
    copy_certs(certs, neg)
    zst_write(fa(), b"not an LRAT proof\n")
    run(neg, [A], "text that is not a proof")
    # certificates of other cases
    copy_certs(certs, neg)
    shutil.copy(fa(certs), os.path.join(neg, tag(B) + ".lrat.zst"))
    run(neg, [B], f"certificate of case {tag(A)} used for case {tag(B)}")
    copy_certs(certs, neg)
    shutil.copy(os.path.join(certs, tag(B) + ".lrat.zst"), fa())
    shutil.copy(fa(certs), os.path.join(neg, tag(B) + ".lrat.zst"))
    run(neg, [A, B], "certificates of two cases swapped")
    copy_certs(certs, neg)
    for i, c in enumerate(order):
        shutil.copy(
            os.path.join(certs, tag(order[(i + 1) % len(order)]) + ".lrat.zst"),
            os.path.join(neg, tag(c) + ".lrat.zst"),
        )
    failed = run(
        neg, None, "every case with the certificate of the next case of the list"
    )
    check(
        len(failed) >= 150,
        f"  ... {len(failed):d} of 195 rotated certificates rejected (the others are proofs by unit propagation that fit both formulas)",
    )
    # one failure among many: all other cases are still checked and reported
    copy_certs(certs, neg)
    os.remove(fa())
    rc, _out, lr = qd(8, 4, neg, "--jobs", "4", log=log)
    check(
        rc == 1
        and sum(r.get("verdict") == "verified" for r in lr) == 194
        and lr[-1]["summary"]["failed"] == 1,
        "after a failure the other 194 cases are still verified and logged",
    )
    shutil.rmtree(neg)


def test_e(W):
    print("--- (e) formulas with an empty clause (LRAT file of 0 bytes)")
    d = os.path.join(W, "e")
    os.makedirs(os.path.join(d, "certs"), exist_ok=True)
    cases = [
        (0, 0, 0, 0, 1, 1, 1, 0),
        (0, 0, 0, 0, 1, 1, 1, 1),
        (0, 1, 0, 0, 3, 0, 0, 0),
    ]  # not admissible: a bound is negative
    sizes = []
    for c in cases:
        cnf = os.path.join(d, tag(c) + ".cnf")
        drat = os.path.join(d, tag(c) + ".drat")
        lrat = os.path.join(d, tag(c) + ".lrat")
        with open(cnf, "w") as f:
            subprocess.run(
                [DUMPCNF, "8", "4"] + [str(v) for v in c], stdout=f, check=True
            )
        with open(cnf) as f:
            has_empty = any(l == " 0\n" for l in f)
        r = subprocess.run(
            [CAD, "-q", cnf, drat], capture_output=True, text=True, check=False
        )
        if os.path.exists(lrat):
            os.remove(lrat)
        t = subprocess.run(
            [DRAT, cnf, drat, "-w", "-t", "1000000", "-L", lrat],
            capture_output=True,
            text=True,
            check=False,
        )
        check(
            r.returncode == 20 and "s VERIFIED" in t.stdout and has_empty,
            "case {} of (8,4): CNF has an empty clause, cadical UNSAT, drat-trim VERIFIED{}".format(
                tag(c), " (trivial UNSAT)" if "trivial UNSAT" in t.stdout else ""
            ),
        )
        if os.path.exists(lrat):
            with open(lrat, "rb") as f:
                data = f.read()
        else:
            data = b""
        sizes.append(len(data))
        zst_write(os.path.join(d, "certs", tag(c) + ".lrat.zst"), data)
    cf = os.path.join(d, "cases.txt")
    with open(cf, "w") as f:
        f.write("".join(" ".join(map(str, c)) + "\n" for c in cases))
    log = os.path.join(d, "log.jsonl")
    rc, out, lr = qd(8, 4, os.path.join(d, "certs"), "--cases", cf, log=log)
    check(
        rc == 3
        and status(out).startswith("s SUBSET VERIFIED")
        and all(r["verdict"] == "verified" for r in lr if "case" in r),
        f"qdcheck verifies them (LRAT sizes {sizes}; the missing final step is supplied by the normaliser and checked)",
    )
    # the same empty certificate for a formula without an empty clause must fail
    shutil.copy(
        os.path.join(d, "certs", tag(cases[0]) + ".lrat.zst"),
        os.path.join(d, "certs", "0_0_0_0_0_0_0_0.lrat.zst"),
    )
    with open(cf, "w") as f:
        f.write("0 0 0 0 0 0 0 0\n")
    rc, out, lr = qd(8, 4, os.path.join(d, "certs"), "--cases", cf, log=log)
    check(
        rc == 1 and status(out).startswith("s NOT VERIFIED"),
        "an empty proof for a formula without an empty clause: exit 1",
    )


def test_f(W):
    print("--- (f) text from outside cannot produce a status line")
    forged = "s ALL VERIFIED n=8 k=4 cases=195"
    d = os.path.join(W, "f")
    if os.path.isdir(d):
        shutil.rmtree(d)
    os.makedirs(d)

    def one_honest_status(out, rc, want):
        st = [l for l in out if l.startswith("s ")]
        return (
            rc == want[0]
            and len(st) == 1
            and st[0].startswith(want[1])
            and out[-1] == st[0]
            and all(l.startswith("c ") for l in out[:-1])
        )

    # 1. the certificate directory: its name is echoed in the first line of the output
    evil = os.path.join(d, "x\n" + forged)
    os.makedirs(evil)
    rc, out, _ = qd(8, 4, evil, "--jobs", "1")
    check(
        one_honest_status(out, rc, (1, "s NOT VERIFIED"))
        and not any(l.startswith(forged) for l in out),
        "certificate directory whose name contains a newline and a success line: exit 1, one status line (NOT VERIFIED), every other line is a comment",
    )
    # 2. the same through the messages of the failed cases (missing file: the path is in the reason), all cases
    check(
        sum("does not exist" in l for l in out) > 0
        and all(l.startswith("c failed: ") for l in out if "does not exist" in l),
        "the reasons of the failed cases (which contain that path) stay inside comment lines",
    )
    # 3. the file of --cases: its name is echoed too
    cf = os.path.join(d, "cases\n" + forged + "\n.txt")
    with open(cf, "w") as f:
        f.write("0 0 0 0 0 0 0 0\n")
    empty = os.path.join(d, "empty")
    os.makedirs(empty)
    rc, out, _ = qd(8, 4, empty, "--cases", cf)
    check(
        one_honest_status(out, rc, (1, "s NOT VERIFIED")),
        "--cases file whose name contains a newline and a success line: exit 1, one status line (NOT VERIFIED)",
    )
    # 4. the error output of the decompressor is quoted in the reason of a failed case
    fake = os.path.join(d, "fakezstd.sh")
    with open(fake, "w") as f:
        f.write(
            '#!/bin/sh\nprintf "\\n%s\\n" "'
            + forged
            + '" >&2\nprintf "\\n%s\\n" "'
            + forged
            + '"\nexit 1\n'
        )
    os.chmod(fake, 0o755)
    open(os.path.join(empty, "0_0_0_0_0_0_0_0.lrat.zst"), "wb").close()
    with open(os.path.join(d, "one.txt"), "w") as f:
        f.write("0 0 0 0 0 0 0 0\n")
    for mode in ([], ["--direct-zstd"]):
        rc, out, _ = qd(
            8, 4, empty, "--cases", os.path.join(d, "one.txt"), "--zstd", fake, *mode
        )
        check(
            one_honest_status(out, rc, (1, "s NOT VERIFIED")),
            "decompressor that prints a success line on stderr and stdout and fails%s: exit 1, one status line (NOT VERIFIED)"
            % (" (--direct-zstd)" if mode else ""),
        )
    # 5. the internal decompression server copies bytes to stdout: never exit 0, no positional arguments
    zst_write(os.path.join(d, "forged.zst"), ("\n" + forged + "\n").encode())
    inp = (os.path.join(d, "forged.zst") + "\n").encode()
    r = subprocess.run(
        [Q, "--decompress-server"], input=inp, capture_output=True, check=False
    )
    check(
        r.returncode == 4,
        "the internal decompression server ends with exit code 4, not 0",
    )
    r = subprocess.run(
        [Q, "8", "4", empty, "--jobs", "1", "--decompress-server"],
        input=inp,
        capture_output=True,
        check=False,
    )
    check(
        r.returncode == 2 and r.stdout == b"",
        "--decompress-server together with n k CERTDIR: usage error, no output",
    )
    # 6. the error output: a forged line does not start a line there either
    r = subprocess.run(
        [Q, "8", "4", evil, "--jobs", "1", "--progress", "0"],
        capture_output=True,
        text=True,
        check=False,
    )
    check(
        r.returncode == 1
        and not any(l.startswith("s ") for l in r.stderr.splitlines()),
        "certificate directory whose name contains a success line: no line of stderr starts with `s `",
    )
    # 7. an empty case list: the statement is vacuous and the output says cases=0
    rc, out, _ = qd(48, 23, empty)
    check(
        rc == 0 and status(out) == "s ALL VERIFIED n=48 k=23 cases=0",
        "empty case list (48, 23): exit 0 with `cases=0` in the status line (the statement about no formula)",
    )


def test_d(W, proto, certs48, records48, nsample):
    print("--- (d) agreement with the prototype lratcheck on (48,24)")
    sys.path.insert(0, os.path.join(REPO, "code", "frame"))
    import enc

    with open(records48) as f:
        recs = [json.loads(l) for l in f]
    recs = [r for r in recs if "case" in r]
    rnd = random.Random(4824)
    bydv = {}
    for r in recs:
        bydv.setdefault(tuple(r["case"][4:]), []).append(r)
    sample = []
    per = max(1, nsample // len(bydv))
    for dv, rs in sorted(bydv.items()):
        rs = sorted(rs, key=lambda r: r["lrat_bytes"])
        small = [r for r in rs if r["lrat_bytes"] <= 60e6]
        pick = [rs[0], small[-1], *rnd.sample(small, min(per, len(small)))]
        if dv == (0, 0, 0, 0):
            pick.append(
                next(r for r in rs if r["case"] == [0, 0, 0, 0, 0, 0, 0, 0])
            )  # 275 MB
        for r in pick:
            if r not in sample:
                sample.append(r)
    d = os.path.join(W, "d")
    os.makedirs(d, exist_ok=True)
    cf = os.path.join(d, "cases.txt")
    with open(cf, "w") as f:
        f.write("".join(json.dumps(r["case"]) + "\n" for r in sample))
    # a certificate directory with symbolic links, in which some certificates are swapped
    sw = os.path.join(d, "swapped")
    if os.path.isdir(sw):
        shutil.rmtree(sw)
    os.makedirs(sw)
    src = {tag(r["case"]): tag(r["case"]) for r in sample}
    tags = [tag(r["case"]) for r in sample]
    swapped = []
    for i in range(
        0, len(tags) - 1, 5
    ):  # every fifth case gets the certificate of its neighbour
        src[tags[i]] = tags[i + 1]
        swapped.append(tags[i])
    for t, s in src.items():
        os.symlink(
            os.path.join(os.path.abspath(certs48), s + ".lrat.zst"),
            os.path.join(sw, t + ".lrat.zst"),
        )

    def proto_run(case, cert):
        B = bases.setdefault(tuple(case[4:]), enc.Base(48, 24, tuple(case[4:])))
        extra, nv = enc.case_extra(B, tuple(case))
        cnf = os.path.join(d, "f.cnf")
        txt = enc.dimacs(B, extra, nv)
        with open(cnf, "w") as f:
            f.write(txt)
        z = subprocess.Popen(
            ["zstd", "-dc", os.path.realpath(cert)], stdout=subprocess.PIPE
        )
        assert z.stdout is not None
        r = subprocess.run(
            [proto, "--stream", cnf, "-"],
            stdin=z.stdout,
            capture_output=True,
            text=True,
            check=False,
        )
        z.stdout.close()
        z.wait()
        out = r.stdout
        st = [l for l in out.splitlines() if l.startswith("s ")][-1]

        def num(key):
            return int(out.split(key + "=")[1].split()[0])

        return st == "s VERIFIED", num("lemmas"), num("hints"), enc.sha(txt)

    bases = {}
    log = os.path.join(d, "log.jsonl")
    rc, out, lr = qd(48, 24, certs48, "--cases", cf, "--jobs", "2", log=log)
    mine = {tuple(r["case"]): r for r in lr if "case" in r}
    sample_gb = sum(r["lrat_bytes"] for r in sample) / 1e9
    check(
        rc == 3
        and status(out).startswith(
            f"s SUBSET VERIFIED n=48 k=24 cases={len(sample):d} of 47580"
        ),
        f"qdcheck 48 24 --cases (sample of {len(sample):d} cases, {sample_gb:.1f} GB of LRAT, all 11 deficit vectors): exit 3, SUBSET VERIFIED",
    )
    agree = sha_ok = 0
    for r in sample:
        ok, lem, hints, sha = proto_run(
            r["case"], os.path.join(certs48, tag(r["case"]) + ".lrat.zst")
        )
        m = mine[tuple(r["case"])]
        agree += (
            ok
            and m["verdict"] == "verified"
            and lem == m["lemmas"]
            and hints == m["hints"]
            and m["bytes"] == r["lrat_bytes"]
        )
        sha_ok += sha == r["cnf_sha256"]
    check(
        agree == len(sample),
        f"prototype: same verdict (VERIFIED), lemma and hint counts on {agree:d} of {len(sample):d} cases; bytes equal to the records",
    )
    check(
        sha_ok == len(sample),
        f"the CNFs given to the prototype have the records' cnf_sha256 ({sha_ok:d} of {len(sample):d})",
    )
    rc, out, lr = qd(48, 24, sw, "--cases", cf, "--jobs", "2", log=log)
    mine = {tag(r["case"]): r for r in lr if "case" in r}
    agree = 0
    rejected = 0
    for t in swapped:
        ok, lem, hints, _ = proto_run(
            [int(x) for x in t.split("_")], os.path.join(sw, t + ".lrat.zst")
        )
        agree += ok == (mine[t]["verdict"] == "verified")
        rejected += not ok
    untouched_ok = all(
        mine[t]["verdict"] == "verified" for t in tags if t not in swapped
    )
    check(
        rc == 1 and agree == len(swapped) and untouched_ok,
        f"swapped certificates ({len(swapped):d} cases): qdcheck and the prototype agree on every one ({rejected:d} rejected by both); the untouched cases are verified",
    )


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("workdir")
    ap.add_argument(
        "--proto", default="", help="the prototype binary lratcheck: enables test (d)"
    )
    ap.add_argument(
        "--certs48", default=os.path.join(REPO, "runs", "d_48_24.jsonl.lrat")
    )
    ap.add_argument("--records48", default=os.path.join(REPO, "runs", "d_48_24.jsonl"))
    ap.add_argument("--sample", type=int, default=44)
    ap.add_argument("--only", default="abcefd")
    a = ap.parse_args()
    W = os.path.abspath(a.workdir)
    os.makedirs(W, exist_ok=True)
    recs = certs = None
    if "a" in a.only or "c" in a.only:
        if "a" in a.only:
            recs, certs = test_a(W)
        else:
            recs, _ = generate(8, 4, os.path.join(W, "d_8_4.jsonl"))
            certs = os.path.join(W, "d_8_4.jsonl.lrat")
    if "b" in a.only:
        test_b(W)
    if "c" in a.only:
        test_c(W, recs, certs)
    if "e" in a.only:
        test_e(W)
    if "f" in a.only:
        test_f(W)
    if "d" in a.only and a.proto:
        test_d(W, a.proto, a.certs48, a.records48, a.sample)
    print(f"{count:d} checks, {fails:d} failed")
    sys.exit(1 if fails else 0)


main()
