#!/usr/bin/env python3
# Derived from code/frame/run_cases.py of https://github.com/jasondavies/queen-domination (Apache-2.0); changes below.
"""Frame-method run for (n, k) that also keeps a trimmed LRAT proof of every case.

This is run_cases.py (--mode drat) with three additions; the formulas are the unchanged ones of enc.py:
  * the case list comes from cases_fast(), which enumerates the deficit vectors with the bound
    dR + dC + dT + dS <= 4k - 2n + 2 pushed into the loops (same list, same order as geom.cases_by_frame;
    `--check-list` compares the two);
  * drat-trim is called with `-L`, so that besides checking the DRAT proof it writes the core lemmas as an
    LRAT proof; the LRAT file is kept zstd-compressed in <out>.lrat/ (the DRAT proof is deleted as before);
  * the hardest class (square boxes, deficit vector 0) is run first, so that a satisfiable case, if there is
    one, shows up early.
Records: one JSON line per case (case, cnf_sha256, result, t_solve, proof_bytes, drat, t_check,
lrat_bytes, lrat_sha256).  Resumable.
usage: run_cases48.py n k --jobs 6 --out out.jsonl [--tl 1800] [--limit N] [--check-list] [--cases FILE]
"""
import argparse, hashlib, json, os, resource, subprocess, sys, time
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import geom
from geom import case_of, dominated
import enc

CAD = os.path.join(HERE, '..', '..', 'tools', 'cadical')
DRAT = os.path.join(HERE, '..', '..', 'tools', 'drat-trim')
_B = {}
_A = {}


def cases_fast(n, k):
    """geom.cases_by_frame(n, k), with the loops over the deficits cut at the bound of (F)"""
    out = []
    dm = k - 1; sm = 4 * k - 2 * n + 2
    for f in sorted(geom.canonical_frames(n, k)):
        for dR in range(0, min(dm, sm) + 1):
            for dC in range(0, min(dm, sm - dR) + 1):
                for dT in range(0, min(dm, sm - dR - dC) + 1):
                    for dS in range(0, min(dm, sm - dR - dC - dT) + 1):
                        if geom.admissible(n, k, f + (dR, dC, dT, dS)):
                            out.append(f + (dR, dC, dT, dS))
    return out


def init(n, k, wd, ld, tl, nice):
    _A.update(n=n, k=k, wd=wd, ld=ld, tl=tl)
    if nice:
        os.nice(nice)


def base(dv):
    if dv not in _B:
        _B[dv] = enc.Base(_A['n'], _A['k'], dv)
    return _B[dv]


def cpu_children():
    r = resource.getrusage(resource.RUSAGE_CHILDREN)
    return r.ru_utime + r.ru_stime


def tag_of(case):
    return '_'.join(map(str, case))


def work(case):
    n, k = _A['n'], _A['k']
    B = base(case[4:])
    extra, nv = enc.case_extra(B, case)
    rec = {'case': list(case)}
    txt = enc.dimacs(B, extra, nv)
    rec['cnf_sha256'] = enc.sha(txt)
    tag = tag_of(case)
    fc = os.path.join(_A['wd'], tag + '.cnf'); fp = os.path.join(_A['wd'], tag + '.drat')
    fl = os.path.join(_A['wd'], tag + '.lrat'); fz = os.path.join(_A['ld'], tag + '.lrat.zst')
    with open(fc, 'w') as f:
        f.write(txt)
    c0 = cpu_children()
    r = subprocess.run([CAD, '-q'] + (['-t', str(_A['tl'])] if _A.get('tl') else []) + [fc, fp], capture_output=True, text=True)
    c1 = cpu_children()
    rec['result'] = {10: 'SAT', 20: 'UNSAT', 0: 'TIMEOUT'}.get(r.returncode, 'ERR%d' % r.returncode)
    rec['t_solve'] = round(c1 - c0, 3)
    if rec['result'] == 'UNSAT':
        rec['proof_bytes'] = os.path.getsize(fp)
        d = subprocess.run([DRAT, fc, fp, '-w', '-t', '1000000', '-L', fl], capture_output=True, text=True)
        rec['drat'] = 'VERIFIED' if 's VERIFIED' in d.stdout else 'FAILED'
        rec['t_check'] = round(cpu_children() - c1, 3)
        if rec['drat'] == 'VERIFIED' and os.path.exists(fl):
            h = hashlib.sha256()
            with open(fl, 'rb') as f:
                for blk in iter(lambda: f.read(1 << 20), b''):
                    h.update(blk)
            rec['lrat_bytes'] = os.path.getsize(fl); rec['lrat_sha256'] = h.hexdigest()
            z = subprocess.run(['zstd', '-q', '-f', '-3', '--rm', fl, '-o', fz], capture_output=True, text=True)
            rec['lrat_zst'] = (z.returncode == 0)
    elif rec['result'] == 'SAT':
        lits = [int(t) for l in r.stdout.splitlines() if l.startswith('v ') for t in l.split()[1:]]
        pos = set(l for l in lits if l > 0)
        D = sorted((x, y) for x in range(n) for y in range(n) if B.q[x][y] in pos)
        rec['model'] = D
        rec['model_ok'] = len(D) == k and dominated(n, D) and case_of(n, D) == case
    for f in (fc, fp, fl):
        if os.path.exists(f):
            os.remove(f)
    return rec


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('n', type=int); ap.add_argument('k', type=int)
    ap.add_argument('--jobs', type=int, default=6); ap.add_argument('--out', required=True)
    ap.add_argument('--limit', type=int, default=0); ap.add_argument('--tl', type=int, default=1800)
    ap.add_argument('--nice', type=int, default=0)
    ap.add_argument('--check-list', action='store_true', help='compare cases_fast with geom.cases_by_frame (slow) and exit')
    ap.add_argument('--cases', default='', help='run only the cases listed in this file (one JSON list per line)')
    ap.add_argument('--stop-on-sat', action='store_true')
    a = ap.parse_args()
    cases = cases_fast(a.n, a.k)
    if a.check_list:
        slow = geom.cases_by_frame(a.n, a.k)
        print(json.dumps({'n': a.n, 'k': a.k, 'fast': len(cases), 'slow': len(slow), 'equal': cases == slow,
                          'sha256': hashlib.sha256(json.dumps(cases).encode()).hexdigest()}))
        sys.exit(0 if cases == slow else 1)
    ncases = len(cases); nframes = len({c[:4] for c in cases})
    done = {}
    if os.path.exists(a.out):
        for l in open(a.out):
            try:
                r = json.loads(l)
            except ValueError:
                continue
            if 'case' in r and (r.get('result') == 'SAT' or (r.get('result') == 'UNSAT' and r.get('drat') == 'VERIFIED')):
                done[tuple(r['case'])] = r
    todo = [c for c in cases if c not in done]
    if a.cases:
        want = {tuple(json.loads(l)) for l in open(a.cases) if l.strip()}
        todo = [c for c in todo if c in want]
    sq = lambda c: (c[0] + c[1]) == (c[2] + c[3])
    # hardest first: square boxes with deficit 0, then the other square boxes, then by distance from square
    todo.sort(key=lambda c: (0 if sq(c) and sum(c[4:]) == 0 else 1 if sq(c) else 2, abs((c[0] + c[1]) - (c[2] + c[3])), c))
    if a.limit:
        todo = todo[:a.limit]
    wd = a.out + '.wd'; ld = a.out + '.lrat'
    os.makedirs(wd, exist_ok=True); os.makedirs(ld, exist_ok=True)
    t0 = time.time()
    st = {'n': a.n, 'k': a.k, 'mode': 'drat+lrat', 'frames': nframes, 'cases': ncases, 'reused': len(done), 'run': 0, 'SAT': 0, 'UNSAT': 0,
          'verified': 0, 'other': 0, 't_solve': 0.0, 't_check': 0.0, 'proof_bytes': 0, 'lrat_bytes': 0, 'max_t_solve': 0.0}
    for r in done.values():
        st[r['result']] += 1; st['verified'] += r.get('drat') == 'VERIFIED'
    first_sat = None
    with open(a.out, 'a') as f, Pool(a.jobs, initializer=init, initargs=(a.n, a.k, wd, ld, a.tl, a.nice)) as P:
        for rec in P.imap_unordered(work, todo, chunksize=1):
            f.write(json.dumps(rec) + '\n'); f.flush()
            st['run'] += 1
            if rec['result'] in ('SAT', 'UNSAT'):
                st[rec['result']] += 1
            else:
                st['other'] += 1
            st['verified'] += rec.get('drat') == 'VERIFIED'
            ts = rec.get('t_solve', 0)
            st['t_solve'] += ts; st['t_check'] += rec.get('t_check', 0); st['proof_bytes'] += rec.get('proof_bytes', 0)
            st['lrat_bytes'] += rec.get('lrat_bytes', 0)
            st['max_t_solve'] = max(st['max_t_solve'], ts)
            if rec['result'] == 'SAT' and first_sat is None:
                first_sat = rec
                if a.stop_on_sat:
                    P.terminate()
                    break
        st['wall'] = round(time.time() - t0, 1)
        st['t_solve'] = round(st['t_solve'], 1); st['t_check'] = round(st['t_check'], 1)
        st['complete'] = (st['SAT'] + st['UNSAT'] == ncases)
        st['verdict'] = 'SAT' if st['SAT'] else ('UNSAT' if st['complete'] and st['other'] == 0 else 'INCOMPLETE')
        if st['verdict'] == 'UNSAT':
            st['all_proofs_verified'] = st['verified'] == ncases
        if first_sat:
            st['example'] = first_sat['model']
        f.write(json.dumps({'summary': st}) + '\n')
    print(json.dumps(st))


if __name__ == '__main__':
    main()
