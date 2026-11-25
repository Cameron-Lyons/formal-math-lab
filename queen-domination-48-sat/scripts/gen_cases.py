#!/usr/bin/env python3
# Modified from lean/scripts/gen_cases.py of https://github.com/jasondavies/queen-domination (Apache-2.0):
# the arguments LABEL and WHOSE, the module prefix, and the wording of the header.
"""Generate the Lean files of the case list of a frame-method run from the referee's run logs
(read-only input):

  DIR/Cases<N>Data.lean         the case codes, one `def` per pair of horizontal margins (ml, mr), and
                                the table `caseCodes<N>T` with `caseCodes<N>T[ml][mr]` = that def;
  DIR/Cases<N>Pieces.lean       one kernel computation (`decide +kernel`) per pair (ml, mr) with
                                ml + mr <= k:  casesPQ N K ml mr = (tableCodes caseCodes<N>T ml mr).map Case.ofCode,
                                and the assembled equation  enumCases N K = (tableList K caseCodes<N>T).map Case.ofCode.

usage: python3 -B scripts/gen_cases.py N K /path/to/frame/out DIR [LABEL [WHOSE]]
       DIR: the directory of the Lean files; its name is the module prefix (here Queens48);
       LABEL: how the header names the directory of the run logs (default: frame/out);
       WHOSE: whose run the header says it is (default: "the referee's"; n = 48: "the")

The list consists of the cases refuted by the run (scripts/runlog.py: plain records UNSAT + VERIFIED, or a
cover by verified cube records).  Each case (ml, mr, mb, mt, dR, dC, dT, dS) is one decimal numeral
ml mr mb mt (two digits each) dR dC dT dS (one digit each); each def is sorted."""
import sys, os
sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from runlog import analyse, code

n, k, outdir, leandir = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3], sys.argv[4]
label = sys.argv[5].rstrip('/') if len(sys.argv) > 5 else 'frame/out'
whose = sys.argv[6] if len(sys.argv) > 6 else "the referee's"
refuted, info, keys = analyse(outdir, n, k)
assert info['sat_records'] == 0 and info['n_keys_not_refuted'] == 0, info
pairs = [(p, q) for p in range(k + 1) for q in range(k + 1 - p)]          # = marginPairs k
by_pq = {}
for c in refuted:
    assert c[:2] in set(pairs), c
    by_pq.setdefault(c[:2], []).append(code(c))
for v in by_pq.values():
    assert v == sorted(v)

hdr = ['/-', 'GENERATED FILE -- do not edit.  Produced by scripts/gen_cases.py from the run logs']
for fn, d in info['files'].items():
    if d['sha256']:
        hdr.append('  %s/%-20s (%6d records, sha256%s %s)' % (
            label, fn, d['records'], ' of the uncompressed text' if fn.endswith('.xz') else '', d['sha256']))
hdr.append("of %s frame-method run for n = %d, k = %d: %d cases, %d frames;" % (
    whose, n, k, len(refuted), len({c[:4] for c in refuted})))
hdr.append('%d refuted by a plain record (UNSAT, drat-trim VERIFIED), %d by verified cube records of run_hard.py.' % (
    info['plain_refuted'], info['cube_refuted']))

data = hdr + ['Each numeral encodes one case (ml, mr, mb, mt, dR, dC, dT, dS) in decimal as',
              '  ml mr mb mt (two digits each) dR dC dT dS (one digit each);',
              '`caseCodes%dT[ml][mr]` lists the cases with horizontal margins (ml, mr), sorted.' % n,
              '`QueenDom.Case.ofCode` decodes a numeral.', '-/', '',
              'module', '', '@[expose] public section', '', 'namespace QueenDom', '']
for (p, q) in pairs:
    if (p, q) not in by_pq:
        continue
    ch = by_pq[(p, q)]
    data.append('set_option maxRecDepth 100000 in')
    data.append('/-- The %d cases with (ml, mr) = (%d, %d) of the n = %d, k = %d run. -/' % (len(ch), p, q, n, k))
    data.append('def caseCodes%d_%d_%d : List Nat := [' % (n, p, q))
    for i in range(0, len(ch), 8):
        data.append('  ' + ', '.join(str(c) for c in ch[i:i + 8]) + (',' if i + 8 < len(ch) else ''))
    data.append(']')
    data.append('')
data.append('/-- The table of the case codes of the n = %d, k = %d run: row `ml`, column `mr`. -/' % (n, k))
data.append('def caseCodes%dT : List (List (List Nat)) := [' % n)
for p in range(k + 1):
    row = ['caseCodes%d_%d_%d' % (n, p, q) if (p, q) in by_pq else '[]' for q in range(k + 1 - p)]
    data.append('  [' + ', '.join(row) + ']' + (',' if p < k else ''))
data.append(']')
data += ['', 'end QueenDom', '']

pc = hdr + ['Kernel computations: the case list `L(%d, %d)` is the decoded table `caseCodes%dT`, checked piece' % (n, k, n),
            'by piece (one theorem per pair of horizontal margins (ml, mr), so that each kernel computation is',
            'small and the pieces are checked in parallel).  No `native_decide`.', '-/', '',
            'module', '', 'public import QueenDom.Main', 'public import %s.Cases%dData' % (os.path.basename(os.path.abspath(leandir)), n), '',
            '@[expose] public section', '', 'namespace QueenDom', '',
            'set_option maxRecDepth 100000 in',
            '/-- The %d pairs `(ml, mr)` with `ml + mr <= %d`. -/' % (len(pairs), k),
            'theorem marginPairs_%d : marginPairs %d = [' % (k, k)]
for i in range(0, len(pairs), 12):
    pc.append('    ' + ', '.join('(%d, %d)' % pq for pq in pairs[i:i + 12]) + (',' if i + 12 < len(pairs) else ''))
pc += ['  ] := by decide +kernel', '']
for (p, q) in pairs:
    pc.append('set_option maxRecDepth 100000 in')
    pc.append('set_option maxHeartbeats 0 in')
    pc.append('theorem piece%d_%d_%d : casesPQ %d %d %d %d = (tableCodes caseCodes%dT %d %d).map Case.ofCode := by'
              % (n, p, q, n, k, p, q, n, p, q))
    pc.append('  decide +kernel')
    pc.append('')
term = 'List.forall_mem_nil _'
for (p, q) in reversed(pairs):
    term = 'List.forall_mem_cons.2 ⟨piece%d_%d_%d,\n    %s⟩' % (n, p, q, term)
pc += ['set_option maxRecDepth 100000 in',
       '/-- **The case list `L(%d, %d)` is the decoded table of the run** (assembled from the pieces). -/' % (n, k),
       'theorem enumCases_%d_%d_table : enumCases %d %d = (tableList %d caseCodes%dT).map Case.ofCode := by' % (
           n, k, n, k, k, n),
       '  refine enumCases_eq_table ?_',
       '  rw [marginPairs_%d]' % k,
       '  exact ' + term, '', 'end QueenDom', '']
open(os.path.join(leandir, 'Cases%dData.lean' % n), 'w').write('\n'.join(data))
open(os.path.join(leandir, 'Cases%dPieces.lean' % n), 'w').write('\n'.join(pc))
print('n=%d k=%d: %d cases, %d frames, %d nonempty pieces of %d; written Cases%dData.lean, Cases%dPieces.lean' % (
    n, k, len(refuted), len({c[:4] for c in refuted}), len(by_pq), len(pairs), n, n))
