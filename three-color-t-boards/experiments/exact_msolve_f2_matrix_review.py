#!/usr/bin/env python3
"""Compare actual C F2 kernel with independent set-row Gaussian elimination."""
import hashlib
import json
import os
from pathlib import Path
import random
import subprocess

ROOT = Path(__file__).resolve().parents[1]
HERE = ROOT/'experiments'
SOURCE = HERE/'exact_msolve_f2_bitset_tools/msolve-cc044551f8e202d00691990fd3fd0b1226a88ea2/src/neogb/la_ff_2_bitset.c'


def oracle(known, lower):
    # Sets, not bitsets; stop at the first free pivot, then use full Gauss-Jordan.
    pivots = {i: set(row) for i, row in enumerate(known)}
    owners = {}
    for index, row in enumerate(lower):
        current = set(row)
        while current:
            lead = min(current)
            if lead not in pivots:
                pivots[lead] = current
                owners[lead] = index
                break
            current ^= pivots[lead]
    for lead in sorted(owners, reverse=True):
        for other in sorted(owners):
            if other < lead and lead in pivots[other]:
                pivots[other] ^= pivots[lead]
    return [(owners[lead], sorted(pivots[lead])) for lead in sorted(owners, reverse=True)]


def wire(cases):
    lines = [str(len(cases))]
    for ncols, known, lower in cases:
        lines.append(f'{ncols} {len(known)} {len(lower)}')
        for row in known+lower:
            lines.append(' '.join(map(str, [len(row)]+row)))
    return '\n'.join(lines)+'\n'


def cases():
    rng = random.Random(0xF2B175E7)
    result = [(0, [], []), (1, [], []), (1, [[0]], []),
              (1, [], [[0], [0]]), (1, [[0]], [[0], [0]])]
    # Exact word boundaries, high bit, repeated rows, and highly dependent rows.
    for ncols in (2, 3, 63, 64, 65, 127, 128, 129, 255, 256, 257, 1025):
        result.append((ncols, [], [[0, ncols-1], [ncols-1], [0, ncols-1]]))
        known = [[i]+list(reversed(range(i+1,ncols))) for i in range(min(5,ncols))]
        result.append((ncols, known, [row[:] for row in known]*2))
        if ncols > 5:
            result.append((ncols, known, [[j] for j in reversed(range(5,ncols))]))
    for _ in range(1000):
        ncols = rng.choice([rng.randrange(1,280),63,64,65,127,128,129,257])
        ncl = rng.randrange(min(18,ncols)+1)
        nrl = rng.randrange(33)
        density = rng.choice((0.01, 0.05, 0.15, 0.5, 0.95))
        def ordered_lead_row(lead):
            tail = [i for i in range(lead+1,ncols) if rng.random() < density]
            rng.shuffle(tail)
            return [lead]+tail
        known = [ordered_lead_row(i) for i in range(ncl)]
        lower = []
        for _ in range(nrl):
            if lower and rng.randrange(4) == 0:
                lower.append(rng.choice(lower)[:])
            elif known and rng.randrange(4) == 0:
                lower.append(rng.choice(known)[:])
            else:
                lower.append(ordered_lead_row(rng.randrange(ncols)))
        result.append((ncols,known,lower))
    return result


def main():
    executable = HERE/'exact_msolve_f2_matrix_review.bin'
    command = ['cc','-std=c11','-O1','-g','-Wall','-Wextra','-Werror',
               '-fsanitize=address,undefined','-fno-omit-frame-pointer','-no-pie',
               str(HERE/'exact_msolve_f2_matrix_review.c'),'-o',str(executable)]
    subprocess.run(command,check=True,capture_output=True,text=True,timeout=30)
    inputs = cases()
    env = dict(os.environ, ASAN_OPTIONS='detect_leaks=1:halt_on_error=1',
               UBSAN_OPTIONS='halt_on_error=1:print_stacktrace=1')
    result = subprocess.run([str(executable)],input=wire(inputs),text=True,capture_output=True,
                            timeout=60,env=env)
    assert result.returncode == 0, result.stderr[-5000:]
    assert result.stderr == '', result.stderr
    output = iter(result.stdout.splitlines())
    zero_cases = unsorted_cases = total_pivots = 0
    for index, (ncols,known,lower) in enumerate(inputs):
        label,case_index,count,allocations = next(output).split()
        assert label == 'CASE' and int(case_index) == index
        wanted = oracle(known,lower)
        assert int(count) == len(wanted), index
        actual = []
        for _ in range(int(count)):
            line = next(output).split()
            assert line[0] == 'ROW'
            owner,bindex,mult,length,*support = map(int,line[1:])
            assert bindex == owner+100003 and mult == owner*17+70001
            assert len(support) == length and support == sorted(set(support))
            assert all(len(known) <= col < ncols for col in support)
            actual.append((owner,support))
        assert actual == wanted, (index,actual,wanted)
        zero_cases += not wanted
        unsorted_cases += any(row[1:] != sorted(row[1:]) for row in known+lower)
        total_pivots += len(wanted)
    assert next(output,None) is None
    # A small nontrivial sample exercises every allocation site in this path.
    sample = [(65,[[0,64,2],[1,63]],[[0,64,3],[1,5,4],[3,64],[4,5],[64]])]
    success = subprocess.run([str(executable)],input=wire(sample),text=True,capture_output=True,
                             timeout=5,env=env)
    assert success.returncode == 0, success.stderr
    allocation_count = int(success.stdout.splitlines()[0].split()[3])
    failing_env = dict(env,ASAN_OPTIONS='detect_leaks=0:halt_on_error=1')
    for allocation in range(1,allocation_count+1):
        failure = subprocess.run([str(executable),str(allocation)],input=wire(sample),
            text=True,capture_output=True,timeout=5,env=failing_env)
        assert failure.returncode == 1 and 'MSOLVE_F2_BITSET_ERROR: allocation failed' in failure.stderr
        assert 'Sanitizer' not in failure.stderr, failure.stderr
    for invalid in range(1,17):
        failure = subprocess.run([str(executable),'0',str(invalid)],input=wire(sample),
            text=True,capture_output=True,timeout=5,env=failing_env)
        assert failure.returncode == 1 and 'MSOLVE_F2_BITSET_ERROR:' in failure.stderr
        assert 'Sanitizer' not in failure.stderr, failure.stderr
    report = dict(status='PASS',matrix_cases=len(inputs),new_pivots_checked=total_pivots,
        zero_output_cases=zero_cases,unsorted_tail_cases=unsorted_cases,
        allocation_failure_cases=allocation_count,invalid_input_mode_cases=16,
        oracle='independent Python set-row Gauss-Jordan elimination',
        actual_kernel_included=True,old_reducers_freed_before_materialization=True,
        borrowed_coefficients_preserved=True,metadata_original_lower_owner_verified=True,
        sanitizers=['address','undefined'],sanitizer_findings=0,
        source_sha256=hashlib.sha256(SOURCE.read_bytes()).hexdigest(),compile_command=command,
        full_board_solver_runs=0)
    (HERE/'exact_msolve_f2_matrix_review_results.json').write_text(json.dumps(report,indent=2)+'\n')
    (HERE/'exact_msolve_f2_matrix_review.log').write_text(result.stderr+json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))


if __name__ == '__main__':
    main()
