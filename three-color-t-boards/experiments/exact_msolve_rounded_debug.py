#!/usr/bin/env python3
"""Bounded diagnostic reproduction; this script never accepts or counts a basis."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import resource
import signal
import subprocess
import time

ROOT = Path(__file__).resolve().parent
OUT = ROOT / 'exact_msolve_full_prime2_reduced_all_rounded_debug'
EXE = (ROOT / 'exact_msolve_rounded_promotion_tools/msolve').resolve()
SOURCE = ROOT / 'exact_msolve_full_prime2_reduced_all_rounded.ms'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=OUT)
    out = parser.parse_args().output
    for suffix in ('.ms', '.basis', '.log', '.json'):
        if out.with_suffix(suffix).exists():
            raise ValueError('refusing to overwrite diagnostic artifacts')
    data = SOURCE.read_bytes()
    out.with_suffix('.ms').write_bytes(data)
    command = ['/usr/bin/gdb', '-nx', '-batch',
               '-ex', 'set pagination off', '-ex', 'set confirm off',
               '-ex', 'set debuginfod enabled off', '-ex', 'run',
               '-ex', 'thread apply all bt 12', '-ex', 'frame 0',
               '-ex', 'x/6i $pc', '-ex', 'info registers r12 rsi rdi rax',
               '-ex', 'p $_siginfo',
               '-ex', 'info args', '-ex', 'info locals',
               '--args', str(EXE), '-g', '1', '-l', '2', '-t', '1',
               '-r', '1', '-c', '0', '-v', '2', '-m', '16',
               '-f', str(out.with_suffix('.ms')),
               '-o', str(out.with_suffix('.basis'))]
    env = os.environ.copy()
    env['LD_LIBRARY_PATH'] = ':'.join(str(ROOT / part) for part in
        ('exact_algebra_backend_root/usr/lib', 'exact_msolve_tools/usr/lib'))
    def limits():
        resource.setrlimit(resource.RLIMIT_AS, (2048*1024**2,)*2)
        resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
    start = time.monotonic()
    process = subprocess.Popen(command, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT, text=True, env=env, preexec_fn=limits,
        start_new_session=True)
    timed_out = False
    try:
        log, _ = process.communicate(timeout=180)
    except subprocess.TimeoutExpired:
        timed_out = True
        pending, descendants = [process.pid], []
        while pending:
            parent = pending.pop()
            for children in Path(f'/proc/{parent}/task').glob('*/children'):
                try:
                    found = [int(pid) for pid in children.read_text().split()]
                except FileNotFoundError:
                    continue
                for pid in found:
                    if pid not in descendants:
                        descendants.append(pid)
                        pending.append(pid)
        for pid in reversed(descendants):
            try:
                os.kill(pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
        os.killpg(process.pid, signal.SIGKILL)
        log, _ = process.communicate()
    out.with_suffix('.log').write_text(log)
    result = dict(status='DEBUG_ONLY_NO_COUNT', command=command,
                  input_sha256=hashlib.sha256(data).hexdigest(),
                  diagnostic_script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  executable_sha256=hashlib.sha256(EXE.read_bytes()).hexdigest(),
                  address_space_limit_mb=2048, wall_limit_seconds=180,
                  debugger_returncode=process.returncode, timed_out=timed_out,
                  elapsed_seconds=time.monotonic()-start,
                  basis_accepted=False, full_count_computed=False)
    out.with_suffix('.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
