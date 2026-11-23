#!/usr/bin/env python3
"""At most two bounded, deterministic parity-circuit counting trials."""
import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT/'experiments'


def run(name, seconds):
    path = OUT/f'exact_parity_{name}.cnf'
    log = OUT/f'exact_parity_{name}.log'
    command = ['timeout','--kill-after=2s',str(seconds),str(OUT/'exact_count_tools/ganak'),
               '--prob','0','--arjun','0','--puura','0','--td','0','--maxcache','512',
               '--polar','3','--verb','2',str(path)]
    started = time.monotonic()
    with log.open('w') as output:
        process = subprocess.Popen(command,stdout=output,stderr=subprocess.STDOUT,start_new_session=True)
        _,status,usage = os.wait4(process.pid,0)
        code = os.waitstatus_to_exitcode(status)
        process.returncode = code
    contents = log.read_text()
    match = re.search(r'^c s exact arb int (\d+)$',contents,re.M)
    count = int(match[1]) if match and code == 0 else None
    rdb = re.findall(r'rdb: (\d+)',contents)
    conflicts = re.findall(r'^c o conflicts\s+(\d+)',contents,re.M)
    result = dict(variant=name,input=str(path.relative_to(ROOT)),
                  input_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
                  command=command,log=str(log.relative_to(ROOT)),
                  status='complete' if count is not None else
                  ('timeout' if code in (124,137,-9) else 'failed'),
                  exact_count=count,exit_code=code,limit_wall_seconds=seconds,
                  wall_seconds=round(time.monotonic()-started,3),
                  user_seconds=round(usage.ru_utime,3),system_seconds=round(usage.ru_stime,3),
                  cpu_seconds=round(usage.ru_utime+usage.ru_stime,3),max_rss_kb=usage.ru_maxrss,
                  passed_initial_sat='[bce]' in contents or bool(rdb or match),
                  counting_search_observed=bool(rdb or conflicts or match),
                  last_recorded_rdb=int(rdb[-1]) if rdb else None,
                  last_recorded_conflicts=int(conflicts[-1]) if conflicts else None,
                  native_xor_or_gaussian_counting=False)
    print(json.dumps(result),flush=True)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--seconds',type=int,default=90)
    args = parser.parse_args()
    if not 1 <= args.seconds <= 90:
        parser.error('wall limits must lie between 1 and 90 seconds')
    checks = json.loads((OUT/'exact_parity_check_results.json').read_text())
    for connected in (False,True):
        for orbit,expected in [(False,168),(True,42)]:
            assert any(r['case']=='binary' and r['layout']=='chain' and
                       r['connected']==connected and r['orbit']==orbit and
                       r['exact_count']==expected for r in checks)
    with ThreadPoolExecutor(max_workers=2) as pool:
        results = list(pool.map(lambda name:run(name,args.seconds),('chain','connected')))
    (OUT/'exact_parity_runs.json').write_text(json.dumps(results,indent=2)+'\n')


if __name__ == '__main__':
    main()
