#!/usr/bin/env python3
"""Reproduce the guarded six-row fiber integration, with explicit timeout scope."""
import json,subprocess,tempfile,resource,time
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]

def main():
 prefix=json.loads((ROOT/'splice_witnesses.json').read_text())['groups'][0]['prefix']
 with tempfile.TemporaryDirectory(prefix='tboards-tworow-integrated-')as tmp:
  binary=Path(tmp)/'counter'
  subprocess.run(['g++','-O3','-std=c++23','-Wall','-Wextra','-Wpedantic','-Werror','-DTWO_START_ROW=6',str(ROOT/'experiments/exact_tworow_search.cpp'),'-o',str(binary)],check=True)
  args=[str(binary),prefix,'0','0'];started=time.monotonic();before=resource.getrusage(resource.RUSAGE_CHILDREN)
  try:
   run=subprocess.run(args,text=True,capture_output=True,timeout=90,check=True)
   stats=dict(t.split('=',1)for t in run.stdout.split());assert stats['status']=='COMPLETE'and stats['count']=='138'
   record=dict(region='known six-row group1',arguments=args[1:],stats=stats)
   print(run.stdout,flush=True)
  except subprocess.TimeoutExpired:
   record=dict(region='known six-row group1',arguments=args[1:],status='INCOMPLETE',reason='external90secondguard')
   print('INCOMPLETE: 90-second wall-time guard; no exact count',flush=True)
  after=resource.getrusage(resource.RUSAGE_CHILDREN)
  record['elapsed_wall_seconds']=time.monotonic()-started
  record['child_cpu_seconds']=after.ru_utime+after.ru_stime-before.ru_utime-before.ru_stime
  (ROOT/'experiments/exact_tworow_integrated_benchmark.json').write_text(json.dumps(record,indent=2)+'\n')

if __name__=='__main__':main()
