#!/usr/bin/env python3
import argparse,json,subprocess,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]

def main():
 p=argparse.ArgumentParser();p.add_argument('--seconds',type=float,default=10);p.add_argument('--flow',type=int,choices=(0,1),default=0);p.add_argument('--output',type=Path,default=ROOT/'experiments/exact_diagonal_benchmark.json');a=p.parse_args()
 x=json.loads((ROOT/'sources/anc/certificates.json').read_text());results=[]
 with tempfile.TemporaryDirectory(prefix='tboards-diagonal-benchmark-')as tmp:
  binary=Path(tmp)/'counter'
  subprocess.run(['g++','-O3','-std=c++23','-Wall','-Wextra','-Wpedantic','-Werror',str(ROOT/'experiments/exact_diagonal.cpp'),'-o',str(binary)],check=True)
  regions=[(name,['--prefix',''.join(rows)])for name,rows in x['ternary_prefixes'].items()]+[('unrestricted_apex0',['--normalize-apex','1'])]
  for region,flags in regions:
   for reverse in [0,1]:
    args=[str(binary),'--colors','3','--seconds',str(a.seconds),'--reverse',str(reverse),'--flow',str(a.flow),*flags]
    run=subprocess.run(args,capture_output=True,text=True)
    if run.returncode not in (0,1):raise RuntimeError(run.stderr)
    fields=dict(t.split('=',1)for t in run.stdout.strip().split())
    if region!='unrestricted_apex0'and fields['status']=='COMPLETE':assert fields['exact_count']=='2'
    results.append(dict(region=region,arguments=args[1:],stats=fields));a.output.write_text(json.dumps(results,indent=2)+'\n')
    print(region,run.stdout.strip(),flush=True)

if __name__=='__main__':main()
