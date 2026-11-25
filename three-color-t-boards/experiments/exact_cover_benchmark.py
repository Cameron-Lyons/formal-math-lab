#!/usr/bin/env python3
"""Bounded benchmarks for independent colored exact-cover counter."""
import argparse,json,subprocess,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]

def main():
 p=argparse.ArgumentParser();p.add_argument('--seconds',type=float,default=15);p.add_argument('--output',type=Path,default=ROOT/'experiments/exact_cover_benchmark.json');p.add_argument('--suite',choices=('fixed','unrestricted'),default='fixed');a=p.parse_args()
 data=json.loads((ROOT/'sources/anc/certificates.json').read_text())
 configs=[('plain',[]),('cells',['--cells','1']),('hall24',['--cells','1','--hall','24']),('hall81',['--cells','1','--hall','81']),('cellbranch',['--branch-cells','1']),('cellbranch_hall',['--branch-cells','1','--hall','81'])]
 prefixes=[(k,''.join(v)) for k,v in data['ternary_prefixes'].items()] if a.suite=='fixed' else [('unrestricted','')]
 results=[]
 with tempfile.TemporaryDirectory(prefix='tboards-cover-benchmark-') as tmp:
  binary=Path(tmp)/'counter'
  subprocess.run(['g++','-O3','-std=c++23','-Wall','-Wextra','-Wpedantic','-Werror',str(ROOT/'experiments/exact_cover.cpp'),'-o',str(binary)],check=True)
  for name,prefix in prefixes:
   for config,extra in configs:
    args=[str(binary),'--colors','3','--prefix',prefix,'--seconds',str(a.seconds),*extra]
    run=subprocess.run(args,capture_output=True,text=True)
    if run.returncode not in (0,1):raise RuntimeError(run.stderr)
    fields=dict(item.split('=',1) for item in run.stdout.strip().split())
    if a.suite=='fixed' and fields['status']=='COMPLETE':assert fields['count']=='2',fields
    result=dict(region=name,config=config,arguments=args[1:],exit_code=run.returncode,stats=fields)
    results.append(result);a.output.write_text(json.dumps(results,indent=2)+'\n')
    print(name,config,run.stdout.strip(),flush=True)

if __name__=='__main__':main()
