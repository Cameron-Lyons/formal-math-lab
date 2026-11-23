#!/usr/bin/env python3
"""Exact terminal-DP checks against independent full-board row enumeration."""
import itertools,json,random,subprocess,sys,tempfile
from collections import Counter
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'sources/anc'))
from count_extensions import count_extensions


def main():
 with tempfile.TemporaryDirectory(prefix='tboards-lastrow-check-')as tmp:
  binary=Path(tmp)/'terminal';reference=Path(tmp)/'reference'
  for source,target in [('exact_lastrow.cpp',binary),('exact_algo_count.cpp',reference)]:
   subprocess.run(['g++','-O3','-std=c++20','-Wall','-Wextra','-Wpedantic',str(ROOT/'experiments'/source),'-o',str(target)],check=True)
  boards,_,_=count_extensions(2,[]);expected=Counter(''.join(map(str,b[:16]))for b in boards)
  prefixes=list(map(''.join,itertools.product('01',repeat=16)))
  for depth in [0,4,7]:
   run=subprocess.run([str(binary),'2',str(depth),'1000000'],input='\n'.join(prefixes)+'\n',capture_output=True,text=True,check=True)
   counts=list(map(int,run.stdout.split()));assert len(counts)==65536
   assert all(c==expected[p]for p,c in zip(prefixes,counts))and sum(counts)==168
   print(f'All 65,536 binary prefixes agree independently; cache depth {depth}; total 168 PASS',flush=True)
   print(run.stderr.strip(),flush=True)
  data=json.loads((ROOT/'sources/anc/certificates.json').read_text())
  ternary=[''.join(rows[:9])for rows in data['ternary_seeds']]
  group=json.loads((ROOT/'splice_further.json').read_text())['groups'][8]
  endings=Counter(t[:45]for t in group['tails']);tail,count=endings.most_common(1)[0]
  assert count==6;ternary.append(group['prefix']+tail)
  sample=json.loads((ROOT/'splice_witnesses.json').read_text())['groups']
  for group in sample:
   ternary.extend(group['prefix']+tail[:45]for tail in group['tails'][:2])
  ternary=list(dict.fromkeys(ternary));want=[]
  for prefix in ternary:
   run=subprocess.run([str(reference),'--colors','3','--rows','10','--prefix',prefix],capture_output=True,text=True,check=True)
   fields=dict(t.split('=',1)for t in run.stdout.split());assert fields['status']=='COMPLETE'
   want.append(int(fields['exact_count_completed_interval']))
  for depth in [0,8,17]:
   run=subprocess.run([str(binary),'3',str(depth),'1000000'],input='\n'.join(ternary+ternary)+'\n',capture_output=True,text=True,check=True)
   got=list(map(int,run.stdout.split()));assert got==want+want
   print(f'{len(ternary)} ternary prefixes, repeated to exercise reuse, agree with independent counter; cache depth {depth}; max count {max(want)} PASS',flush=True)
   print(run.stderr.strip(),flush=True)


if __name__=='__main__':main()
