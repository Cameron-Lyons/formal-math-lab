#!/usr/bin/env python3
"""Independent validation of exact interleaved two-row counting."""
import itertools,json,subprocess,sys,tempfile
from collections import Counter
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'sources/anc'))
from count_extensions import count_extensions


def main():
 with tempfile.TemporaryDirectory(prefix='tboards-tworow-check-')as tmp:
  binary=Path(tmp)/'counter';search=Path(tmp)/'search';reference=Path(tmp)/'reference'
  for source,target in [('exact_tworow_count.cpp',binary),('exact_tworow_search.cpp',search),('exact_algo_count.cpp',reference)]:
   subprocess.run(['g++','-O3','-std=c++20','-Wall','-Wextra','-Wpedantic',str(ROOT/'experiments'/source),'-o',str(target)],check=True)
  boards,_,_=count_extensions(2,[]);expected=Counter(''.join(map(str,b[:9]))for b in boards);prefixes=list(map(''.join,itertools.product('01',repeat=9)))
  def batch(q,prefixes,depth,endpoints=1):
   run=subprocess.run([str(binary),str(q),str(depth),'1000000','90',str(endpoints)],input='\n'.join(prefixes)+'\n',text=True,capture_output=True,timeout=90,check=True)
   fields=[dict(t.split('=',1)for t in line.split())for line in run.stdout.splitlines()];assert len(fields)==len(prefixes)and all(s['status']=='COMPLETE'for s in fields)
   return [int(s['count'])for s in fields],run.stderr.strip()
  for depth in [0,8,12]:
   for endpoints in [0,1]:
    got,stats=batch(2,prefixes,depth,endpoints);assert all(c==expected[p]for c,p in zip(got,prefixes))and sum(got)==168
    print(f'All512 binary prefixes agree; depth={depth}, endpoint pruning={endpoints}; total168 PASS',stats,flush=True)
  data=json.loads((ROOT/'sources/anc/certificates.json').read_text());regions=[''.join(rows[:8])for rows in data['ternary_seeds']]
  for name,index in [('splice_extension.json',14),('splice_further.json',92)]:
   group=json.loads((ROOT/name).read_text())['groups'][index];tail=Counter(t[:28]for t in group['tails']).most_common(1)[0][0];regions.append(group['prefix']+tail)
  images=[];want=[]
  for prefix in regions:
   run=subprocess.run([str(reference),'--colors','3','--rows','10','--prefix',prefix,'--seconds','90'],text=True,capture_output=True,timeout=90,check=True)
   fields=dict(t.split('=',1)for t in run.stdout.split());assert fields['status']=='COMPLETE';value=int(fields['exact_count_completed_interval'])
   for permutation in itertools.permutations('012'):
    recolored=''.join(permutation[int(c)]for c in prefix)
    for reflected in [False,True]:
     images.append(''.join(recolored[r*r:(r+1)**2][::-1]for r in range(8))if reflected else recolored);want.append(value)
  for depth in [0,16,32]:
   for endpoints in [0,1]:
    got,stats=batch(3,images+images,depth,endpoints);assert got==want+want
    print(f'84 ternary symmetry images repeated, counts up to10 agree; depth={depth}, endpoint pruning={endpoints} PASS',stats,flush=True)
  for name,rows in data['ternary_prefixes'].items():
   run=subprocess.run([str(search),''.join(rows),'0','0'],text=True,capture_output=True,timeout=90,check=True)
   fields=dict(t.split('=',1)for t in run.stdout.split());assert fields['status']=='COMPLETE'and fields['count']=='2'
   print('Published7-row prefix',name,'exhaustive count2 PASS',run.stdout.strip(),flush=True)


if __name__=='__main__':main()
