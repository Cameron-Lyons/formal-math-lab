#!/usr/bin/env python3
"""Independent checks of colored exact cover, propagation, and factoring."""
import itertools,json,subprocess,sys,tempfile
from collections import Counter
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'sources/anc'))
from count_extensions import count_extensions


def patterns(board,q):
 h=q*q+1;cells={(j-r,-r):int(board[r*r+j]) for r in range(h)for j in range(2*r+1)}
 out=[]
 for r in range(1,h):
  for j in range(2*r-1):
   x,y=j+1-r,-r
   out.append(tuple(cells[p]for p in [(x,y+1),(x-1,y),(x,y),(x+1,y)]))
 return out


def main():
 boards,nodes,_=count_extensions(2,[])
 assert len(boards)==168
 expected=Counter(''.join(map(str,b[:4]))for b in boards)
 strong=['--branch-cells','1','--flow','1','--hall','81','--components','1','--memo','100000']
 with tempfile.TemporaryDirectory(prefix='tboards-cover-check-')as tmp:
  binary=Path(tmp)/'counter'
  subprocess.run(['g++','-O3','-std=c++23','-Wall','-Wextra','-Wpedantic','-Werror',str(ROOT/'experiments/exact_cover.cpp'),'-o',str(binary)],check=True)
  def run(q,prefix='',extra=(),limit=30):
   r=subprocess.run([str(binary),'--colors',str(q),'--prefix',prefix,'--seconds',str(limit),*extra],capture_output=True,text=True)
   if r.returncode not in (0,1):raise RuntimeError(r.stderr)
   fields=dict(t.split('=',1)for t in r.stdout.strip().split())
   assert fields['status']=='COMPLETE',fields
   return int(fields['count']),fields
  for mode in ['hybrid','position','pattern']:
   assert run(2,extra=['--mode',mode])[0]==168
  assert run(2,extra=strong)[0]==168
  print('unrestricted binary168: allthree primary modes and allfilters/factoring PASS',flush=True)
  for prefix in map(''.join,itertools.product('01',repeat=4)):
   assert run(2,prefix,strong)[0]==expected[prefix]
  print('all16 binary prefixfibers agree with independent rowenumeration PASS',flush=True)
  data=json.loads((ROOT/'sources/anc/certificates.json').read_text())
  for name,rows in data['ternary_prefixes'].items():
   value,stats=run(3,''.join(rows),strong)
   assert value==2
   print('published ternary prefix',name,'count2 PASS',json.dumps(stats),flush=True)
  board=''.join(data['ternary_seeds'][0]);assert run(3,board,strong)[0]==1
  invalid=list(board);invalid[0]=str((int(invalid[0])+1)%3);invalid=''.join(invalid)
  assert len(set(patterns(invalid,3)))<81
  assert run(3,invalid,strong)[0]==0
  print('full valid board1 and independently invalid board0 PASS',flush=True)
  fixture=ROOT/'experiments/exact_cover_product_fixture.txt'
  inputs=fixture.read_text().splitlines();support=[set(p)for p in zip(*(patterns(w,3)for w in inputs))]
  choices=[sorted({w[i]for w in inputs})for i in range(100)]
  expected_product=0;assignments=0
  for digits in itertools.product(*choices):
   assignments+=1;codes=patterns(''.join(digits),3)
   expected_product+=len(set(codes))==81 and all(p in s for p,s in zip(codes,support))
  assert assignments==16 and expected_product==4
  assert run(3,extra=['--supports-file',str(fixture)])[0]==4
  value,stats=run(3,extra=[*strong,'--supports-file',str(fixture)])
  assert value==4 and int(stats['component_splits'])>=1 and int(stats['component_max'])==2
  print('independent16-assignment fixture:4solutions, factor2x2 PASS',flush=True)


if __name__=='__main__':main()
