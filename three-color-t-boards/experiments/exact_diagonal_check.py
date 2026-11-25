#!/usr/bin/env python3
"""Independent checks of diagonal schedule, fixed data, and count scope."""
import itertools,json,random,subprocess,sys,tempfile
from collections import Counter
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'sources/anc'))
from count_extensions import count_extensions
from exact_cover_check import patterns


def main():
 boards,_,_=count_extensions(2,[]);assert len(boards)==168
 with tempfile.TemporaryDirectory(prefix='tboards-diagonal-check-')as tmp:
  binary=Path(tmp)/'counter'
  subprocess.run(['g++','-O3','-std=c++23','-Wall','-Wextra','-Wpedantic','-Werror',str(ROOT/'experiments/exact_diagonal.cpp'),'-o',str(binary)],check=True)
  def run(q,flags=(),reverse=0,flow=1,seconds=15):
   cmd=[str(binary),'--colors',str(q),'--seconds',str(seconds),'--reverse',str(reverse),'--flow',str(flow),*flags]
   result=subprocess.run(cmd,capture_output=True,text=True)
   if result.returncode not in(0,1):raise RuntimeError(result.stderr)
   return result.returncode,dict(t.split('=',1)for t in result.stdout.strip().split())
  for reverse,flow in itertools.product(range(2),repeat=2):
   code,result=run(2,reverse=reverse,flow=flow);assert code==0 and result['exact_count']=='168'
   code,result=run(2,['--normalize-apex','1'],reverse,flow);assert code==0 and result['exact_count']=='84'and result['unrestricted_labeled_count']=='168'
  print('binary168 inbothdirections, with/withoutflow, apex84x2 PASS',flush=True)
  reference=Counter(''.join(map(str,b[:4]))for b in boards)
  for prefix in map(''.join,itertools.product('01',repeat=4)):
   code,result=run(2,['--prefix',prefix]);assert code==0 and int(result['exact_count'])==reference[prefix]
  randomizer=random.Random(20261122)
  for trial in range(20):
   indices=randomizer.sample(range(25),trial%12)
   source=boards[trial*7%168];mask=''.join(str(source[i])if i in indices else'.'for i in range(25))
   expected=sum(all(str(board[i])==mask[i]for i in indices)for board in boards)
   for reverse in range(2):
    code,result=run(2,['--fixed',mask],reverse);assert code==0 and int(result['exact_count'])==expected
  print('all16 binaryprefixes and20arbitraryfixedmasks agreewith independentenumeration PASS',flush=True)
  data=json.loads((ROOT/'sources/anc/certificates.json').read_text())
  for name,rows in data['ternary_prefixes'].items():
   for reverse in range(2):
    code,result=run(3,['--prefix',''.join(rows)],reverse);assert code==0 and result['exact_count']=='2'
    print('ternaryprefix',name,'direction',reverse,'exact2 PASS',json.dumps(result),flush=True)
  fixture=(ROOT/'experiments/exact_cover_product_fixture.txt').read_text().splitlines()
  holes=[i for i in range(100)if fixture[0][i]!=fixture[1][i]];assert len(holes)==4
  mask=''.join('.'if i in holes else c for i,c in enumerate(fixture[0]));expected=0
  for colors in itertools.product('012',repeat=4):
   board=list(fixture[0])
   for i,c in zip(holes,colors):board[i]=c
   expected+=len(set(patterns(''.join(board),3)))==81
  for reverse in range(2):
   code,result=run(3,['--fixed',mask],reverse);assert code==0 and int(result['exact_count'])==expected
  print('arbitraryternarymask agreeswith independent81-assignmentcheck:',expected,'PASS',flush=True)
  code,result=run(3,['--normalize-apex','1'],seconds=0.000001)
  assert code==1 and result['status']=='INCOMPLETE'and'exact_count'not in result and'unrestricted_labeled_count'not in result
  print('timeout reports onlycompletedleaves; noexacttotal PASS',flush=True)


if __name__=='__main__':main()
