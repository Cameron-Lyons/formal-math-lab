#!/usr/bin/env python3
import json,subprocess,tempfile
from collections import Counter
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]

def main():
 certificates=json.loads((ROOT/'sources/anc/certificates.json').read_text())
 regions=[('seed'+str(i+1),''.join(rows[:8]))for i,rows in enumerate(certificates['ternary_seeds'])]
 for name,index in [('splice_extension.json',14),('splice_further.json',92)]:
  g=json.loads((ROOT/name).read_text())['groups'][index];tails=Counter(t[:28]for t in g['tails']);tail,n=tails.most_common(1)[0]
  regions.append((name+':'+str(index),g['prefix']+tail))
 results=[]
 with tempfile.TemporaryDirectory(prefix='tboards-tworow-benchmark-')as tmp:
  binary=Path(tmp)/'counter';reference=Path(tmp)/'reference'
  for source,target in [('exact_tworow_count.cpp',binary),('exact_algo_count.cpp',reference)]:
   subprocess.run(['g++','-O3','-std=c++20','-Wall','-Wextra','-Wpedantic',str(ROOT/'experiments'/source),'-o',str(target)],check=True)
  for name,prefix in regions:
   r=subprocess.run([str(reference),'--colors','3','--rows','10','--prefix',prefix,'--seconds','90'],text=True,capture_output=True,timeout=95,check=True)
   base=dict(t.split('=',1)for t in r.stdout.split());assert base['status']=='COMPLETE';expected=int(base['exact_count_completed_interval'])
   print(name,'row-major',r.stdout.strip(),flush=True)
   for depth in [0,16,32]:
    run=subprocess.run([str(binary),'3',str(depth),'1000000','90'],input=prefix+'\n',text=True,capture_output=True,timeout=95,check=True)
    stats=dict(t.split('=',1)for t in run.stdout.split());assert stats['status']=='COMPLETE'and int(stats['count'])==expected
    record=dict(region=name,prefix=prefix,depth=depth,reference=base,stats=stats,summary=run.stderr.strip());results.append(record)
    (ROOT/'experiments/exact_tworow_benchmark.json').write_text(json.dumps(results,indent=2)+'\n')
    print(name,'two-row depth',depth,run.stdout.strip(),run.stderr.strip(),flush=True)

if __name__=='__main__':main()
