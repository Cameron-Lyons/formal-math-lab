#!/usr/bin/env python3
from pathlib import Path
import subprocess,os,json,hashlib
R=Path(__file__).resolve().parent
command=['cc','-std=c23','-O1','-g','-Wall','-Wextra','-Wpedantic','-Werror',
 '-fsanitize=address,undefined',str(R/'table_check.c'),'-lm','-o',str(R/'table_check')]
p=subprocess.run(command,capture_output=True,text=True)
(R/'table_check_compile.log').write_text(p.stdout+p.stderr)
assert p.returncode==0,p.stderr
p=subprocess.run([str(R/'table_check')],capture_output=True,text=True,timeout=90)
(R/'table_check.log').write_text(p.stdout+p.stderr)
assert p.returncode==0 and 'Sanitizer' not in p.stderr,p
failures=[]
for mode,count in [('invalid',17),('allocation',10)]:
 for k in range(1,count+1):
  bad=subprocess.run([str(R/'table_check'),mode,str(k)],capture_output=True,text=True,timeout=20,
     env=dict(os.environ,ASAN_OPTIONS='detect_leaks=0'))
  assert bad.returncode==1 and 'Error:' in bad.stderr and 'Sanitizer' not in bad.stderr,(mode,k,bad)
  failures.append(dict(mode=mode,case=k,returncode=bad.returncode,diagnostic=bad.stderr.strip()))
record=dict(status='PASS',scope='actual data.h/hash.c/order.c with typed byte API; no solver',
 actual_sources=['src/neogb/data.h','src/neogb/stored_exp.h','src/neogb/hash.c','src/neogb/order.c'],
 stubs=['CPU/wall clocks return zero'],sanitizers='ASan+UBSan',api_vectors=2032,
 coordinate_values=256,drl_divisibility_lcm_pairs=2100,stages=13,
 nonpower_row_comparisons=1,nonpower_capacity=196608,legacy_capacity=262144,
 complete_actual_tables_compared=150000,subsequent_paths=['clean','grow','copy','reinitialize','generic reset/reinsert'],
 failure_checks=failures,command=command,output=p.stdout.strip(),
 source_sha256=hashlib.sha256((R/'table_check.c').read_bytes()).hexdigest())
(R/'table_check.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(record,indent=2))
