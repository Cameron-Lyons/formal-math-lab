#!/usr/bin/env python3
"""Finite outer guard covering the algebra process and Python postprocessing."""
import argparse,json,os,resource,signal,subprocess,sys,time
from pathlib import Path

def main():
 p=argparse.ArgumentParser(description=__doc__)
 p.add_argument('--output',type=Path,required=True)
 p.add_argument('--outer-seconds',type=float,default=180)
 p.add_argument('--outer-memory-mb',type=int,default=2048)
 p.add_argument('--backend',choices=['singular','msolve'],default='singular')
 p.add_argument('backend_arguments',nargs=argparse.REMAINDER)
 a=p.parse_args()
 args=a.backend_arguments
 if args and args[0]=='--':args=args[1:]
 if '--output'in args:raise ValueError('pass the output path only to the guard')
 if a.outer_seconds<=0 or a.outer_memory_mb<=0:raise ValueError('positive outer limits required')
 script='exact_algebra_backend.py'if a.backend=='singular'else'exact_msolve_backend.py'
 command=[sys.executable,str(Path(__file__).with_name(script)),*args,'--output',str(a.output)]
 def limits():resource.setrlimit(resource.RLIMIT_AS,(a.outer_memory_mb*1024**2,)*2)
 start=time.monotonic();before=resource.getrusage(resource.RUSAGE_CHILDREN)
 child=subprocess.Popen(command,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True,start_new_session=True,preexec_fn=limits)
 exhausted=False
 try:stdout,stderr=child.communicate(timeout=a.outer_seconds)
 except subprocess.TimeoutExpired:
  exhausted=True;os.killpg(child.pid,signal.SIGKILL);stdout,stderr=child.communicate()
 after=resource.getrusage(resource.RUSAGE_CHILDREN)
 result=dict(command=command,outer_wall_limit_seconds=a.outer_seconds,outer_memory_mb=a.outer_memory_mb,returncode=child.returncode,outer_wall_limit_reached=exhausted,elapsed_seconds=time.monotonic()-start,process_tree_cpu_seconds=after.ru_utime+after.ru_stime-before.ru_utime-before.ru_stime,status='OUTER_LIMIT_INCOMPLETE'if exhausted else'OUTER_PROCESS_FINISHED')
 metadata_path=a.output.with_suffix('.json')
 if metadata_path.exists():result['backend_status']=json.loads(metadata_path.read_text()).get('status')
 a.output.with_suffix('.outer.json').write_text(json.dumps(result,indent=2)+'\n')
 a.output.with_suffix('.outer.log').write_text(stdout+stderr)
 print(json.dumps(result,indent=2))
 raise SystemExit(1 if exhausted else child.returncode)

if __name__=='__main__':main()
