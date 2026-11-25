#!/usr/bin/env python3
"""One bounded deterministic GANAK probe of the full-label branch3 CNF.
No installation, symmetry normalization, prefix restriction, or count factor.
"""
from pathlib import Path
from itertools import product
import argparse,hashlib,json,os,re,resource,signal,subprocess,sys,time
from exact_count_cnf import make_cnf

HERE=Path(__file__).resolve().parent
STEM=HERE/'exact_f3_branch3_ganak'
BINARY=HERE/'exact_count_tools/ganak'
BINARY_SHA='e7a3c6a66377db349939ceb01c78783767fbca5a3ef3dad66cbc6cf11f2daf58'
SIX_PREFIX='100011101011000101010011112112211212021201221022121202020220010222002102100022222'

def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def save(path,obj):path.write_text(json.dumps(obj,indent=2)+'\n')
def available_kib():return int(next(x.split()[1] for x in Path('/proc/meminfo').read_text().splitlines() if x.startswith('MemAvailable:')))
def write_cnf(path,variables,clauses,comments):
    with path.open('x') as f:
        for c in comments:f.write('c '+c+'\n')
        f.write(f'p cnf {variables} {len(clauses)}\n')
        for clause in clauses:f.write(' '.join(map(str,clause))+' 0\n')
def read_cnf(path):
    clauses=[];header=None
    for line in path.read_text().splitlines():
        if line.startswith('c'):continue
        if line.startswith('p cnf'):header=tuple(map(int,line.split()[2:]));continue
        values=list(map(int,line.split()));assert values[-1]==0 and all(values[:-1])
        clauses.append(values[:-1])
    assert header and len(clauses)==header[1]
    assert max(abs(v) for c in clauses for v in c)<=header[0]
    return header,clauses

def prepare():
    for suffix in ('.cnf','.audit.json','.help.log','.version.log','.known_prefix.cnf'):
        assert not STEM.with_suffix(suffix).exists(),suffix
    assert BINARY.is_file() and os.access(BINARY,os.X_OK) and sha(BINARY)==BINARY_SHA
    help_run=subprocess.run([str(BINARY),'--help'],capture_output=True,text=True,timeout=10)
    version=subprocess.run([str(BINARY),'--version'],capture_output=True,text=True,timeout=10)
    assert help_run.returncode==version.returncode==0
    help_text=help_run.stdout+help_run.stderr
    for flag in ('--prob','--mode','--arjun','--puura','--td','--threads','--maxcache','--appmct'):
        assert flag in help_text
    STEM.with_suffix('.help.log').write_text(help_text)
    STEM.with_suffix('.version.log').write_text(version.stdout+version.stderr)
    cnf,cells=make_cnf(3,[],canonical=False,occurrence_amo='tree',orbit_canonical=False)
    assert set(cells)==set(range(100))
    assert all(cells[pos]==[3*pos+c+1 for c in range(3)] for pos in range(100))
    base_clauses=len(cnf.clauses);base_variables=cnf.variables;extra=[]
    for a,b in ((0,3),(1,6),(2,7)):
        for color in range(3):
            extra.append([-cells[a][color],cells[b][color]])
            extra.append([cells[a][color],-cells[b][color]])
    for color in range(3):extra.append([-cells[3][color],-cells[8][color]])
    assert len(extra)==21
    for clause in extra:cnf.add(clause)
    path=STEM.with_suffix('.cnf')
    write_cnf(path,cnf.variables,cnf.clauses,[
        'Full labeled ternary boards in branch3; no prefix or symmetry normalization.',
        'c0=c3, c1=c6, c2=c7, c3!=c8. Every auxiliary is functional.',
        'Count multiplier1 divisor1; all Boolean variables are counted.'])
    header,actual=read_cnf(path)
    assert header==(13341,59308) and cnf.variables==base_variables
    assert actual[:base_clauses]==cnf.clauses[:base_clauses]
    assert actual[base_clauses:]==extra
    # Independent finite relation audit of the clauses read back from disk.
    involved=[0,1,2,3,6,7,8];accepted=[]
    for values in product(range(3),repeat=7):
        board=dict(zip(involved,values))
        assignment={3*pos+c+1:board[pos]==c for pos in involved for c in range(3)}
        satisfies=all(any(assignment[abs(v)]==(v>0) for v in clause) for clause in actual[base_clauses:])
        semantic=(board[0]==board[3] and board[1]==board[6] and board[2]==board[7] and board[3]!=board[8])
        assert satisfies==semantic
        if satisfies:accepted.append(values)
    assert len(accepted)==54
    prefix=[int(x) for x in SIX_PREFIX]
    known_values=tuple(prefix[p] for p in involved)
    assert known_values not in accepted
    assignment={3*pos+c+1:prefix[pos]==c for pos in involved for c in range(3)}
    bad=next((i,c) for i,c in enumerate(extra) if not any(assignment[abs(v)]==(v>0) for v in c))
    prefix_units=[[cells[pos][color]] for pos,color in enumerate(prefix)]
    write_cnf(STEM.with_suffix('.known_prefix.cnf'),cnf.variables,actual+prefix_units,[
        'Unsolved check fixture: original known six-completion prefix plus branch3 is contradictory.',
        'The relation-table audit already proves zero; no second GANAK call is made.'])
    # Explicit three-clause contradiction: c0=1, c3=0 violate equality via
    # [-cell0color1,cell3color1], and the cell3 one-hot excludes color1.
    assert prefix[0]==1 and prefix[3]==0
    equality=[-cells[0][1],cells[3][1]]
    exclusion=[-cells[3][0],-cells[3][1]]
    assert equality in extra and exclusion in actual[:base_clauses]
    audit={
      'status':'PASS','scope':'full-label branch3 Boolean model; no solver result',
      'variables':cnf.variables,'clauses':len(actual),'base_variables':base_variables,
      'base_clauses':base_clauses,'branch_clause_count':21,'branch_new_variables':0,
      'one_hot_cells':100,'cell_colors':3,'pattern_placements':81,
      'generator_call':"make_cnf(3, [], canonical=False, occurrence_amo='tree', orbit_canonical=False)",
      'base_auxiliary_count_semantics':'All selector and AMO-tree auxiliaries are defined by biconditionals; ordinary all-variable count is parsimonious.',
      'branch_id':3,'branch_conditions':['c0=c3','c1=c6','c2=c7','c3!=c8'],
      'original_placement_cells':[[0,1,2,3],[3,6,7,8]],
      'fixed_prefix':[],'palette_canonical':False,'reflection_canonical':False,
      'independent_support_projection':False,'count_multiplier':1,'count_divisor':1,
      'all_actual_branch_clauses':extra,'relation_cells':involved,
      'ternary_relation_assignments_checked':3**7,'accepted_relation_assignments':len(accepted),
      'actual_dimacs_readback_checked':True,'all_base_clauses_retained':True,
      'known_six_prefix':SIX_PREFIX,'known_prefix_expected_branch_count':0,
      'known_prefix_check_method':'exhaustive seven-cell relation audit and explicit equality/one-hot conflict, no solver',
      'known_prefix_falsified_clause':{'branch_clause_index':bad[0],'clause':bad[1]},
      'known_prefix_conflict_clauses':[equality,exclusion,[cells[0][1]],[cells[3][0]]],
      'known_prefix_fixture_sha256':sha(STEM.with_suffix('.known_prefix.cnf')),
      'input_sha256':sha(path),'binary_sha256':BINARY_SHA,
      'base_generator_sha256':sha(HERE/'exact_count_cnf.py'),
      'probe_generator_sha256':sha(Path(__file__)),
      'help_sha256':sha(STEM.with_suffix('.help.log')),
      'version_sha256':sha(STEM.with_suffix('.version.log')),
      'full_branch_count_status':'UNEVALUATED',
    }
    save(STEM.with_suffix('.audit.json'),audit)
    print(json.dumps({'status':'PREPARED','variables':cnf.variables,'clauses':len(actual),
                      'relation_assignments_checked':2187,'known_prefix_branch_count':0,
                      'input_sha256':audit['input_sha256']},indent=2))

def limits():
    resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2)
    resource.setrlimit(resource.RLIMIT_CORE,(0,0))

def worker():
    status_path=STEM.with_suffix('.status.json');log_path=STEM.with_suffix('.log')
    assert not status_path.exists() and not log_path.exists()
    audit=json.loads(STEM.with_suffix('.audit.json').read_text());path=STEM.with_suffix('.cnf')
    assert sha(path)==audit['input_sha256'] and sha(BINARY)==BINARY_SHA
    assert audit['status']=='PASS' and not audit['fixed_prefix'] and not audit['palette_canonical'] and not audit['reflection_canonical']
    mem=available_kib()
    command=[str(BINARY),'--prob','0','--mode','0','--arjun','0','--puura','0','--td','0',
             '--threads','1','--maxcache','128','--appmct','-1',str(path)]
    record={'status':'RUNNING','scope':'full-label branch3, not unrestricted total N',
      'branch_id':3,'command':command,'input_sha256':sha(path),'binary_sha256':BINARY_SHA,
      'audit_sha256':sha(STEM.with_suffix('.audit.json')),
      'variables':audit['variables'],'clauses':audit['clauses'],
      'prefix':[],'palette_canonical':False,'reflection_canonical':False,
      'count_multiplier':1,'count_divisor':1,'threads':1,
      'deterministic_prob_zero':True,'approximate_fallback_disabled':True,
      'child_wall_limit_seconds':60,'outer_wall_limit_seconds':90,
      'address_space_limit_bytes':512*1024**2,'maxcache_megabytes':128,
      'mem_available_kib_before_launch':mem,'minimum_required_kib':1536*1024,
      'solver_invocations':0,'count_complete':False,'branch_count_decimal':None}
    if mem<1536*1024:
        record['status']='SKIPPED_INSUFFICIENT_MEMORY';save(status_path,record);print(json.dumps(record));return
    record['solver_invocations']=1;save(status_path,record)
    env=os.environ.copy();env['OMP_NUM_THREADS']='1';env['OPENBLAS_NUM_THREADS']='1'
    start=time.monotonic();before=resource.getrusage(resource.RUSAGE_CHILDREN)
    with log_path.open('x') as log:
        try:
            result=subprocess.run(command,stdout=log,stderr=subprocess.STDOUT,timeout=60,
                                  preexec_fn=limits,env=env)
            record['returncode']=result.returncode;record['status']='INCOMPLETE_COUNTER_ERROR'
        except subprocess.TimeoutExpired:
            record['status']='UNKNOWN_TIMEOUT';record['returncode']=None
        except OSError as error:
            record['status']='SKIPPED_UNRUNNABLE';record['launch_error']=str(error)
    after=resource.getrusage(resource.RUSAGE_CHILDREN)
    record['wall_seconds']=time.monotonic()-start
    record['cpu_seconds']=after.ru_utime+after.ru_stime-before.ru_utime-before.ru_stime
    log=log_path.read_text(errors='replace')
    counts=re.findall(r'^c s exact arb int (\d+)$',log,re.M)
    errors=[line for line in log.splitlines() if re.search(r'\berror\b|fatal|out of memory|cannot allocate|bad_alloc|assertion|segmentation|aborted',line,re.I)]
    record['exact_count_lines']=counts;record['error_diagnostics']=errors;record['log_sha256']=sha(log_path)
    if record.get('returncode')==0 and record['status']!='UNKNOWN_TIMEOUT' and len(counts)==1 and not errors:
        record.update(status='COMPLETE_EXACT_COUNTER_RESULT',count_complete=True,branch_count_decimal=str(int(counts[0])))
    save(status_path,record);print(json.dumps(record,indent=2))

def outer():
    for suffix in ('.outer.json','.outer.log','.status.json','.log'):
        assert not STEM.with_suffix(suffix).exists(),suffix
    command=[sys.executable,str(Path(__file__).absolute()),'--worker']
    started=time.monotonic();status={'command':command,'outer_limit_seconds':90,'status':'RUNNING'}
    with STEM.with_suffix('.outer.log').open('x') as log:
        p=subprocess.Popen(command,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
        try:
            status['returncode']=p.wait(timeout=90);status['status']='WORKER_FINISHED'
        except subprocess.TimeoutExpired:
            os.killpg(p.pid,signal.SIGKILL);p.wait();status['status']='UNKNOWN_OUTER_TIMEOUT';status['returncode']=p.returncode
    status['wall_seconds']=time.monotonic()-started
    if status['status']=='UNKNOWN_OUTER_TIMEOUT':
        old=json.loads(STEM.with_suffix('.status.json').read_text()) if STEM.with_suffix('.status.json').exists() else {}
        old.update(status='UNKNOWN_OUTER_TIMEOUT',count_complete=False,branch_count_decimal=None)
        save(STEM.with_suffix('.status.json'),old)
    save(STEM.with_suffix('.outer.json'),status)
    print(json.dumps(status,indent=2))

def main():
    parser=argparse.ArgumentParser();mode=parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--prepare',action='store_true');mode.add_argument('--run',action='store_true');mode.add_argument('--worker',action='store_true')
    args=parser.parse_args()
    if args.prepare:prepare()
    elif args.worker:worker()
    else:outer()
if __name__=='__main__':main()
