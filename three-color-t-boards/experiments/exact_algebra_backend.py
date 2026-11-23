#!/usr/bin/env python3
"""Exact local Singular backend plus arbitrary-precision monomial counting.

Ternary Fourier variables are ordinary polynomial variables with cubic
root-of-unity domains. They are never put in a Boolean ring.
"""
import argparse,functools,hashlib,itertools,json,math,os,re,resource,subprocess,time
from pathlib import Path
ROOT=Path(__file__).resolve().parent
LOCAL=ROOT/'exact_algebra_backend_root'
SINGULAR=LOCAL/'usr/bin/Singular'


def monomial_dimension(leading,variables,seconds=60):
    """Count standard monomials exactly, using Python arbitrary-size integers."""
    leading=[tuple(g)for g in leading]
    if any(len(g)!=variables or any(e<0 for e in g)for g in leading):raise ValueError('invalid exponent vector')
    if any(not any(g)for g in leading):return 0,dict(states=0)
    bounds=[None]*variables
    for g in leading:
        support=[i for i,e in enumerate(g)if e]
        if len(support)==1:
            i=support[0];bounds[i]=g[i]if bounds[i]is None else min(bounds[i],g[i])
    if any(b is None for b in bounds):raise ValueError('leading ideal has no pure-power bound for every variable')
    started=time.monotonic();states=0
    @functools.lru_cache(None)
    def visit(bounds,generators):
        nonlocal states
        states+=1
        if states%256==0 and time.monotonic()-started>seconds:raise TimeoutError('standard-monomial counter time limit')
        if any(not any(g)for g in generators):return 0
        bounds=list(bounds)
        for g in generators:
            support=[i for i,e in enumerate(g)if e]
            if len(support)==1:bounds[support[0]]=min(bounds[support[0]],g[support[0]])
        kept=[]
        for g in sorted(set(generators),key=lambda x:(sum(x),x)):
            if any(e>=b for e,b in zip(g,bounds)):continue
            if not any(all(a<=b for a,b in zip(h,g))for h in kept):kept.append(g)
        if not kept:return math.prod(bounds)
        active=[i for i in range(len(bounds))if any(g[i]for g in kept)]
        factor=math.prod(bounds[i]for i in range(len(bounds))if i not in active)
        if len(active)<len(bounds):
            return factor*visit(tuple(bounds[i]for i in active),tuple(tuple(g[i]for i in active)for g in kept))
        j=max(range(len(bounds)),key=lambda i:sum(bool(g[i])for g in kept))
        rest=tuple(bounds[:j]+bounds[j+1:]);total=0
        for exponent in range(bounds[j]):
            constraints=tuple(sorted(set(g[:j]+g[j+1:]for g in kept if g[j]<=exponent)))
            total+=visit(rest,constraints)
        return total
    result=visit(tuple(bounds),tuple(sorted(set(leading))))
    return result,dict(states=states,cache_hits=visit.cache_info().hits,elapsed_seconds=time.monotonic()-started)


def monomial(term):
    factors=[f'x{i+1}'+(f'^{e}'if e!=1 else'')for i,e in term if e]
    return '*'.join(factors)or'1'


def packed_polynomial(terms,n,bits):
    result=[]
    for encoded in terms:
        word=int(encoded,16);pairs=[]
        for i in range(n):
            e=(word>>(bits*i))&((1<<bits)-1)
            if bits==2 and e==3:raise ValueError('unexpected exponent3 in reduced encoding')
            if e:pairs.append((i,e))
        if word>>(bits*n):raise ValueError('monomial exceeds variable count')
        result.append(monomial(pairs))
    return '+'.join(result)or'0'


def prime_definitions(model,prefix):
    """Import freshly generated prime-characteristic geometry, never F2 reductions."""
    import exact_prime_fourier as generator
    prime=int(model.split(':',1)[1])
    all_moments=model.startswith('prime-all:')
    if len(prefix)>100 or any(c not in'012'for c in prefix):raise ValueError('invalid fixed ternary prefix')
    rows=math.isqrt(len(prefix))
    if rows*rows!=len(prefix):raise ValueError('prime model currently requires a prefix of complete rows')
    data=generator.generate_model(prime,prefix=[prefix[r*r:(r+1)**2]for r in range(rows)],all_moments=all_moments)
    expected_moments=80 if all_moments else 40
    assert data['coefficient_characteristic']==prime and len(data['moment_equations'])==expected_moments
    assert len(data['domain_equations'])==len(data['free_original_cells'])==data['variables']
    n=data['variables'];extension=False;polynomials=[]
    for equation in data['moment_equations']:
        pieces=[]
        for term in equation['terms']:
            u,v=term['coefficient'];u%=prime;v%=prime
            if not(u or v):continue
            extension|=bool(v)
            pairs=term['monomial']
            if any(not(0<=i<n)or e not in(1,2)for i,e in pairs):raise ValueError('invalid prime monomial')
            coefficient=f'({u}+{v}*a)'if v else str(u)
            pieces.append(coefficient+'*'+monomial(pairs))
        if equation.get('rhs',[0,0])!=[0,0]:raise ValueError('unexpected nonzero Fourier right-hand side')
        if pieces:polynomials.append('+'.join(pieces))
    equations=[f'x{i+1}^3-1'for i in range(n)]+polynomials
    if n==0:n=1;equations.insert(0,'x1')
    field=f'F{prime}'+('^2'if extension else'')
    coefficient=f'({prime},a)'if extension else str(prime)
    definition=f'ring R={coefficient},('+','.join(f'x{i+1}'for i in range(n))+'),dp;\n'
    if extension:definition+='minpoly=a^2+a+1;\n'
    definition+='ideal I=\n'+',\n'.join(equations)+';\n'
    source=Path(generator.__file__)
    metadata=dict(model=model,field=field,characteristic=prime,variables=n,generators=len(equations),fourier_moments=expected_moments,prefix=prefix,free_original_cells=data['free_original_cells'],color_map=['1','a','-a-1'],generator=str(source),generator_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),model_data_sha256=hashlib.sha256(json.dumps(data,sort_keys=True).encode()).hexdigest(),meaning='fresh geometric Fourier moments with coefficients modulo the specified prime; ordinary cubic domains')
    metadata.update(count_scope=data['count_scope'],fixed_prefix_rows=rows,fixed_cell_count=len(prefix),fixed_original_cells=list(range(len(prefix))))
    if not prefix:assert n==100 and len(equations)==100+expected_moments and not extension
    return definition,metadata


def definitions(model,prefix='',field='F2',normalize_apex=False):
    if normalize_apex and model!='ternary-original':raise ValueError('apex normalization is supported only for ternary-original')
    if model.startswith(('prime:','prime-all:')):return prime_definitions(model,prefix)
    metadata=dict(model=model,field=field)
    sources={'binary-reduced':'exact_parity_math_reduced_2.json','ternary-reduced':'exact_parity_math_fourier_reduced.json','ternary-original':'exact_parity_math_fourier_original.json','ternary-prefix':'exact_parity_math_fourier_original.json'}
    if model in sources:
        source=ROOT/sources[model];metadata.update(source=str(source),source_sha256=hashlib.sha256(source.read_bytes()).hexdigest())
    if model=='binary-reduced':
        d=json.loads((ROOT/'exact_parity_math_reduced_2.json').read_text());n=d['variables'];field='F2'
        equations=[f'x{i+1}^2+x{i+1}'for i in range(n)]
        equations += [packed_polynomial(e['terms'],n,1)for e in d['equations']]
        metadata['meaning']='binary Boolean ANF, including every Boolean field equation'
    elif model=='ternary-reduced':
        d=json.loads((ROOT/'exact_parity_math_fourier_reduced.json').read_text());n=d['variables'];field='F2'
        equations=[f'x{i+1}^3+1'for i in range(n)]
        equations += [packed_polynomial(e['terms'],n,2)for e in d['remaining_equations']]
        assert n==96 and len(equations)==136
        metadata['meaning']='ordinary F2 polynomial ring; 96 free cubic domains plus all40 exported equations'
    elif model in ('ternary-original','ternary-prefix'):
        d=json.loads((ROOT/'exact_parity_math_fourier_original.json').read_text())
        if model=='ternary-original':
            n=d['variables'];equations=[f'x{i+1}^3+1'for i in range(n)]
            equations += ['+'.join(monomial(term)for term in e['terms'])or'0'for e in d['moment_equations']]
            assert n==100 and len(equations)==140
            if normalize_apex:equations.append('x1+1');metadata['unrestricted_multiplier']=3
        else:
            if not prefix or len(prefix)>100 or any(c not in'012'for c in prefix):raise ValueError('invalid fixed ternary prefix')
            field='F4';free=list(range(len(prefix),100));index={cell:i for i,cell in enumerate(free)};n=max(1,len(free))
            equations=[f'x{i+1}^3+1'for i in range(n)]if free else['x1']
            for equation in d['moment_equations']:
                terms={}
                for original in equation['terms']:
                    power=0;term=[]
                    for cell,e in original:
                        if cell<len(prefix):power+=int(prefix[cell])*e
                        else:term.append((index[cell],e))
                    key=tuple(term);coefficient=(1,2,3)[power%3];terms[key]=terms.get(key,0)^coefficient
                pieces=[]
                for term,coefficient in sorted(terms.items()):
                    if not coefficient:continue
                    factor=('', 'a*','(a+1)*')[coefficient-1]
                    pieces.append(factor+monomial(term))
                if pieces:equations.append('+'.join(pieces))
            metadata['prefix']=prefix;metadata['color_map']=['1','a','a+1']
    elif model.startswith('fixture:'):
        name=model.split(':',1)[1]
        fixtures={
            'domain1':(1,['x1^3+1']),
            'domain2':(2,['x1^3+1','x2^3+1']),
            'diagonal':(2,['x1^3+1','x2^3+1','x1+x2']),
            'cyclotomic':(1,['x1^3+1','x1^2+x1+1']),
            'fourier3':(3,['x1^3+1','x2^3+1','x3^3+1','x1+x2+x3']),
            'fourier3-reduced':(2,['x1^3+1','x2^3+1','(x1+x2)^3+1']),
            'gf4-linear':(1,['x1^3+1','x1+a']),
            'zero':(1,['x1^3+1','1']),
            'bigint-product':(10,[f'x{i+1}^100+1'for i in range(10)]),
            'huge-domains':(100,[f'x{i+1}^3+1'for i in range(100)]),
        }
        if name not in fixtures:raise ValueError('unknown fixture')
        n,equations=fixtures[name]
        if name=='gf4-linear':field='F4'
    else:raise ValueError('unknown model')
    metadata.update(variables=n,generators=len(equations),field=field)
    names=','.join(f'x{i+1}'for i in range(n));coefficient='2'if field=='F2'else'(2,a)'
    text=f'ring R={coefficient},({names}),dp;\n'
    if field=='F4':text+='minpoly=a^2+a+1;\n'
    text+='ideal I=\n'+',\n'.join(equations)+';\n'
    return text,metadata


def singular_script(definition,algorithm='std',export_basis=True,small_vdim=False):
    if algorithm not in('std','slimgb'):raise ValueError('unknown standard-basis algorithm')
    script=definition+'option(redSB);\nprint("GB_STARTED");\nideal G='+algorithm+'(I);\nprint("GB_COMPLETE");\n'
    script+='print("BASIS_IS_STANDARD="+string(attrib(G,"isSB")));\nprint("KRULL_DIM="+string(dim(G)));\nprint("BASIS_SIZE="+string(size(G)));\n'
    if export_basis:script+='for(int k=1;k<=size(G);k++){if(G[k]==0){ERROR("zero polynomial in standard basis export");}print("LM="+string(leadexp(G[k])));}\n'
    script+='print("LM_COMPLETE");\nprint("HILB_STARTED");\nbigintvec H=hilb(G,2);\nprint("HILB_TYPE="+typeof(H));\nbigint D=0;\nfor(int j=1;j<size(H);j++){D=D+H[j];}\nprint("HILB_DIM="+string(D));\n'
    if small_vdim:script+='print("VDIM_DIAGNOSTIC="+string(vdim(G)));\n'
    script+='print("BACKEND_COMPLETE");\nquit;\n';return script


def run(model,output,timeout=60,memory_mb=2048,algorithm='std',prefix='',field='F2',normalize_apex=False,prepare_only=False):
    definition,metadata=definitions(model,prefix,field,normalize_apex)
    script=singular_script(definition,algorithm,small_vdim=model.startswith('fixture:')and model not in('fixture:huge-domains','fixture:bigint-product'))
    output=Path(output);source=output.with_suffix('.sing');source.write_text(script)
    metadata.update(algorithm=algorithm,ordering='dp',ring_type='ordinary polynomial ring',command=[str(SINGULAR),'-q'],script_sha256=hashlib.sha256(script.encode()).hexdigest(),script=str(source),timeout_seconds=timeout,memory_mb=memory_mb,basis_complete=False,standard_basis_complete=False,leading_export_complete=False,dimension_complete=False)
    if prepare_only:metadata['status']='PREPARED_NOT_RUN';output.with_suffix('.json').write_text(json.dumps(metadata,indent=2)+'\n');return metadata
    metadata['status']='RUNNING';output.with_suffix('.json').write_text(json.dumps(metadata,indent=2)+'\n')
    env=os.environ.copy();env['LD_LIBRARY_PATH']=str(LOCAL/'usr/lib')+(':'+env['LD_LIBRARY_PATH']if env.get('LD_LIBRARY_PATH')else'')
    env['SINGULARPATH']=str(LOCAL/'usr/share/singular/LIB')
    def limits():resource.setrlimit(resource.RLIMIT_AS,(memory_mb*1024*1024,)*2)
    started=time.monotonic();before=resource.getrusage(resource.RUSAGE_CHILDREN)
    timed_out=False
    try:
        process=subprocess.run([str(SINGULAR),'-q'],input=script,text=True,capture_output=True,timeout=timeout,env=env,preexec_fn=limits)
        log=process.stdout+process.stderr;metadata['returncode']=process.returncode
    except subprocess.TimeoutExpired as exc:
        timed_out=True;log=(exc.stdout or b'').decode()if isinstance(exc.stdout,bytes)else(exc.stdout or'')
        if exc.stderr:log+=exc.stderr.decode()if isinstance(exc.stderr,bytes)else exc.stderr
    metadata['wall_timeout_reached']=timed_out
    diagnostics=[line for line in log.splitlines()if line.lstrip().startswith('?')or re.search(r'\berror\b|overflow|segmentation fault|aborted',line,re.I)]
    fields={line.split('=',1)[0]:line.split('=',1)[1]for line in log.splitlines()if'='in line and not line.startswith('LM=')}
    basis_complete=not diagnostics and 'GB_COMPLETE'in log and 'LM_COMPLETE'in log and fields.get('BASIS_IS_STANDARD')=='1'
    metadata['basis_complete']=basis_complete
    metadata['standard_basis_complete']=not diagnostics and 'GB_COMPLETE'in log and fields.get('BASIS_IS_STANDARD')=='1'
    if diagnostics or metadata.get('returncode',0):
        metadata.update(status='BACKEND_ERROR',error_diagnostics=diagnostics)
    elif basis_complete:
        try:
            leading=[list(map(int,line[3:].split(',')))for line in log.splitlines()if line.startswith('LM=')]
            if len(leading)!=int(fields['BASIS_SIZE']):raise ValueError('incomplete leading-ideal export')
            metadata['leading_export_complete']=True
            leading_record=dict(format='leading-monomial-ideal-v1',variables=metadata['variables'],standard_basis_complete=True,leading_monomials=leading,provenance=dict(script_sha256=metadata['script_sha256'],algorithm=algorithm,field=metadata['field']))
            leading_path=output.with_suffix('.leading.json');leading_path.write_text(json.dumps(leading_record,indent=2)+'\n')
            exact,counter=monomial_dimension(leading,metadata['variables'],seconds=timeout)
            from exact_standard_monomials import count_standard_monomials
            independent_stats={}
            independent=count_standard_monomials(leading,variables=metadata['variables'],standard_basis_complete=True,stats=independent_stats,max_states=1000000)
            if independent!=exact:raise RuntimeError(f'independent monomial counters disagree: {independent}, {exact}')
            metadata.update(leading_monomials_file=str(leading_path),monomial_dimension=exact,monomial_counter=counter,independent_monomial_dimension=independent,independent_monomial_counter=independent_stats,krull_dimension=int(fields['KRULL_DIM']),basis_size=int(fields['BASIS_SIZE']))
            if timed_out:metadata.update(status='COMPLETE_FROM_LEADING_IDEAL',hilbert_status='TIMEOUT',quotient_dimension=exact,dimension_decimal=str(exact))
            elif 'BACKEND_COMPLETE'not in log or fields.get('HILB_TYPE')!='bigintvec':metadata['status']='BACKEND_ERROR'
            else:
                expected=int(fields['HILB_DIM'])
                if exact!=expected:raise RuntimeError(f'Hilbert and monomial counts disagree: {expected}, {exact}')
                metadata.update(status='COMPLETE',quotient_dimension=exact,dimension_decimal=str(exact),hilbert_dimension=expected)
                if'VDIM_DIAGNOSTIC'in fields:metadata['vdim_diagnostic']=int(fields['VDIM_DIAGNOSTIC'])
            if metadata.get('unrestricted_multiplier') and metadata.get('quotient_dimension')is not None:
                metadata['unrestricted_labeled_count']=metadata['unrestricted_multiplier']*exact
        except (TimeoutError,ValueError,RuntimeError,RecursionError,MemoryError,ImportError)as exc:
            metadata.update(status='POSTPROCESS_ERROR',postprocess_error=f'{type(exc).__name__}: {exc}')
    else:metadata['status']='INCOMPLETE_STANDARD_BASIS_TIMEOUT'if timed_out else'BACKEND_ERROR'
    metadata['dimension_complete']=metadata['status']in('COMPLETE','COMPLETE_FROM_LEADING_IDEAL')
    after=resource.getrusage(resource.RUSAGE_CHILDREN);metadata['child_cpu_seconds']=after.ru_utime+after.ru_stime-before.ru_utime-before.ru_stime;metadata['elapsed_seconds']=time.monotonic()-started
    output.with_suffix('.log').write_text(log);output.with_suffix('.json').write_text(json.dumps(metadata,indent=2)+'\n');return metadata


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--model',required=True);p.add_argument('--output',type=Path,required=True);p.add_argument('--timeout',type=float,default=60);p.add_argument('--memory-mb',type=int,default=2048);p.add_argument('--algorithm',choices=('std','slimgb'),default='std');p.add_argument('--prefix',default='');p.add_argument('--field',choices=('F2','F4'),default='F2');p.add_argument('--normalize-apex',action='store_true');p.add_argument('--prepare-only',action='store_true');a=p.parse_args()
    result=run(a.model,a.output,a.timeout,a.memory_mb,a.algorithm,a.prefix,a.field,a.normalize_apex,a.prepare_only)
    print(json.dumps({k:v for k,v in result.items()if k not in('leading_monomials','prefix')},indent=2))
    if result['status']not in('COMPLETE','COMPLETE_FROM_LEADING_IDEAL','PREPARED_NOT_RUN'):raise SystemExit(1)

if __name__=='__main__':main()
