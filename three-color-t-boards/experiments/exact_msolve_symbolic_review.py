#!/usr/bin/env python3
"""Independent seventh-build reserve, staging, and allocation-failure audit."""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

import exact_msolve_staged_review as previous

HERE=Path(__file__).resolve().parent
SOURCE=HERE/'exact_msolve_symbolic_reserve_tools/msolve-cc044551f8e202d00691990fd3fd0b1226a88ea2/src/neogb/hash.c'

ROW_CHECKS=r'''
static md_t metadata(ht_t *t){md_t md={0};md.ht=t;md.fc=3;md.laopt=2;md.nthrds=1;md.print_gb=1;return md;}
static void row_case(hl_t capacity,hl_t load,len_t length,hl_t wanted) {
 count_calls=0;ht_t t=table(capacity,3);t.eld=load;ht_t original=t;
 for(hl_t id=1;id<load;id++){
  t.hd[id]=(hd_t){(uint32_t)id,(uint32_t)id+3,(uint32_t)id+5,(uint32_t)id+7};
  t.ev[id][0]=(exp_t)id;t.ev[id][1]=(exp_t)(id>>16);t.ev[id][2]=37;
  t.hmap[id]=(hi_t)id;
 }
 hm_t poly[OFFSET]={0};poly[LENGTH]=length;md_t md=metadata(&t);
 allocation_calls=0;count_calls=1;reserve_symbolic_row_capacity(&t,poly,&md);count_calls=0;
 assert(t.esz==wanted&&t.eld==load&&t.eld+(hl_t)length<t.esz);
 assert(t.hsz>=2*t.esz&&!(t.hsz&(t.hsz-1)));verify_scalars(&t,&original);
 for(hl_t id=1;id<load;id++){
  assert(t.hd[id].val==id&&t.hd[id].deg==id+3&&t.hd[id].sdm==id+5&&t.hd[id].idx==id+7);
  assert(t.ev[id][0]==(exp_t)id&&t.ev[id][1]==(exp_t)(id>>16)&&t.ev[id][2]==37);
  assert(t.hmap[id]==id);
 }
 for(hl_t id=0;id<t.esz;id++)assert(t.ev[id]==t.ev[0]+id*3);
 if(capacity==wanted)assert(allocation_calls==0);else assert(allocation_calls==3||allocation_calls==4);
 destroy(&t);
}
static void check_row_reserve(void) {
 row_case(8,6,1,8);row_case(8,6,2,16);row_case(32768,32760,7,32768);
 row_case(32768,32760,8,65536);row_case(65536,65530,5,65536);
 row_case(65536,65530,6,131072);row_case(131072,131060,12,196608);
 row_case(196608,196600,8,262144);
 ht_t t=table(8,3);t.eld=6;hm_t poly[OFFSET]={0};poly[LENGTH]=8;
 for(int mode=0;mode<8;mode++){
  md_t md=metadata(&t);
  if(mode==0)md.fc=5;
  if(mode==1)md.laopt=1;
  if(mode==2)md.nthrds=2;
  if(mode==3)md.trace_level=1;
  if(mode==4)md.nf=1;
  if(mode==5)md.in_final_reduction_step=1;
  if(mode==6)md.nev=1;
  if(mode==7)md.print_gb=0;
  ht_t old=t;allocation_calls=0;count_calls=1;
  reserve_symbolic_row_capacity(&t,poly,&md);count_calls=0;
  assert(!memcmp(&t,&old,sizeof(t))&&allocation_calls==0);
 }destroy(&t);
}
static void row_failure(const char *which,int number) {
 count_calls=0;ht_t t=table(8,3);t.eld=6;hm_t poly[OFFSET]={0};poly[LENGTH]=5;
 md_t md=metadata(&t);allocation_calls=0;count_calls=1;fail_call=number;
 if(!strcmp(which,"allocate")){
  reserve_symbolic_row_capacity(&t,poly,&md);printf("ROW_ALLOCATIONS=%d\n",allocation_calls);return;
 }
 if(!strcmp(which,"null-metadata"))reserve_symbolic_row_capacity(&t,poly,NULL);
 else if(!strcmp(which,"wrong-owner")){md.ht=NULL;reserve_symbolic_row_capacity(&t,poly,&md);}
 else if(!strcmp(which,"null-poly"))reserve_symbolic_row_capacity(&t,NULL,&md);
 else if(!strcmp(which,"oversized-row")){poly[LENGTH]=UINT32_MAX;reserve_symbolic_row_capacity(&t,poly,&md);}
 else if(!strcmp(which,"zero-load")){t.eld=0;reserve_symbolic_row_capacity(&t,poly,&md);}
 else if(!strcmp(which,"zero-quantum"))reserve_hash_table_checked(&t,3,0,0,"TEST");
 else if(!strcmp(which,"nonpower-quantum"))reserve_hash_table_checked(&t,3,3,0,"TEST");
 else if(!strcmp(which,"large-quantum"))reserve_hash_table_checked(&t,3,131072,0,"TEST");
 else if(!strcmp(which,"null-context"))reserve_hash_table_checked(&t,3,65536,0,NULL);
 else assert(!"unknown row failure");
 assert(!"invalid row reserve accepted");
}
static void plan(hl_t capacity,hl_t load,len_t length) {
 ht_t t=table(8,3);t.esz=capacity;t.eld=load;t.hsz=2;
 while(t.hsz<2*capacity)t.hsz*=2;
 hm_t poly[OFFSET]={0};poly[LENGTH]=length;md_t md=metadata(&t);md.info_level=2;
 allocation_calls=0;count_calls=1;fail_call=1;
 reserve_symbolic_row_capacity(&t,poly,&md);assert(!"plan expected first allocation failure");
}
'''


def main():
    source=SOURCE.read_text()
    markers=['static void reserve_hash_table_checked(',
        'static void reserve_basis_hash_table_for_promotion(',
        'static void reserve_symbolic_row_capacity(',
        'static void *symbolic_stage_calloc(',
        'static exp_t *stage_missing_symbolic_exponents(',
        'static inline void switch_used_hcm_data_to_basis_hash_table(']
    functions=[previous.extract(source,m) for m in markers]
    prelude=previous.PRELUDE.replace(
        'typedef struct {len_t ncl,ncr,nc,np; hm_t **tr;} mat_t;',
        'typedef struct {len_t ncl,ncr,nc,np; hm_t **tr;} mat_t;\n'
        'typedef struct {ht_t *ht;int fc,laopt,nthrds,trace_level,nf,in_final_reduction_step,nev,print_gb,info_level;} md_t;\n'
        '#define NO_TRACER 0')
    prelude=prelude.replace('t.esz=capacity;t.hsz=2*capacity;t.eld=1;',
        't.esz=capacity;t.hsz=2;while(t.hsz<2*capacity)t.hsz*=2;t.eld=1;')
    postlude=previous.POSTLUDE.replace(
        'hl_t cap=4;while(cap<=nc)cap*=2;',
        'hl_t cap=4;while(cap<=nc)cap*=2;\n'
        ' if(iteration%31==0&&!fault)cap=6144;\n'
        ' if(iteration%379==0&&!fault){cap=196608;width=3;}')
    postlude=postlude.replace('static int staged_cases=0,unchanged_cases=0,large_resets=0,zero_missing_cases=0;',
        'static int staged_cases=0,unchanged_cases=0,large_resets=0,zero_missing_cases=0,nonpower_stages=0;')
    postlude=postlude.replace('staged_cases++;if(!missing)zero_missing_cases++;',
        'staged_cases++;nonpower_stages+=!!(cap&(cap-1));if(!missing)zero_missing_cases++;')
    postlude=postlude.replace('else if(!strcmp(which,"null-private"))s.hmap=NULL;',
        'else if(!strcmp(which,"null-private"))s.hmap=NULL;\n'
        ' else if(!strcmp(which,"nonpower-buckets"))s.hsz=31;\n'
        ' else if(!strcmp(which,"undersized-buckets"))s.hsz=16;')
    postlude=postlude.replace('int main(int argc,char **argv) {',ROW_CHECKS+'\nint main(int argc,char **argv) {')
    postlude=postlude.replace(' if(argc==3&&!strcmp(argv[1],"fail"))',
        ' if(argc>=3&&!strcmp(argv[1],"row")){row_failure(argv[2],argc>3?atoi(argv[3]):0);return 0;}\n'
        ' if(argc==5&&!strcmp(argv[1],"plan")){plan(strtoull(argv[2],NULL,10),strtoull(argv[3],NULL,10),(len_t)strtoul(argv[4],NULL,10));return 0;}\n'
        ' if(argc==3&&!strcmp(argv[1],"fail"))')
    postlude=postlude.replace(' for(unsigned i=0;i<1200;i++)one_case(i,0);',
        ' check_row_reserve();\n for(unsigned i=0;i<1200;i++)one_case(i,0);\n assert(nonpower_stages>0);')
    postlude=postlude.replace('ZERO_MISSING=%d\\n",staged_cases,unchanged_cases,large_resets,zero_missing_cases);',
        'ZERO_MISSING=%d NONPOWER=%d\\n",staged_cases,unchanged_cases,large_resets,zero_missing_cases,nonpower_stages);')
    c_path=HERE/'exact_msolve_symbolic_review.c';binary=HERE/'exact_msolve_symbolic_review'
    c_path.write_text(prelude+'\n#pragma GCC diagnostic push\n#pragma GCC diagnostic ignored "-Wtype-limits"\n#if defined(__clang__)\n#pragma clang diagnostic ignored "-Wtautological-constant-out-of-range-compare"\n#endif\n'+'\n\n'.join(functions)+'\n#pragma GCC diagnostic pop\n'+postlude)
    command=['cc','-std=c23','-O1','-g','-Wall','-Wextra','-Wpedantic','-Werror',
        '-fsanitize=address,undefined',str(c_path),'-o',str(binary)]
    compiled=subprocess.run(command,capture_output=True,text=True,check=True)
    logs=[compiled.stdout+compiled.stderr]
    def run(args):
        result=subprocess.run([str(binary)]+args,capture_output=True,text=True,
                              env=dict(os.environ,ASAN_OPTIONS='detect_leaks=1'))
        logs.append('COMMAND '+repr(args)+'\n'+result.stdout+result.stderr)
        assert 'AddressSanitizer' not in result.stderr and 'runtime error:' not in result.stderr,result
        return result
    valid=run([]);assert valid.returncode==0,valid
    paths={}
    for name,prefix in [('promotion',['fail']),('symbolic-row',['row','allocate'])]:
        ok=run(prefix+['0']);assert ok.returncode==0,ok
        calls=int(ok.stdout.strip().split('=')[-1]);paths[name]=calls
        for i in range(1,calls+1):
            failed=run(prefix+[str(i)])
            assert failed.returncode==1 and 'Error:' in failed.stderr and not failed.stdout,(name,i,failed)
    invalid=['nonpower','bad-load','bad-mask','duplicate-inverse','out-of-range-inverse','wrong-missing',
        'wrong-new-map','nonflat-pointer','zero-width','overflow','null-private','nonpower-buckets','undersized-buckets']
    for case in invalid:
        failed=run(['invalid',case]);assert failed.returncode==1 and 'Error:' in failed.stderr,failed
    row_invalid=['null-metadata','wrong-owner','null-poly','oversized-row','zero-load',
        'zero-quantum','nonpower-quantum','large-quantum','null-context']
    for case in row_invalid:
        failed=run(['row',case]);assert failed.returncode==1 and 'Error:' in failed.stderr,failed
    plans=[]
    for capacity,load,length in [(2097152,2080795,55218),(4194304,4194200,55124),(65536,65535,1)]:
        failed=run(['plan',str(capacity),str(load),str(length)])
        assert failed.returncode==1 and 'cannot allocate promotion hash metadata' in failed.stderr
        target=((load+length+1+65535)//65536)*65536
        assert f'requested_capacity={target}' in failed.stdout
        plans.append(dict(old_capacity=capacity,load=load,row_length=length,requested_capacity=target))
    report=dict(status='PASS',source_sha256=hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
        extracted_functions_sha256=hashlib.sha256('\n\n'.join(functions).encode()).hexdigest(),
        valid_staging_cases=1200,case_summary=valid.stdout.strip(),row_capacity_boundary_cases=8,
        disabled_mode_cases=8,allocation_failure_points=paths,invalid_staging_layouts=invalid,
        invalid_reservation_cases=row_invalid,large_capacity_plans=plans,
        sanitizers=['address','undefined'],compiler_command=command,
        actual_row_constructor_tested=False,actual_hash_probing_tested=False,
        scope='independent linear lookup/vector reference; owner separately tests actual upstream constructors/probing',
        full_solver_runs=0)
    (HERE/'exact_msolve_symbolic_review.log').write_text('\n'.join(logs))
    (HERE/'exact_msolve_symbolic_review_results.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))


if __name__=='__main__':main()
