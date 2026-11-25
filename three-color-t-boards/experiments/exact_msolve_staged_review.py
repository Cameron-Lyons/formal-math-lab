#!/usr/bin/env python3
"""Independent compaction/ownership/failure tests using the actual staged helper.

Hash lookup and insertion use a simple linear reference, not upstream probing.
The actual rounded reservation, staging, and support selection are extracted.
Owner tests separately exercise upstream lookup/clean/grow/reuse.
"""
import hashlib
import json
import os
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]
HERE = ROOT / 'experiments'
SOURCE = HERE / 'exact_msolve_staged_promotion_tools/msolve-cc044551f8e202d00691990fd3fd0b1226a88ea2/src/neogb/hash.c'

PRELUDE = r'''
#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef uint64_t hl_t;
typedef uint32_t hi_t;
typedef uint32_t hm_t;
typedef uint32_t len_t;
typedef uint32_t val_t;
typedef uint16_t exp_t;
typedef struct {uint32_t val,deg,sdm,idx;} hd_t;
typedef struct {
 exp_t **ev; hd_t *hd; hi_t *hmap; len_t elo; hl_t eld,esz,hsz;
 len_t ebl; int32_t mo; len_t nv,evl; uint32_t *dm,*dv,ndv,bpv,*rn,rsd;
} ht_t;
typedef struct {len_t ncl,ncr,nc,np; hm_t **tr;} mat_t;
#define OFFSET 6
#define LENGTH 5
#define ERRSTREAM stderr
#define VERBSTREAM stdout
static void *allocations[256];
static size_t allocation_sizes[256];
static int allocation_calls=0, fail_call=0, count_calls=0;
static uint32_t borrowed_rn[128],borrowed_dv[128],borrowed_dm[128];
static int find_allocation(void *p) {
 for(int i=0;i<256;i++)if(allocations[i]==p)return i;
 assert(!"untracked pointer");return -1;
}
static void remember(void *p,size_t n) {
 assert(p);for(int i=0;i<256;i++)if(!allocations[i]){
  allocations[i]=p;allocation_sizes[i]=n;return;
 }assert(!"too many tracked allocations");
}
static int should_fail(void) {
 if(!count_calls)return 0;
 allocation_calls++;return allocation_calls==fail_call;
}
static void *review_calloc(size_t n,size_t width) {
 if(should_fail())return NULL;
 void *p=calloc(n?n:1,width?width:1);assert(p);remember(p,(n?n:1)*(width?width:1));return p;
}
static void *review_realloc(void *p,size_t n) {
 assert(n>0);if(should_fail())return NULL;
 int i=find_allocation(p);void *q=realloc(p,n);assert(q);
 allocations[i]=q;allocation_sizes[i]=n;return q;
}
static void review_free(void *p) {
 if(!p)return;
 assert(p!=borrowed_rn && p!=borrowed_dv && p!=borrowed_dm);
 int i=find_allocation(p);allocations[i]=NULL;allocation_sizes[i]=0;free(p);
}
static void cleanup(void) {
 for(int i=0;i<256;i++)if(allocations[i]){free(allocations[i]);allocations[i]=NULL;}
}
#define calloc review_calloc
#define realloc review_realloc
#define free review_free
static ht_t table(hl_t capacity,len_t width) {
 ht_t t={0};t.esz=capacity;t.hsz=2*capacity;t.eld=1;t.evl=width;
 t.nv=width-1;t.elo=37;t.ebl=0;t.mo=0;t.ndv=5;t.bpv=6;t.rsd=123;
 t.rn=borrowed_rn;t.dv=borrowed_dv;t.dm=borrowed_dm;
 t.hd=calloc(capacity,sizeof(hd_t));t.hmap=calloc(t.hsz,sizeof(hi_t));
 t.ev=calloc(capacity,sizeof(exp_t*));exp_t *block=calloc(capacity*width,sizeof(exp_t));
 for(hl_t i=0;i<capacity;i++)t.ev[i]=block+i*width;
 return t;
}
static val_t hash_vector(const ht_t *t,const exp_t *v) {
 val_t h=0;for(len_t j=0;j<t->evl;j++)h+=t->rn[j]*v[j];return h;
}
static int32_t is_contained_in_hash_table(const exp_t *v,const ht_t *t,
                                         val_t hash,hi_t *position) {
 assert(hash==hash_vector(t,v));
 for(hi_t i=1;i<t->eld;i++)if(!memcmp(v,t->ev[i],t->evl*sizeof(exp_t))){*position=i;return 1;}
 *position=UINT32_MAX;return 0;
}
static hi_t insert_in_hash_table(const exp_t *v,ht_t *t) {
 hi_t pos=0;val_t h=hash_vector(t,v);
 if(is_contained_in_hash_table(v,t,h,&pos))return pos;
 assert(t->eld<t->esz);pos=(hi_t)t->eld++;
 memcpy(t->ev[pos],v,t->evl*sizeof(exp_t));
 t->hd[pos]=(hd_t){h,v[0],pos+3,pos+7};
 hi_t bucket=h;
 for(hl_t step=0;step<t->hsz;step++){
  bucket=(hi_t)((bucket+step)&(t->hsz-1));
  if(!t->hmap[bucket]){t->hmap[bucket]=pos;return pos;}
 }assert(!"reference probe exhausted");return 0;
}
static void destroy(ht_t *t) {free(t->ev[0]);free(t->ev);free(t->hd);free(t->hmap);}
static uint32_t rng=0x4192ae75;
static uint32_t next_random(void){rng^=rng<<13;rng^=rng>>17;rng^=rng<<5;return rng;}
'''

POSTLUDE = r'''
static int staged_cases=0,unchanged_cases=0,large_resets=0,zero_missing_cases=0;
static void verify_scalars(const ht_t *s,const ht_t *old) {
 assert(s->nv==old->nv && s->mo==old->mo && s->evl==old->evl && s->ebl==old->ebl);
 assert(s->rn==old->rn && s->dm==old->dm && s->dv==old->dv);
 assert(s->ndv==old->ndv && s->bpv==old->bpv && s->elo==old->elo && s->rsd==old->rsd);
}
static void one_case(unsigned iteration,int fault) {
 count_calls=0;
 len_t nc=iteration%31==0?2053:8+next_random()%113;
 len_t ncl=next_random()%(nc/3+1),width=1+next_random()%97;
 if(fault){nc=8;ncl=2;width=7;}
 hl_t cap=4;while(cap<=nc)cap*=2;
 ht_t symbolic=table(cap,width),basis=table(fault?4:cap,width);
 for(hi_t id=1;id<=nc;id++){
  for(len_t j=0;j<width;j++)symbolic.ev[id][j]=(exp_t)(id*17+j*53);
  symbolic.hd[id]=(hd_t){id+19,id+23,id+29,0};
 }symbolic.eld=nc+1;
 hi_t *mapping=calloc(nc,sizeof(hi_t));
 for(len_t c=0;c<nc;c++)mapping[c]=c+1;
 for(len_t c=nc-1;c;c--){len_t d=next_random()%(c+1);hi_t tmp=mapping[c];mapping[c]=mapping[d];mapping[d]=tmp;}
 if(iteration%7==0)for(len_t c=0;c<nc;c++)mapping[c]=nc-c;
 for(len_t c=0;c<nc;c++)symbolic.hd[mapping[c]].idx=c;
 uint8_t *selected=calloc(nc,1);
 for(len_t c=ncl;c<nc;c++)selected[c]=(uint8_t)(next_random()%3!=0);
 if(fault)for(len_t c=ncl;c<nc;c++)selected[c]=1;
 if(iteration%13==0&&!fault)memset(selected+ncl,1,nc-ncl);
 if(iteration%17==0&&!fault)memset(selected+ncl,0,nc-ncl);
 /* Existing basis monomials overlap symbolic columns in arbitrary order. */
 for(len_t c=0;c<nc;c++)if((!fault && next_random()%3==0)||(fault&&c==2))
  insert_in_hash_table(symbolic.ev[mapping[c]],&basis);
 hi_t *expected_ids=calloc(nc,sizeof(hi_t));
 exp_t *expected=calloc((size_t)(basis.eld+nc)*width,sizeof(exp_t));
 hl_t before=basis.eld,next_id=before;
 memcpy(expected,basis.ev[0],(size_t)before*width*sizeof(exp_t));
 len_t missing=0,referenced=0;
 for(len_t c=ncl;c<nc;c++)if(selected[c]){
  referenced++;hi_t old_id=0;const exp_t *v=symbolic.ev[mapping[c]];
  if(!is_contained_in_hash_table(v,&basis,hash_vector(&basis,v),&old_id)){
   old_id=(hi_t)next_id++;missing++;memcpy(expected+(size_t)old_id*width,v,width*sizeof(exp_t));
  }expected_ids[c]=old_id;
 }
 /* Some cases force basis growth (including exact boundary), others do not. */
 if((iteration%2==0||fault)&&missing>0){
  hl_t bcap=2;while(bcap<before)bcap*=2;
  if(bcap==before+missing+1)bcap*=2;
  if(before+missing+1>bcap){
   basis.esz=bcap; /* Backing allocation remains larger; real reserve shrinks/grows correctly. */
  }
 }
 if(iteration%19==0&&!fault){
  /* A valid full table of existing terms still needs the requested spare. */
  if(before>1){basis.esz=before;}
 }
 mat_t mat={ncl,nc-ncl,nc,referenced?2:0,NULL};
 if(mat.np){
  mat.tr=calloc(2,sizeof(hm_t*));
  for(len_t i=0;i<2;i++){
   mat.tr[i]=calloc(OFFSET+referenced,sizeof(hm_t));mat.tr[i][LENGTH]=referenced;
   len_t k=0;for(len_t c=nc;c-->ncl;)if(selected[c])mat.tr[i][OFFSET+k++]=c;
  }
 }
 ht_t original_symbolic=symbolic;
 int consume=fault||iteration%5!=1;
 int should_stage=consume && (before>=basis.esz||missing>=basis.esz-before);
 allocation_calls=0;count_calls=1;
 switch_used_hcm_data_to_basis_hash_table(mapping,&basis,&mat,&symbolic,consume?&symbolic:NULL,0);
 count_calls=0;
 assert(basis.eld==next_id && basis.eld<basis.esz);
 for(hl_t id=0;id<next_id;id++)assert(!memcmp(basis.ev[id],expected+(size_t)id*width,width*sizeof(exp_t)));
 for(len_t c=ncl;c<nc;c++)if(selected[c])assert(mapping[c]==expected_ids[c]);
 verify_scalars(&symbolic,&original_symbolic);
 if(should_stage){
  staged_cases++;if(!missing)zero_missing_cases++;
  hl_t reset=cap<2048?cap:2048;large_resets+=cap>2048;
  assert(symbolic.eld==1&&symbolic.esz==reset&&symbolic.hsz==2*reset);
  for(hl_t i=0;i<reset;i++){
   assert(symbolic.ev[i]==symbolic.ev[0]+i*width);
   hd_t zero={0};assert(!memcmp(&symbolic.hd[i],&zero,sizeof(zero)));
   for(len_t j=0;j<width;j++)assert(symbolic.ev[i][j]==0);
  }
  for(hl_t i=0;i<2*reset;i++)assert(symbolic.hmap[i]==0);
 }else{
  unchanged_cases++;assert(symbolic.eld==original_symbolic.eld&&symbolic.esz==cap);
  assert(symbolic.ev==original_symbolic.ev&&symbolic.hd==original_symbolic.hd&&symbolic.hmap==original_symbolic.hmap);
 }
 for(len_t i=0;i<mat.np;i++)free(mat.tr[i]);free(mat.tr);
 free(mapping);free(selected);free(expected_ids);free(expected);destroy(&symbolic);destroy(&basis);
 if(fault)printf("ALLOCATION_CALLS=%d\n",allocation_calls);
}
static void invalid_case(const char *which) {
 ht_t s=table(16,3);s.eld=9;
 hi_t hcm[8];uint8_t used[6]={1,0,1,0,1,0};
 for(hi_t i=1;i<9;i++){s.hd[i].idx=i-1;hcm[i-1]=i;}
 mat_t m={2,6,8,0,NULL};len_t missing=3;
 if(!strcmp(which,"nonpower"))s.esz=15;
 else if(!strcmp(which,"bad-load"))s.eld=8;
 else if(!strcmp(which,"bad-mask"))used[1]=3;
 else if(!strcmp(which,"duplicate-inverse"))s.hd[8].idx=1;
 else if(!strcmp(which,"out-of-range-inverse"))s.hd[8].idx=8;
 else if(!strcmp(which,"wrong-missing"))missing=4;
 else if(!strcmp(which,"wrong-new-map"))hcm[2]=7;
 else if(!strcmp(which,"nonflat-pointer"))s.ev[3]=s.ev[4];
 else if(!strcmp(which,"zero-width"))s.evl=0;
 else if(!strcmp(which,"overflow")){s.esz=UINT64_C(1)<<63;s.hsz=UINT64_C(1)<<63;}
 else if(!strcmp(which,"null-private"))s.hmap=NULL;
 else assert(!"unknown invalid case");
 stage_missing_symbolic_exponents(hcm,used,&m,&s,missing,0);
 assert(!"invalid input accepted");
}
int main(int argc,char **argv) {
 atexit(cleanup);for(int i=0;i<128;i++){borrowed_rn[i]=31+2*i;borrowed_dm[i]=i+51;borrowed_dv[i]=i+71;}
 if(argc==3&&!strcmp(argv[1],"fail")){fail_call=atoi(argv[2]);one_case(2,1);return 0;}
 if(argc==3&&!strcmp(argv[1],"invalid")){invalid_case(argv[2]);return 0;}
 for(unsigned i=0;i<1200;i++)one_case(i,0);
 assert(staged_cases>100&&unchanged_cases>100&&large_resets>0&&zero_missing_cases>0);
 printf("CASES=1200 STAGED=%d UNCHANGED=%d LARGE_RESET=%d ZERO_MISSING=%d\n",staged_cases,unchanged_cases,large_resets,zero_missing_cases);
 return 0;
}
'''


def extract(source, marker):
    start = source.index(marker)
    end = source.index('{', start) + 1
    depth = 1
    while depth:
        depth += (source[end] == '{') - (source[end] == '}')
        end += 1
    return source[start:end]


def main():
    source = SOURCE.read_text()
    functions = [extract(source, marker) for marker in (
        'static void reserve_basis_hash_table_for_promotion(',
        'static void *symbolic_stage_calloc(',
        'static exp_t *stage_missing_symbolic_exponents(',
        'static inline void switch_used_hcm_data_to_basis_hash_table(')]
    c_path = HERE / 'exact_msolve_staged_review.c'
    binary = HERE / 'exact_msolve_staged_review'
    c_path.write_text(PRELUDE+'\n\n'.join(functions)+POSTLUDE)
    command = ['cc','-std=c11','-O1','-g','-Wall','-Wextra','-Werror',
               '-Wno-error=type-limits','-Wno-error=misleading-indentation',
               '-fsanitize=address,undefined',str(c_path),'-o',str(binary)]
    compiled = subprocess.run(command,capture_output=True,text=True,check=True)
    logs = [compiled.stdout+compiled.stderr]
    def run(args):
        result = subprocess.run([str(binary)]+args,capture_output=True,text=True,
                                env=dict(os.environ,ASAN_OPTIONS='detect_leaks=1'))
        logs.append('COMMAND '+repr(args)+'\n'+result.stdout+result.stderr)
        assert 'AddressSanitizer' not in result.stderr and 'runtime error:' not in result.stderr, result
        return result
    valid = run([])
    assert valid.returncode == 0, valid
    count = run(['fail','0'])
    assert count.returncode == 0, count
    calls = int(count.stdout.strip().split('=')[-1])
    for i in range(1,calls+1):
        failed = run(['fail',str(i)])
        assert failed.returncode == 1 and 'Error:' in failed.stderr and not failed.stdout,(i,failed)
    invalid = ['nonpower','bad-load','bad-mask','duplicate-inverse','out-of-range-inverse',
               'wrong-missing','wrong-new-map','nonflat-pointer','zero-width','overflow','null-private']
    for name in invalid:
        failed = run(['invalid',name])
        assert failed.returncode == 1 and 'Error:' in failed.stderr and not failed.stdout,(name,failed)
    report = dict(status='PASS',source_sha256=hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
        extracted_functions_sha256=hashlib.sha256('\n\n'.join(functions).encode()).hexdigest(),
        valid_cases=1200,case_summary=valid.stdout.strip(),allocation_failure_points=calls,
        invalid_layout_cases=invalid,sanitizers=['address','undefined'],
        compiler_command=command,independent_lookup='linear equality lookup with hash verification',
        actual_upstream_lookup_tested=False,full_solver_runs=0)
    (HERE/'exact_msolve_staged_review.log').write_text('\n'.join(logs))
    (HERE/'exact_msolve_staged_review_results.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))


if __name__ == '__main__':
    main()
