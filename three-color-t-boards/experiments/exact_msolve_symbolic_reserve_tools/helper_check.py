#!/usr/bin/env python3
"""Actual upstream symbolic construction, staging and subsequent hash reuse."""
import hashlib,importlib.util,json,os,subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parent
SOURCE=ROOT/'msolve-cc044551f8e202d00691990fd3fd0b1226a88ea2/src/neogb/hash.c'
spec=importlib.util.spec_from_file_location('sixth',ROOT.parent/'exact_msolve_staged_promotion_tools/helper_check.py')
sixth=importlib.util.module_from_spec(spec);spec.loader.exec_module(sixth)
PRELUDE=sixth.PRELUDE.replace('int32_t init_hts;} md_t;', 'int32_t init_hts,fc,laopt,nthrds,trace_level,nf,in_final_reduction_step,nev,print_gb,info_level; ht_t *ht;} md_t;')
PRELUDE+='\n#define NO_TRACER 0\n#define COEFFS (OFFSET-3)\n#define PRELOOP (OFFSET-2)\n'
POSTLUDE=sixth.POSTLUDE[:sixth.POSTLUDE.index('int main(')]+r'''
static md_t ordinary(ht_t *s,int prime) {
    md_t md={0};md.fc=prime;md.laopt=2;md.nthrds=1;md.print_gb=1;md.ht=s;return md;
}
static void compare_rows(const hm_t *a,const hm_t *b) {
    assert(a[COEFFS]==b[COEFFS]&&a[PRELOOP]==b[PRELOOP]&&a[LENGTH]==b[LENGTH]);
    assert(memcmp(a+OFFSET,b+OFFSET,(size_t)a[LENGTH]*sizeof(hm_t))==0);
}
static void reuse_after_stage(ht_t *s) {
    assert(s->eld==1&&s->esz==2048);
    clean_hash_table(s);
    for(unsigned i=1;i<=2200;i++)assert(add(s,500+i)==i);
    verify(s);ht_t *copy=copy_hash_table(s);verify(copy);dispose(copy,0);free(copy);
    reinitialize_hash_table(s,s->esz);assert(s->eld==1);add(s,777);verify(s);
    add(s,888);add(s,999);
    hm_t r0[OFFSET+2]={0},r1[OFFSET+1]={0};r0[LENGTH]=2;r0[OFFSET]=1;r0[OFFSET+1]=3;r1[LENGTH]=1;r1[OFFSET]=3;
    hm_t *rs[2]={r0,r1};uint8_t red[2]={0};bs_t bs={2,red,rs};spair_t p={2};ps_t ps={1,&p};md_t md={0};
    reset_hash_table(s,&bs,&ps,&md);verify(s);assert(s->eld==4&&r0[OFFSET+1]==r1[OFFSET]);
}
static void row_case(int prime,int translated) {
    ht_t b;initialize(&b,32768,0);
    const len_t n=30000;
    hm_t *poly=calloc(OFFSET+n,sizeof(hm_t));poly[LENGTH]=n;poly[PRELOOP]=n%4;poly[COEFFS]=13;
    for(unsigned i=1;i<=n;i++)poly[OFFSET+i-1]=add(&b,i);
    md_t init={0};init.init_hts=23;ht_t *s=initialize_secondary_hash_table(&b,&init);
    assert(s->esz==131072);
    for(unsigned i=1;i<=120000;i++)assert(add(s,i)==i);
    ht_t *legacy=copy_hash_table(s);
    for(hi_t i=1;i<s->eld;i++)s->hd[i].idx=legacy->hd[i].idx=i%3;
    exp_t em[4]={(exp_t)translated,0,0,(exp_t)translated};
    md_t md=ordinary(s,prime);
    reserve_symbolic_row_capacity(s,poly,&md);
    assert(s->esz==196608&&s->hsz==524288&&s->eld==120001);
    for(hi_t i=1;i<s->eld;i++)assert(s->hd[i].idx==i%3);
    hm_t *row=multiplied_poly_to_matrix_row(s,&b,0,em,poly);
    hm_t *oldrow=multiplied_poly_to_matrix_row(legacy,&b,0,em,poly);
    assert(legacy->esz==262144&&s->esz==196608);
    assert(s->eld==legacy->eld&&s->eld==(translated?150001:120001));compare_rows(row,oldrow);
    for(hi_t i=1;i<s->eld;i++)assert(memcmp(s->ev[i],legacy->ev[i],4*sizeof(exp_t))==0);
    verify(s);verify(legacy);
    /* An actual no-multiplier constructor also preserves support IDs. */
    hm_t *plain=poly_to_matrix_row(s,&b,poly);compare_rows(plain,poly);free(plain);
    /* Reverse all hash→column mappings, then promote enough support to grow
     * the basis. This exercises compaction of the non-power source table. */
    len_t nc=(len_t)s->eld-1;hi_t *hcm=malloc(nc*sizeof(hi_t)),*oldhcm=malloc(nc*sizeof(hi_t));
    hm_t *out=calloc(OFFSET+nc,sizeof(hm_t));out[LENGTH]=nc;
    for(len_t c=0;c<nc;c++){hi_t id=nc-c;hcm[c]=oldhcm[c]=id;s->hd[id].idx=legacy->hd[id].idx=c;out[OFFSET+c]=c;}
    hm_t *rows[1]={out};mat_t mat={0,nc,nc,1,rows};ht_t *oldb=copy_hash_table(&b);
    val_t *rn=s->rn;len_t *dv=s->dv;sdm_t *dm=s->dm;
    switch_used_hcm_data_to_basis_hash_table(oldhcm,oldb,&mat,legacy,NULL,0);
    switch_used_hcm_data_to_basis_hash_table(hcm,&b,&mat,s,s,0);
    compare_basis(&b,oldb);assert(memcmp(hcm,oldhcm,nc*sizeof(hi_t))==0);
    assert(s->rn==rn&&s->dv==dv&&s->dm==dm);
    reuse_after_stage(s);
    free(poly);free(row);free(oldrow);free(out);free(hcm);free(oldhcm);
    dispose(s,0);free(s);dispose(legacy,0);free(legacy);dispose(oldb,0);free(oldb);dispose(&b,1);
}
static void gate_and_boundaries(void) {
    for(int which=0;which<8;which++) {
        ht_t s;initialize(&s,8,0);hm_t poly[OFFSET]={0};poly[LENGTH]=9;md_t md=ordinary(&s,2);
        switch(which){case 0:md.fc=5;break;case 1:md.laopt=1;break;case 2:md.nthrds=2;break;
          case 3:md.trace_level=1;break;case 4:md.nf=1;break;case 5:md.in_final_reduction_step=1;break;
          case 6:md.nev=1;break;case 7:md.print_gb=0;break;}
        reserve_symbolic_row_capacity(&s,poly,&md);assert(s.esz==8&&s.eld==1);dispose(&s,1);
    }
    hl_t requireds[]={8,9,65536,65537,131072,131073,196608};
    hl_t expected[]={8,16,65536,131072,131072,196608,196608};
    for(unsigned j=0;j<sizeof(requireds)/sizeof(requireds[0]);j++) {
        ht_t s;initialize(&s,8,0);hm_t poly[OFFSET]={0};poly[LENGTH]=(hm_t)(requireds[j]-2);md_t md=ordinary(&s,3);
        reserve_symbolic_row_capacity(&s,poly,&md);assert(s.esz==expected[j]);verify(&s);dispose(&s,1);
    }
}
static void symbolic_fault(unsigned failure) {
    ht_t s;initialize(&s,8,0);hm_t poly[OFFSET]={0};poly[LENGTH]=9;md_t md=ordinary(&s,3);
    allocation_calls=0;fail_at=failure;reserve_symbolic_row_capacity(&s,poly,&md);
    fputs("injected failure not reached\n",stderr);exit(3);
}
int main(int argc,char **argv) {
    if(argc==2){symbolic_fault((unsigned)strtoul(argv[1],NULL,10));return 2;}
    for(unsigned r=0;r<23;r++)for(int c=0;c<2;c++)one(r,c,0,0);
    one(2,0,1,0);one(7,0,0,1);one(12,1,0,1);direct_zero_or_fault(0);
    for(int p=2;p<=3;p++)for(int t=0;t<=1;t++)row_case(p,t);
    gate_and_boundaries();
    puts("PASS prior_promotions=49 actual_row_comparisons=4 nonpower_stage_and_reuse=4 fallback_gates=8 capacity_boundaries=7");
}
'''

def main():
    text=SOURCE.read_text()
    markers=[
        ('ht_t *copy_hash_table(', 'ht_t *initialize_secondary_hash_table('),
        ('ht_t *initialize_secondary_hash_table(', 'void free_shared_hash_data('),
        ('static void enlarge_hash_table(', 'static inline sdm_t generate_short_divmask('),
        ('static inline int32_t is_contained_in_hash_table(', '/* This function assumes that is_contained_in_hash_table()'),
        ('static inline hi_t insert_in_hash_table(', 'static inline void reinitialize_hash_table('),
        ('static inline void reinitialize_hash_table(', 'static inline int prime_monomials('),
        ('static void reserve_hash_table_checked(', 'static inline void insert_in_basis_hash_table_pivots('),
        ('static inline void insert_poly_in_hash_table(', 'static inline void reinsert_in_hash_table('),
        ('static inline void reinsert_in_hash_table(', 'void reset_hash_table_indices('),
        ('static void reset_hash_table(', '/* computes lcm of a and b from ht1 and inserts it in ht2 */')]
    extracted='\n'.join(text[text.index(a):text.index(b,text.index(a))] for a,b in markers)
    extracted+='\n'+text[text.index('static inline hm_t *poly_to_matrix_row('):]
    source,exe=ROOT/'helper_check.c',ROOT/'helper_check'
    source.write_text(PRELUDE+extracted+POSTLUDE)
    command=['cc','-std=c11','-O1','-g','-Wall','-Wextra','-Werror','-Wno-error=type-limits','-Wno-unused-parameter','-fsanitize=address,undefined',str(source),'-lm','-o',str(exe)]
    subprocess.run(command,check=True)
    good=subprocess.run([str(exe)],capture_output=True,text=True,timeout=60)
    (ROOT/'helper_check.log').write_text(good.stdout+good.stderr)
    assert good.returncode==0 and not good.stderr,good
    faults=[]
    for i in range(1,5):
        bad=subprocess.run([str(exe),str(i)],capture_output=True,text=True,timeout=10,env=dict(os.environ,ASAN_OPTIONS='detect_leaks=0'))
        assert bad.returncode==1 and 'Error: ' in bad.stderr and 'Sanitizer' not in bad.stderr,bad
        faults.append(dict(allocation=i,returncode=bad.returncode,diagnostic=bad.stderr.strip()))
    report=dict(status='PASS',prior_actual_hash_promotions=49,actual_row_construction_comparisons=4,nonpower_capacity=196608,legacy_capacity=262144,
                subsequent_operations=['nonpower staging','lookup','insert','clean','legacy grow','copy','reinitialize','reset/reinsert'],fallback_gates=8,capacity_boundaries=7,
                sanitizer='ASan+UBSan; normal leak checks; deliberate fatal allocations disable leak reporting',allocation_failures=faults,compiler_command=command,
                stubs=['short divisibility mask returns zero','timing returns zero'],owner_hash_c_sha256=hashlib.sha256(text.encode()).hexdigest(),
                extracted_source_sha256=hashlib.sha256(extracted.encode()).hexdigest(),output=good.stdout.strip())
    (ROOT/'helper_check.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
if __name__=='__main__':main()
