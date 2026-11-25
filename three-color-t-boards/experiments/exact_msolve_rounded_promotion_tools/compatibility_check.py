#!/usr/bin/env python3
"""Exercise actual legacy hash callers after non-power-of-two reservation."""
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parent
SOURCE = ROOT / 'msolve-cc044551f8e202d00691990fd3fd0b1226a88ea2/src/neogb/hash.c'
spec = importlib.util.spec_from_file_location('prior_harness', ROOT.parent/'exact_msolve_missing_promotion_tools/helper_check.py')
prior = importlib.util.module_from_spec(spec)
spec.loader.exec_module(prior)
PRELUDE = prior.PRELUDE.replace('hd_t *hd; hi_t *hmap; val_t *rn;} ht_t;',
    'hd_t *hd; hi_t *hmap; val_t *rn; len_t nv,ndv,bpv,*dv; int32_t mo; sdm_t *dm;} ht_t;')
PRELUDE += r'''
typedef len_t bl_t;
typedef struct {bl_t ld; uint8_t *red; hm_t **hm;} bs_t;
typedef struct {hi_t lcm;} spair_t;
typedef struct {len_t ld; spair_t *p;} ps_t;
typedef struct {double rht_ctime,rht_rtime; int32_t init_hts;} md_t;
static double cputime(void){return 0;}
static double realtime(void){return 0;}
'''

POSTLUDE = r'''
static void init(ht_t *h,hl_t n,int collisions) {
    memset(h,0,sizeof(*h));h->evl=4;h->nv=3;h->esz=n;h->eld=1;h->hsz=2*n;
    h->ev=malloc(n*sizeof(exp_t*));h->ev[0]=calloc(n*4,sizeof(exp_t));
    for(hl_t i=1;i<n;i++)h->ev[i]=h->ev[0]+4*i;
    h->hd=calloc(n,sizeof(hd_t));h->hmap=calloc(2*n,sizeof(hi_t));h->rn=calloc(4,sizeof(val_t));
    for(int i=0;i<4;i++)h->rn[i]=collisions?0:0x138fa417u+(val_t)i*0x1fa53897u;
}
static void clear(ht_t *h,int own_shared) {
    free(h->ev[0]);free(h->ev);free(h->hd);free(h->hmap);
    if(own_shared)free(h->rn);
}
static hi_t add(ht_t *h,unsigned code) {
    exp_t e[4]={0};for(int i=1;i<4;i++){e[i]=code%1024;code/=1024;e[0]+=e[i];}
    if(h->eld>=h->esz)enlarge_hash_table(h);
    return insert_in_hash_table(e,h);
}
static void verify(const ht_t *h) {
    assert(h->hsz>=2*h->esz&&!(h->hsz&(h->hsz-1)));
    for(hl_t i=0;i<h->esz;i++)assert(h->ev[i]==h->ev[0]+4*i);
    for(hi_t i=1;i<h->eld;i++) {
        hi_t found=0;assert(is_contained_in_hash_table(h->ev[i],h,h->hd[i].val,&found)==1);
        assert(found==i);
    }
}
int main(void) {
    for(int collisions=0;collisions<2;collisions++) {
        ht_t b;init(&b,131072,collisions);
        for(unsigned i=1;i<=120;i++)assert(add(&b,i)==i);
        exp_t before[120][4];for(unsigned i=1;i<=120;i++)memcpy(before[i-1],b.ev[i],sizeof(before[0]));
        reserve_basis_hash_table_for_promotion(&b,131072,0);
        assert(b.esz==196608&&b.hsz==524288&&b.eld==121);verify(&b);
        for(unsigned i=1;i<=120;i++)assert(memcmp(before[i-1],b.ev[i],sizeof(before[0]))==0);
        enlarge_hash_table(&b);
        assert(b.esz==393216&&b.hsz==1048576&&b.eld==121);verify(&b);
        for(unsigned i=1;i<=120;i++)assert(memcmp(before[i-1],b.ev[i],sizeof(before[0]))==0);
        ht_t *copy=copy_hash_table(&b);assert(copy->esz==b.esz&&copy->hsz==b.hsz);verify(copy);
        for(unsigned i=1;i<=120;i++)assert(memcmp(before[i-1],copy->ev[i],sizeof(before[0]))==0);
        clean_hash_table(copy);assert(copy->eld==1);assert(add(copy,999)==1);verify(copy);
        reinitialize_hash_table(copy,copy->esz);
        assert(copy->esz==786432&&copy->hsz==2097152&&copy->eld==1);
        assert(add(copy,666)==1);verify(copy);clear(copy,0);free(copy);
        md_t md={0};md.init_hts=8;
        ht_t *secondary=initialize_secondary_hash_table(&b,&md);
        assert(secondary->evl==4&&secondary->esz==4&&secondary->hsz==8);
        for(unsigned i=1;i<=16;i++){add(secondary,i);}
        verify(secondary);
        clear(secondary,0);free(secondary);
        hm_t row0[OFFSET+2]={0},row1[OFFSET+1]={0};
        row0[LENGTH]=2;row0[OFFSET]=5;row0[OFFSET+1]=90;
        row1[LENGTH]=1;row1[OFFSET]=90;
        hm_t *rows[2]={row0,row1};uint8_t red[2]={0};bs_t bs={2,red,rows};
        spair_t pair={120};ps_t pairs={1,&pair};
        reset_hash_table(&b,&bs,&pairs,&md);
        assert(b.esz==393216&&b.hsz==1048576&&b.eld==4);verify(&b);
        assert(memcmp(b.ev[row0[OFFSET]],before[4],sizeof(before[0]))==0);
        assert(memcmp(b.ev[row0[OFFSET+1]],before[89],sizeof(before[0]))==0);
        assert(row1[OFFSET]==row0[OFFSET+1]);
        assert(memcmp(b.ev[pair.lcm],before[119],sizeof(before[0]))==0);
        clear(&b,1);
        ht_t exact;init(&exact,65536,collisions);add(&exact,1);
        reserve_basis_hash_table_for_promotion(&exact,65536-exact.eld,0);
        assert(exact.esz==131072&&exact.hsz==262144);verify(&exact);clear(&exact,1);
    }
    puts("PASS collision_modes=2 nonpower_reserve legacy_growth copy clean reinitialize secondary reset exact_boundary_spare");
}
'''


def main():
    text = SOURCE.read_text()
    markers = [
        ('ht_t *copy_hash_table(', 'ht_t *initialize_secondary_hash_table('),
        ('ht_t *initialize_secondary_hash_table(', 'void free_shared_hash_data('),
        ('static void enlarge_hash_table(', 'static inline sdm_t generate_short_divmask('),
        ('static inline int32_t is_contained_in_hash_table(', '/* This function assumes that is_contained_in_hash_table()'),
        ('static inline hi_t insert_in_hash_table(', 'static inline void reinitialize_hash_table('),
        ('static inline void reinitialize_hash_table(', 'static inline int prime_monomials('),
        ('static void reserve_basis_hash_table_for_promotion(', '/* Used only by exact, non-tracing ordinary F4 export computations. */'),
        ('static inline void reinsert_in_hash_table(', 'void reset_hash_table_indices('),
        ('static void reset_hash_table(', '/* computes lcm of a and b from ht1 and inserts it in ht2 */'),
    ]
    extracted = '\n'.join(text[text.index(start):text.index(end, text.index(start))] for start, end in markers)
    source, executable = ROOT/'compatibility_check.c', ROOT/'compatibility_check'
    source.write_text(PRELUDE + '\n#pragma GCC diagnostic push\n#pragma GCC diagnostic ignored "-Wtype-limits"\n#if defined(__clang__)\n#pragma clang diagnostic ignored "-Wtautological-constant-out-of-range-compare"\n#endif\n' + extracted + '\n#pragma GCC diagnostic pop\n' + POSTLUDE)
    command = ['cc', '-std=c23', '-O1', '-g', '-Wall', '-Wextra', '-Wpedantic', '-Werror',
               '-fsanitize=address,undefined', str(source), '-lm', '-o', str(executable)]
    subprocess.run(command, check=True)
    run = subprocess.run([str(executable)], text=True, capture_output=True, timeout=30)
    (ROOT/'compatibility_check.log').write_text(run.stdout + run.stderr)
    assert run.returncode == 0 and not run.stderr, run
    report = dict(status='PASS', compiler_command=command,
                  actual_upstream_operations=['lookup', 'insertion', 'legacy enlargement', 'copy',
                                             'clean', 'reinitialize', 'secondary initialization', 'reset/reinsert'],
                  candidate_operation='promotion-only rounded reserve',
                  allocation_failures_tested=False,
                  stubs=['short divisibility mask returns zero', 'CPU and wall timing return zero'],
                  non_power_of_two_capacity=196608, subsequent_legacy_capacity=393216,
                  tested_exact_boundary_spare=True, tested_forced_hash_collisions=True,
                  extracted_source_sha256=hashlib.sha256(extracted.encode()).hexdigest(),
                  owner_hash_c_sha256=hashlib.sha256(text.encode()).hexdigest(), output=run.stdout.strip())
    (ROOT/'compatibility_check.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
