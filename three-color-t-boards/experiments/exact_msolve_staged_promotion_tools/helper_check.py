#!/usr/bin/env python3
"""Actual upstream hash functions + staged promotion: ownership/reuse tests."""

import hashlib
import importlib.util
import json
import os
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent
SOURCE = ROOT / "msolve-cc044551f8e202d00691990fd3fd0b1226a88ea2/src/neogb/hash.c"
spec = importlib.util.spec_from_file_location(
    "previous",
    ROOT.parent / "exact_msolve_rounded_promotion_tools/compatibility_check.py",
)
assert spec is not None and spec.loader is not None
previous = importlib.util.module_from_spec(spec)
spec.loader.exec_module(previous)
PRELUDE = (
    previous.PRELUDE
    + r"""
static unsigned fail_at=0, allocation_calls=0;
static void *checked_calloc(size_t n,size_t s) {
    if(fail_at && ++allocation_calls==fail_at)return NULL;
    return calloc(n,s);
}
static void *checked_realloc(void *p,size_t s) {
    if(fail_at && ++allocation_calls==fail_at)return NULL;
    return realloc(p,s);
}
#define calloc checked_calloc
#define realloc checked_realloc
"""
)

POSTLUDE = r"""
static void initialize(ht_t *h,hl_t n,int collide) {
    memset(h,0,sizeof(*h));h->evl=4;h->nv=3;h->esz=n;h->hsz=2*n;h->eld=1;
    h->ev=malloc(n*sizeof(exp_t*));h->ev[0]=calloc(n*4,sizeof(exp_t));
    for(hl_t i=1;i<n;i++)h->ev[i]=h->ev[0]+4*i;
    h->hd=calloc(n,sizeof(hd_t));h->hmap=calloc(2*n,sizeof(hi_t));
    h->rn=calloc(4,sizeof(val_t));h->dv=calloc(1,sizeof(len_t));h->dm=calloc(1,sizeof(sdm_t));
    for(int i=0;i<4;i++)h->rn[i]=collide?0:0x138fa417u+(val_t)i*0x1fa53897u;
}
static hi_t add(ht_t *h,unsigned code) {
    exp_t e[4]={0};for(int i=1;i<4;i++){e[i]=code%1024;code/=1024;e[0]+=e[i];}
    if(h->eld>=h->esz-1)enlarge_hash_table(h);
    return insert_in_hash_table(e,h);
}
static void verify(const ht_t *h) {
    assert(h->hsz>=2*h->esz&&!(h->hsz&(h->hsz-1)));
    for(hl_t i=0;i<h->esz;i++)assert(h->ev[i]==h->ev[0]+i*4);
    for(hi_t i=1;i<h->eld;i++) {
        hi_t got=0;assert(is_contained_in_hash_table(h->ev[i],h,h->hd[i].val,&got)==1&&got==i);
    }
}
static void dispose(ht_t *h,int shared) {
    free(h->ev[0]);free(h->ev);free(h->hd);free(h->hmap);
    if(shared){free(h->rn);free(h->dv);free(h->dm);}
}
static ht_t *secondary(ht_t *b,int large) {
    md_t md={0};md.init_hts=large?23:11;
    ht_t *s=initialize_secondary_hash_table(b,&md);
    for(unsigned i=1;i<=23;i++)assert(add(s,i)==i);
    return s;
}
static void mapping(ht_t *s,hi_t *hcm,unsigned rotation) {
    for(unsigned c=0;c<23;c++) {
        /* A reversed order forces nonmonotone source IDs for columns. */
        hi_t id=1+(22-c+rotation)%23;
        hcm[c]=id;s->hd[id].idx=c;
    }
}
static void compare_basis(const ht_t *a,const ht_t *b) {
    assert(a->eld==b->eld&&a->esz==b->esz&&a->hsz==b->hsz);
    for(hi_t i=1;i<a->eld;i++) {
        assert(memcmp(a->ev[i],b->ev[i],4*sizeof(exp_t))==0);
        assert(a->hd[i].val==b->hd[i].val);
    }
    verify(a);verify(b);
}
static void one(unsigned rotation,int collide,int large,int all_known) {
    ht_t b;initialize(&b,all_known?32:8,collide);
    for(unsigned i=1;i<=5;i++)assert(add(&b,i)==i);
    ht_t *s=secondary(&b,large),*legacy_s=copy_hash_table(s),*legacy_b=copy_hash_table(&b);
    hi_t hcm[23],legacy_hcm[23];mapping(s,hcm,rotation);mapping(legacy_s,legacy_hcm,rotation);
    hm_t row[OFFSET+23]={0};row[LENGTH]=0;
    const len_t ncl=3;
    for(unsigned c=ncl;c<23;c++) {
        if(hcm[c]<=5 || (!all_known && (hcm[c]%3==0 || hcm[c]==23)))
            row[OFFSET+row[LENGTH]++]=c;
    }
    hm_t *rows[1]={row};mat_t mat={ncl,23-ncl,23,1,rows};
    val_t *rn=s->rn;len_t *dv=s->dv;sdm_t *dm=s->dm;
    const hl_t oldcap=s->esz;
    switch_used_hcm_data_to_basis_hash_table(legacy_hcm,legacy_b,&mat,legacy_s,NULL,0);
    switch_used_hcm_data_to_basis_hash_table(hcm,&b,&mat,s,s,0);
    compare_basis(&b,legacy_b);
    for(unsigned j=0;j<row[LENGTH];j++)assert(hcm[row[OFFSET+j]]==legacy_hcm[row[OFFSET+j]]);
    assert(s->rn==rn&&s->dv==dv&&s->dm==dm&&s->nv==3&&s->evl==4);
    if(!all_known){assert(s->eld==1&&s->esz==(oldcap<2048?oldcap:2048));}
    else assert(s->eld==24&&s->esz==oldcap);
    clean_hash_table(s);assert(s->eld==1);
    unsigned count=large?2200:70;
    for(unsigned i=1;i<=count;i++)assert(add(s,i+500)==i);
    verify(s);
    ht_t *copy=copy_hash_table(s);verify(copy);dispose(copy,0);free(copy);
    reinitialize_hash_table(s,s->esz);assert(s->eld==1);add(s,777);verify(s);
    /* Use actual legacy reset/reinsert on the restored and regrown table. */
    add(s,888);add(s,999);
    hm_t r0[OFFSET+2]={0},r1[OFFSET+1]={0};r0[LENGTH]=2;r0[OFFSET]=1;r0[OFFSET+1]=3;r1[LENGTH]=1;r1[OFFSET]=3;
    hm_t *reset_rows[2]={r0,r1};uint8_t red[2]={0};bs_t bs={2,red,reset_rows};
    spair_t pair={2};ps_t ps={1,&pair};md_t md={0};
    reset_hash_table(s,&bs,&ps,&md);verify(s);assert(s->eld==4&&r0[OFFSET+1]==r1[OFFSET]);
    dispose(s,0);free(s);dispose(legacy_s,0);free(legacy_s);dispose(legacy_b,0);free(legacy_b);dispose(&b,1);
}
static void direct_zero_or_fault(unsigned failure) {
    ht_t b;initialize(&b,8,0);ht_t *s=secondary(&b,0);
    hi_t hcm[23];mapping(s,hcm,3);uint8_t used[23]={0};
    mat_t mat={0,23,23,0,NULL};
    unsigned missing=0;
    if(failure){for(unsigned c=0;c<23;c++)if(hcm[c]%2){used[c]=1;missing++;}}
    val_t *rn=s->rn;len_t *dv=s->dv;sdm_t *dm=s->dm;
    allocation_calls=0;fail_at=failure;
    exp_t *staged=stage_missing_symbolic_exponents(hcm,used,&mat,s,missing,0);
    if(failure){fprintf(stderr,"injected failure was not reached\n");exit(3);}
    assert(missing==0&&s->eld==1&&s->rn==rn&&s->dv==dv&&s->dm==dm);
    free(staged);clean_hash_table(s);assert(add(s,42)==1);verify(s);
    dispose(s,0);free(s);dispose(&b,1);
}
int main(int argc,char **argv) {
    if(argc==2){direct_zero_or_fault((unsigned)strtoul(argv[1],NULL,10));return 2;}
    for(unsigned r=0;r<23;r++)for(int c=0;c<2;c++)one(r,c,0,0);
    one(2,0,1,0);one(7,0,0,1);one(12,1,0,1);direct_zero_or_fault(0);
    puts("PASS actual_hash_promotions=49 rotations=23 collision_modes=2 staged_zero=1 subsequent_growth_clean_copy_reinitialize_reset=49");
}
"""


def main():
    text = SOURCE.read_text()
    markers = [
        ("ht_t *copy_hash_table(", "ht_t *initialize_secondary_hash_table("),
        ("ht_t *initialize_secondary_hash_table(", "void free_shared_hash_data("),
        (
            "static void enlarge_hash_table(",
            "static inline sdm_t generate_short_divmask(",
        ),
        (
            "static inline int32_t is_contained_in_hash_table(",
            "/* This function assumes that is_contained_in_hash_table()",
        ),
        (
            "static inline hi_t insert_in_hash_table(",
            "static inline void reinitialize_hash_table(",
        ),
        (
            "static inline void reinitialize_hash_table(",
            "static inline int prime_monomials(",
        ),
        (
            "static void reserve_basis_hash_table_for_promotion(",
            "static inline void insert_in_basis_hash_table_pivots(",
        ),
        (
            "static inline void reinsert_in_hash_table(",
            "void reset_hash_table_indices(",
        ),
        (
            "static void reset_hash_table(",
            "/* computes lcm of a and b from ht1 and inserts it in ht2 */",
        ),
    ]
    extracted = "\n".join(
        text[text.index(a) : text.index(b, text.index(a))] for a, b in markers
    )
    source, exe = ROOT / "helper_check.c", ROOT / "helper_check"
    source.write_text(
        PRELUDE
        + '\n#pragma GCC diagnostic push\n#pragma GCC diagnostic ignored "-Wtype-limits"\n#if defined(__clang__)\n#pragma clang diagnostic ignored "-Wtautological-constant-out-of-range-compare"\n#endif\n'
        + extracted
        + "\n#pragma GCC diagnostic pop\n"
        + POSTLUDE
    )
    command = [
        "cc",
        "-std=c23",
        "-O1",
        "-g",
        "-Wall",
        "-Wextra",
        "-Wpedantic",
        "-Werror",
        "-fsanitize=address,undefined",
        str(source),
        "-lm",
        "-o",
        str(exe),
    ]
    subprocess.run(command, check=True)
    good = subprocess.run(
        [str(exe)], capture_output=True, text=True, timeout=40, check=False
    )
    (ROOT / "helper_check.log").write_text(good.stdout + good.stderr)
    assert good.returncode == 0 and not good.stderr, good
    faults = []
    for i in range(1, 6):
        bad = subprocess.run(
            [str(exe), str(i)],
            capture_output=True,
            text=True,
            timeout=10,
            env=dict(os.environ, ASAN_OPTIONS="detect_leaks=0"),
            check=False,
        )
        assert (
            bad.returncode == 1
            and "Error: " in bad.stderr
            and "Sanitizer" not in bad.stderr
        ), bad
        faults.append(
            {
                "allocation": i,
                "returncode": bad.returncode,
                "diagnostic": bad.stderr.strip(),
            }
        )
    report = {
        "status": "PASS",
        "actual_hash_promotions": 49,
        "forced_hash_collisions": True,
        "zero_missing_direct_stage": True,
        "subsequent_operations": [
            "insert",
            "lookup",
            "legacy grow",
            "clean",
            "copy",
            "reinitialize",
            "reset/reinsert",
        ],
        "sanitizer": "ASan+UBSan; normal-run leak detection enabled; deliberate fatal-allocation tests disable leak reporting",
        "allocation_failures": faults,
        "compiler_command": command,
        "stubs": ["short divisibility mask returnszero", "timing returnszero"],
        "owner_hash_c_sha256": hashlib.sha256(text.encode()).hexdigest(),
        "extracted_source_sha256": hashlib.sha256(extracted.encode()).hexdigest(),
        "output": good.stdout.strip(),
    }
    (ROOT / "helper_check.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
