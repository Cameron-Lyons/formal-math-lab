#!/usr/bin/env python3
"""ASan/UBSan checks using the actual lookup, insertion and rehash routines."""
import hashlib
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parent
SOURCE = ROOT / 'msolve-cc044551f8e202d00691990fd3fd0b1226a88ea2/src/neogb/hash.c'

PRELUDE = r'''
#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
typedef uint32_t val_t, hi_t, hm_t, len_t, sdm_t;
typedef uint64_t hl_t;
typedef uint16_t exp_t;
typedef int32_t deg_t;
typedef struct {val_t val; sdm_t sdm; uint32_t idx; deg_t deg;} hd_t;
typedef struct {hl_t esz,eld,hsz; len_t evl,ebl; exp_t **ev;
                hd_t *hd; hi_t *hmap; val_t *rn;} ht_t;
typedef struct {len_t ncl,ncr,nc,np; hm_t **tr;} mat_t;
#define OFFSET 6
#define LENGTH 5
#define ERRSTREAM stderr
#define VERBSTREAM stdout
static sdm_t generate_short_divmask(const exp_t *a,const ht_t *ht) {
    (void)a;(void)ht;return 0;
}
'''

POSTLUDE = r'''
static uint32_t rng=0x8391beef;
static uint32_t next(void){rng=1664525*rng+1013904223;return rng;}
static void init(ht_t *ht,hl_t size,int collisions) {
    memset(ht,0,sizeof(*ht));ht->evl=4;ht->esz=size;ht->eld=1;ht->hsz=2*size;
    ht->ev=malloc(size*sizeof(exp_t*));ht->ev[0]=calloc(size*4,sizeof(exp_t));
    for(hl_t i=1;i<size;i++)ht->ev[i]=ht->ev[0]+4*i;
    ht->hd=calloc(size,sizeof(hd_t));ht->hmap=calloc(2*size,sizeof(hi_t));
    ht->rn=calloc(4,sizeof(val_t));
    for(int i=0;i<4;i++)ht->rn[i]=collisions?0:0x91abcdefu+(val_t)i*0x1829384u;
}
static void clear(ht_t *ht) {
    free(ht->ev[0]);free(ht->ev);free(ht->hd);free(ht->hmap);free(ht->rn);
}
static hi_t add(ht_t *ht,unsigned code) {
    exp_t e[4]={0};
    for(int i=1;i<4;i++){e[i]=(exp_t)(code%7);code/=7;e[0]+=e[i];}
    if(ht->eld==ht->esz)enlarge_hash_table(ht);
    return insert_in_hash_table(e,ht);
}
static void clone(ht_t *dst,const ht_t *src) {
    init(dst,src->esz,0);memcpy(dst->rn,src->rn,4*sizeof(val_t));
    for(hi_t i=1;i<src->eld;i++)assert(insert_in_hash_table(src->ev[i],dst)==i);
}
int main(void) {
    unsigned growth_cases=0,overlap_cases=0,capacity_savings=0;
    for(unsigned trial=0;trial<2000;trial++) {
        ht_t symbols,basis,reference;init(&symbols,256,trial%2);init(&basis,8,trial%2);
        const len_t count=trial==0?6:trial==1?9:10+next()%90;
        for(unsigned i=0;i<count;i++)assert(add(&symbols,i+1)==i+1);
        const len_t existing=trial==0?6:trial==1?6:next()%(count+1);
        for(unsigned i=0;i<existing;i++)add(&basis,i+1);
        const hl_t before_load=basis.eld,before_capacity=basis.esz;
        clone(&reference,&basis);
        hi_t map[128],expected[128],original[128];uint8_t used[128]={0};
        for(unsigned i=0;i<count;i++)map[i]=i+1;
        for(unsigned i=count-1;i>0;i--){unsigned j=next()%(i+1);hi_t t=map[i];map[i]=map[j];map[j]=t;}
        memcpy(original,map,sizeof(map));memcpy(expected,map,sizeof(map));
        hm_t rows[4][OFFSET+128]={0},saved[4][OFFSET+128];hm_t *ptrs[4];
        mat_t mat={0,count,count,4,ptrs};
        for(unsigned r=0;r<4;r++) {
            ptrs[r]=rows[r];rows[r][LENGTH]=trial<2?count:1+next()%count;
            for(unsigned j=0;j<rows[r][LENGTH];j++) {
                hi_t col=trial<2?j:next()%count;rows[r][OFFSET+j]=col;used[col]=1;
            }
        }
        memcpy(saved,rows,sizeof(rows));unsigned referenced=0;
        for(unsigned c=0;c<count;c++)referenced+=used[c];
        while(reference.esz-reference.eld<referenced)enlarge_hash_table(&reference);
        for(unsigned c=0;c<count;c++)if(used[c])expected[c]=insert_in_hash_table(symbols.ev[map[c]],&reference);
        switch_used_hcm_data_to_basis_hash_table(map,&basis,&mat,&symbols,0);
        assert(basis.eld==reference.eld);
        assert(basis.esz<=reference.esz);
        assert(memcmp(rows,saved,sizeof(rows))==0);
        for(unsigned c=0;c<count;c++)assert(map[c]==expected[c]);
        for(hi_t i=1;i<basis.eld;i++) {
            assert(memcmp(basis.ev[i],reference.ev[i],4*sizeof(exp_t))==0);
            assert(memcmp(basis.hd+i,reference.hd+i,sizeof(hd_t))==0);
        }
        if(basis.esz>before_capacity)growth_cases++;
        if(basis.eld-before_load<referenced)overlap_cases++;
        if(basis.esz<reference.esz)capacity_savings++;
        if(trial==0){assert(basis.esz==8);assert(reference.esz==16);assert(basis.eld==7);}
        if(trial==1){assert(basis.esz==16);assert(basis.eld==10);}
        clear(&symbols);clear(&basis);clear(&reference);
    }
    assert(growth_cases>0&&overlap_cases>0&&capacity_savings>0);
    printf("PASS cases=2000 growth=%u overlap=%u smaller_capacity=%u\n",growth_cases,overlap_cases,capacity_savings);
}
'''


def main():
    text = SOURCE.read_text()
    markers = [
        ('static void enlarge_hash_table(', 'static inline sdm_t generate_short_divmask('),
        ('static inline int32_t is_contained_in_hash_table(', '/* This function assumes that is_contained_in_hash_table()'),
        ('static inline hi_t insert_in_hash_table(', 'static inline void reinitialize_hash_table('),
        ('static inline void switch_used_hcm_data_to_basis_hash_table(', 'static inline void insert_in_basis_hash_table_pivots('),
    ]
    extracted = '\n'.join(text[text.index(start):text.index(end, text.index(start))]
                          for start, end in markers)
    source = ROOT / 'helper_check.c'
    binary = ROOT / 'helper_check'
    source.write_text(PRELUDE + extracted + POSTLUDE)
    command = ['cc', '-std=c11', '-O1', '-g', '-Wall', '-Wextra', '-Werror',
               '-fsanitize=address,undefined', str(source), '-lm', '-o', str(binary)]
    subprocess.run(command, check=True)
    result = subprocess.run([str(binary)], capture_output=True, text=True, timeout=30)
    (ROOT / 'helper_check.log').write_text(result.stdout + result.stderr)
    assert result.returncode == 0 and not result.stderr, result
    report = dict(status='PASS', randomized_cases=2000, command=command,
                  actual_upstream_functions=['is_contained_in_hash_table', 'insert_in_hash_table', 'enlarge_hash_table'],
                  stubbed_function='generate_short_divmask returns zero; divisibility is not tested',
                  allocation_failure_tested=False, forced_hash_collisions=True,
                  exact_extracted_functions_sha256=hashlib.sha256(extracted.encode()).hexdigest(),
                  owner_hash_c_sha256=hashlib.sha256(text.encode()).hexdigest(),
                  output=result.stdout.strip())
    (ROOT / 'helper_check.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
