#!/usr/bin/env python3
"""Compile the exact candidate helper against a minimal instrumented hash table."""
import hashlib
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]
TOOLS = ROOT/'experiments/exact_msolve_sparse_promotion_tools'
SOURCE = TOOLS/'msolve-cc044551f8e202d00691990fd3fd0b1226a88ea2/src/neogb/hash.c'

PRELUDE = r'''
#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef uint32_t hi_t;
typedef uint32_t hm_t;
typedef uint32_t len_t;
typedef uint64_t hl_t;
typedef uint16_t exp_t;
#define OFFSET 6
#define LENGTH 5
#define ERRSTREAM stderr
#define VERBSTREAM stdout
#define CAP 2048
typedef struct {hl_t eld,esz; exp_t storage[CAP]; exp_t *ev[CAP];} ht_t;
typedef struct {len_t ncl,ncr,nc,np; hm_t **tr;} mat_t;
static int allocation_failure=0;
static void *review_calloc(size_t n,size_t size) {
    return allocation_failure ? NULL : calloc(n,size);
}
static void enlarge_hash_table(ht_t *table) {
    assert(table->esz>0 && table->esz*2<CAP);
    table->esz*=2;
}
static hi_t insert_in_hash_table(const exp_t *exponent,ht_t *table) {
    for(hi_t i=1;i<table->eld;i++) if(table->storage[i]==*exponent) return i;
    assert(table->eld<table->esz);
    hi_t index=(hi_t)table->eld++;
    table->storage[index]=*exponent;
    return index;
}
static void init_table(ht_t *table) {
    memset(table,0,sizeof(*table));
    table->eld=1;table->esz=2;
    for(int i=0;i<CAP;i++)table->ev[i]=table->storage+i;
}
#define calloc review_calloc
'''

POSTLUDE = r'''
#undef calloc
static uint32_t state=0x51A7F00D;
static uint32_t next_random(void) {state=1664525*state+1013904223;return state;}
static void valid_cases(void) {
    for(int trial=0;trial<5000;trial++) {
        ht_t symbolic,basis;init_table(&symbolic);init_table(&basis);
        mat_t matrix={0};matrix.ncl=next_random()%7;matrix.ncr=1+next_random()%120;
        matrix.nc=matrix.ncl+matrix.ncr;matrix.np=1+next_random()%16;
        symbolic.eld=matrix.nc+1;symbolic.esz=256;
        for(hi_t i=1;i<symbolic.eld;i++)symbolic.storage[i]=(exp_t)(7*i+3);
        const len_t initial=next_random()%12;
        for(hi_t i=1;i<=initial;i++)basis.storage[i]=(exp_t)(7*i+3);
        basis.eld=initial+1;while(basis.esz<=basis.eld)basis.esz*=2;
        hi_t mapping[256],original[256],expected[256];
        uint8_t used[256]={0};
        for(hi_t i=0;i<matrix.nc;i++)mapping[i]=i+1;
        for(hi_t i=matrix.nc-1;i>0;i--){hi_t j=next_random()%(i+1),t=mapping[i];mapping[i]=mapping[j];mapping[j]=t;}
        memcpy(original,mapping,sizeof(mapping));memcpy(expected,mapping,sizeof(mapping));
        hm_t rows[16][OFFSET+120], saved[16][OFFSET+120];hm_t *pointers[16];
        matrix.tr=pointers;
        for(len_t i=0;i<matrix.np;i++) {
            pointers[i]=rows[i];memset(rows[i],0,sizeof(rows[i]));
            rows[i][LENGTH]=1+next_random()%matrix.ncr;
            for(len_t j=0;j<rows[i][LENGTH];j++) {
                const hi_t column=matrix.ncl+next_random()%matrix.ncr;
                rows[i][OFFSET+j]=column;used[column]=1;
            }
        }
        memcpy(saved,rows,sizeof(rows));
        exp_t expected_values[CAP];memcpy(expected_values,basis.storage,sizeof(expected_values));
        hi_t next=(hi_t)basis.eld;
        for(hi_t column=matrix.ncl;column<matrix.nc;column++)if(used[column]) {
            exp_t value=symbolic.storage[original[column]];hi_t index=1;
            for(;index<next;index++)if(expected_values[index]==value)break;
            if(index==next)expected_values[next++]=value;
            expected[column]=index;
        }
        switch_used_hcm_data_to_basis_hash_table(mapping,&basis,&matrix,&symbolic,0);
        assert(basis.eld==next);
        assert(memcmp(rows,saved,sizeof(rows))==0);
        for(hi_t i=1;i<basis.eld;i++)assert(basis.storage[i]==expected_values[i]);
        for(hi_t column=0;column<matrix.nc;column++) {
            assert(mapping[column]==expected[column]);
            if(used[column])assert(basis.storage[mapping[column]]==symbolic.storage[original[column]]);
            else assert(mapping[column]==original[column]);
        }
    }
    puts("VALID_CASES=5000");
}
int main(int argc,char **argv) {
    if(argc==1){valid_cases();return 0;}
    ht_t symbolic,basis;init_table(&symbolic);init_table(&basis);
    symbolic.eld=5;symbolic.esz=8;
    for(hi_t i=1;i<5;i++)symbolic.storage[i]=(exp_t)i;
    hi_t mapping[]={1,2,3,4};
    hm_t row[OFFSET+4]={0};row[LENGTH]=1;row[OFFSET]=1;
    hm_t *rows[]={row};mat_t matrix={1,3,4,1,rows};
    if(!strcmp(argv[1],"low-column"))row[OFFSET]=0;
    else if(!strcmp(argv[1],"high-column"))row[OFFSET]=4;
    else if(!strcmp(argv[1],"zero-hash"))mapping[1]=0;
    else if(!strcmp(argv[1],"high-hash"))mapping[1]=5;
    else if(!strcmp(argv[1],"null-row"))rows[0]=NULL;
    else if(!strcmp(argv[1],"empty-row"))row[LENGTH]=0;
    else if(!strcmp(argv[1],"overlong-row"))row[LENGTH]=4;
    else if(!strcmp(argv[1],"null-rows"))matrix.tr=NULL;
    else if(!strcmp(argv[1],"bad-dimensions"))matrix.ncr=2;
    else if(!strcmp(argv[1],"bad-pivot-bound"))matrix.ncl=5;
    else if(!strcmp(argv[1],"bad-hash-load"))basis.eld=3;
    else if(!strcmp(argv[1],"mask-allocation"))allocation_failure=1;
    else return 3;
    switch_used_hcm_data_to_basis_hash_table(mapping,&basis,&matrix,&symbolic,0);
    puts("UNEXPECTED_SUCCESS");return 0;
}
'''


def main():
    text = SOURCE.read_text()
    start = text.index('static inline void switch_used_hcm_data_to_basis_hash_table(')
    body = text.index('{', start)
    depth = 1; end = body+1
    while depth:
        depth += (text[end] == '{')-(text[end] == '}')
        end += 1
    helper = text[start:end]
    c_path = ROOT/'experiments/exact_msolve_sparse_helper_check.c'
    executable = ROOT/'experiments/exact_msolve_sparse_helper_check'
    c_path.write_text(PRELUDE+helper+POSTLUDE)
    command = ['cc', '-std=c23', '-O1', '-g', '-Wall', '-Wextra', '-Wpedantic', '-Werror',
               '-fsanitize=address,undefined', str(c_path), '-o', str(executable)]
    subprocess.run(command, check=True, capture_output=True, text=True)
    valid = subprocess.run([str(executable)], capture_output=True, text=True, check=True)
    assert valid.stdout.strip() == 'VALID_CASES=5000' and not valid.stderr
    failures = []
    for case in ('low-column', 'high-column', 'zero-hash', 'high-hash', 'null-row',
                 'empty-row', 'overlong-row', 'null-rows', 'bad-dimensions',
                 'bad-pivot-bound', 'bad-hash-load', 'mask-allocation'):
        run = subprocess.run([str(executable), case], capture_output=True, text=True)
        assert run.returncode == 1 and 'Error:' in run.stderr and not run.stdout, (case, run)
        assert 'AddressSanitizer' not in run.stderr and 'runtime error:' not in run.stderr
        failures.append(case)
    result = dict(status='PASS', exact_extracted_helper_sha256=hashlib.sha256(helper.encode()).hexdigest(),
                  owner_hash_c_sha256=hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
                  random_support_cases=5000, failure_cases=failures,
                  compiler_command=command, sanitizers=['address', 'undefined'],
                  actual_hash_allocation_tested=False,
                  note='Instrumented hash stub checks support/mapping semantics; upstream enlarge allocator is outside this harness.')
    (ROOT/'experiments/exact_msolve_sparse_helper_results.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
