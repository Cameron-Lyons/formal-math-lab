#!/usr/bin/env python3
"""Independent arithmetic/allocation checks of the exact rounded reserve helper."""
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT/'experiments/exact_msolve_rounded_promotion_tools/msolve-cc044551f8e202d00691990fd3fd0b1226a88ea2/src/neogb/hash.c'

PRELUDE = r'''
#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef uint64_t hl_t;
typedef uint32_t hi_t;
typedef uint32_t len_t;
typedef uint16_t exp_t;
typedef struct {uint32_t val,deg,sdm,idx;} hd_t;
typedef struct {hl_t eld,esz,hsz;len_t evl;exp_t **ev;hd_t *hd;hi_t *hmap;} ht_t;
#define ERRSTREAM stderr
#define VERBSTREAM stdout
#ifdef REVIEW_SIZE32
#undef SIZE_MAX
#define SIZE_MAX UINT32_MAX
#endif
static ht_t *current=NULL;
static int calls=0,fail_call=0;
static void cleanup(void) {
    if(current){free(current->ev[0]);free(current->ev);free(current->hd);free(current->hmap);free(current);current=NULL;}
}
static void finish(void) {printf("AUDIT_ALLOCATION_CALLS=%d\n",calls);cleanup();}
static void *checked_test_realloc(void *old,size_t size) {
    calls++;
    if(calls==fail_call)return NULL;
    return realloc(old,size);
}
#define realloc checked_test_realloc
'''

POSTLUDE = r'''
#undef realloc
static ht_t *initial(hl_t esz,hl_t eld,hl_t hsz,len_t evl,int real) {
    ht_t *table=calloc(1,sizeof(*table));assert(table);
    table->eld=eld;table->esz=esz;table->hsz=hsz;table->evl=evl;
    size_t allocated=real?(size_t)esz:1;
    size_t width=real?(size_t)evl:1;
    table->ev=malloc(allocated*sizeof(*table->ev));assert(table->ev);
    exp_t *block=malloc(allocated*width*sizeof(*block));assert(block);
    for(size_t i=0;i<allocated;i++)table->ev[i]=block+i*width;
    table->hd=calloc(allocated,sizeof(*table->hd));assert(table->hd);
    table->hmap=calloc(real?(size_t)hsz:1,sizeof(*table->hmap));assert(table->hmap);
    if(real)for(hi_t i=1;i<eld;i++){
        table->hd[i]=(hd_t){0,i+7,i+11,i+13}; /* All hashes intentionally collide. */
        for(len_t j=0;j<evl;j++)table->ev[i][j]=(exp_t)(10*i+j);
        hi_t bucket=0;
        for(hl_t step=0;step<hsz;step++){
            bucket=(hi_t)((bucket+step)&(hsz-1));
            if(table->hmap[bucket]==0){table->hmap[bucket]=i;break;}
        }
    }
    current=table;return table;
}
static void verify(ht_t *table,hl_t old_eld) {
    assert(table->eld==old_eld && table->esz>old_eld && table->hsz>=2*table->esz);
    assert((table->hsz&(table->hsz-1))==0);
    for(hl_t i=0;i<table->esz;i++)assert(table->ev[i]==table->ev[0]+i*table->evl);
    for(hi_t i=1;i<old_eld;i++){
        assert(table->hd[i].val==0 && table->hd[i].deg==i+7 && table->hd[i].sdm==i+11 && table->hd[i].idx==i+13);
        for(len_t j=0;j<table->evl;j++)assert(table->ev[i][j]==10*i+j);
        hi_t bucket=0;int found=0;
        for(hl_t step=0;step<table->hsz;step++){
            bucket=(hi_t)((bucket+step)&(table->hsz-1));
            if(table->hmap[bucket]==i){found=1;break;}
            assert(table->hmap[bucket]!=0);
        }
        assert(found);
    }
    for(hl_t i=old_eld;i<table->esz;i++)assert(table->hd[i].val==0 && table->hd[i].deg==0 && table->hd[i].sdm==0 && table->hd[i].idx==0);
    size_t entries=0;for(hl_t i=0;i<table->hsz;i++)entries+=table->hmap[i]!=0;
    assert(entries==old_eld-1);
}
int main(int argc,char **argv) {
    atexit(finish);
    if(argc==7 && !strcmp(argv[1],"plan")){
        hl_t esz=strtoull(argv[2],NULL,10),eld=strtoull(argv[3],NULL,10);
        hl_t extra=strtoull(argv[4],NULL,10),hsz=strtoull(argv[6],NULL,10);
        len_t evl=(len_t)strtoul(argv[5],NULL,10);
        ht_t *table=initial(esz,eld,hsz,evl,0);fail_call=1;
        reserve_basis_hash_table_for_promotion(table,extra,2);
        puts("PLAN_NO_GROWTH");return 0;
    }
    if(argc>=2 && !strcmp(argv[1],"fail")){
        ht_t *table=initial(8,6,16,3,1);fail_call=atoi(argv[2]);
        reserve_basis_hash_table_for_promotion(table,5,0);
        puts("UNEXPECTED_SUCCESS");return 0;
    }
    if(argc==2 && !strcmp(argv[1],"success")){
        const hl_t specs[][5]={{8,6,16,5,65536},{131072,12,262144,131060,196608},{131072,12,1048576,131060,196608}};
        for(size_t i=0;i<3;i++){
            ht_t *table=initial(specs[i][0],specs[i][1],specs[i][2],3,1);
            calls=0;reserve_basis_hash_table_for_promotion(table,specs[i][3],0);
            assert(table->esz==specs[i][4]);assert(calls==(i==2?3:4));
            verify(table,specs[i][1]);cleanup();
        }
        puts("REAL_REALLOC_COLLISION_CASES=3");return 0;
    }
    return 3;
}
'''


def main():
    source = SOURCE.read_text()
    start = source.index('static void reserve_basis_hash_table_for_promotion(')
    opening = source.index('{', start); depth = 1; end = opening+1
    while depth:
        depth += (source[end] == '{')-(source[end] == '}'); end += 1
    helper = source[start:end]
    c_path = ROOT/'experiments/exact_msolve_rounded_capacity_check.c'
    c_path.write_text(PRELUDE+helper+POSTLUDE)
    binaries = {}
    for tag in ('native', 'size32'):
        binary = ROOT/('experiments/exact_msolve_rounded_capacity_check_'+tag)
        command = ['cc', '-std=c11', '-O1', '-g', '-Wall', '-Wextra', '-Wno-type-limits',
                   '-fsanitize=address,undefined', str(c_path), '-o', str(binary)]
        if tag == 'size32':
            command.append('-DREVIEW_SIZE32')
        subprocess.run(command, check=True, capture_output=True, text=True)
        binaries[tag] = binary
    def run(tag, arguments):
        result = subprocess.run([str(binaries[tag])]+list(map(str, arguments)), capture_output=True, text=True)
        assert 'AddressSanitizer' not in result.stderr and 'runtime error:' not in result.stderr, result
        return result
    succeeded = run('native', ['success'])
    assert succeeded.returncode == 0 and 'REAL_REALLOC_COLLISION_CASES=3' in succeeded.stdout
    failures = []
    for index in range(1, 5):
        failure = run('native', ['fail', index])
        assert failure.returncode == 1 and f'AUDIT_ALLOCATION_CALLS={index}' in failure.stdout
        assert 'Error: cannot allocate promotion' in failure.stderr and 'UNEXPECTED_SUCCESS' not in failure.stdout
        failures.append(index)
    plans = []
    valid = [(8, 6, 1, 3, 16), (65536, 65535, 0, 3, 131072),
             (65536, 65535, 1, 3, 131072), (131072, 12, 131060, 101, 262144),
             (131072, 12, 131060, 101, 1048576),
             (2097152, 2080795, 55218, 101, 4194304),
             (1 << 29, 1, (1 << 30)-2, 1, 1 << 30)]
    for esz, eld, extra, width, buckets in valid:
        result = run('native', ['plan', esz, eld, extra, width, buckets])
        required = eld+extra+1
        if required <= esz:
            assert result.returncode == 0 and 'PLAN_NO_GROWTH' in result.stdout
            assert 'AUDIT_ALLOCATION_CALLS=0' in result.stdout
            target, target_buckets = esz, buckets
        else:
            target = (required+65535)//65536*65536
            target_buckets = buckets
            while target_buckets < 2*target:
                target_buckets *= 2
            assert result.returncode == 1 and 'AUDIT_ALLOCATION_CALLS=1' in result.stdout
            match = re.search(r'required_with_spare=(\d+) exponent_old=(\d+) exponent_new=(\d+) buckets_old=(\d+) buckets_new=(\d+)', result.stdout)
            assert match and tuple(map(int, match.groups())) == (required, esz, target, buckets, target_buckets)
        plans.append(dict(old_capacity=esz, load=eld, missing=extra,
                          expected_capacity=target, expected_buckets=target_buckets))
    invalid = [
        ('zero-capacity', 0, 1, 0, 3, 2), ('zero-load', 8, 0, 0, 3, 16),
        ('load-over-capacity', 8, 9, 0, 3, 16), ('zero-width', 8, 1, 1, 0, 16),
        ('non-power-buckets', 8, 1, 1, 3, 17), ('insufficient-buckets', 8, 1, 1, 3, 8),
        ('legacy-bucket-limit', 8, 1, 1, 3, 1 << 32),
        ('entry-limit', 8, 1, 1 << 30, 3, 16),
        ('spare-at-max', 1 << 30, (1 << 30)-1, 1, 3, 1 << 31),
        ('huge-additional', 8, 1, (1 << 64)-1, 3, 16)]
    rejected = []
    for name, *arguments in invalid:
        result = run('native', ['plan']+arguments)
        assert result.returncode == 1 and 'Error:' in result.stderr and 'AUDIT_ALLOCATION_CALLS=0' in result.stdout
        rejected.append(name)
    for name, arguments in (
            ('simulated-size32-metadata-overflow', [8, 1, 1 << 28, 3, 16]),
            ('simulated-size32-vector-overflow', [8, 1, 8, (1 << 32)-1, 16]),
            ('simulated-size32-bucket-overflow', [1 << 28, 1, (1 << 29)-2, 1, 1 << 29])):
        result = run('size32', ['plan']+arguments)
        assert result.returncode == 1 and 'allocation size overflow' in result.stderr
        assert 'AUDIT_ALLOCATION_CALLS=0' in result.stdout
        rejected.append(name)
    report = dict(status='PASS', helper_sha256=hashlib.sha256(helper.encode()).hexdigest(),
                  owner_hash_c_sha256=hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
                  real_realloc_and_collision_cases=3, checked_allocation_failure_stages=failures,
                  independently_checked_capacity_plans=plans, rejected_arithmetic_layout_cases=rejected,
                  sanitizers=['address', 'undefined'], no_full_solver_run=True,
                  size32_note='SIZE_MAX was restricted in a native64 harness to exercise32-bit allocation guards; not a32-bit executable.')
    (ROOT/'experiments/exact_msolve_rounded_capacity_results.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
