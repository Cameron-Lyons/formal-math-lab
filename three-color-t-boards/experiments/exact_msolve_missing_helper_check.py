#!/usr/bin/env python3
"""Independent extracted-helper tests for missing-only capacity reservation."""
import hashlib
import json
from pathlib import Path
import subprocess

import exact_msolve_sparse_helper_check as previous

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT/'experiments/exact_msolve_missing_promotion_tools/msolve-cc044551f8e202d00691990fd3fd0b1226a88ea2/src/neogb/hash.c'


def main():
    source = SOURCE.read_text()
    start = source.index('static inline void switch_used_hcm_data_to_basis_hash_table(')
    opening = source.index('{', start); end = opening+1; depth = 1
    while depth:
        depth += (source[end] == '{')-(source[end] == '}'); end += 1
    helper = source[start:end]
    prelude = previous.PRELUDE.replace('typedef uint32_t hi_t;', 'typedef uint32_t hi_t; typedef uint32_t val_t;')
    prelude = prelude.replace('hl_t eld,esz;', 'hl_t eld,esz; len_t evl; val_t rn[1];')
    prelude = prelude.replace('static int allocation_failure=0;',
        'static int allocation_failure=0, lookup_failure=0, invalid_found=0, suppress_insert=0;')
    prelude = prelude.replace('static hi_t insert_in_hash_table(const exp_t *exponent,ht_t *table) {',
        'static hi_t insert_in_hash_table(const exp_t *exponent,ht_t *table) {\n'
        '    if(suppress_insert)return 1;')
    prelude = prelude.replace('table->eld=1;table->esz=2;', 'table->eld=1;table->esz=2;table->evl=1;table->rn[0]=41;')
    lookup = r'''
static int32_t is_contained_in_hash_table(const exp_t *exponent,const ht_t *table,
                                        const val_t hash,hi_t *position) {
    assert(hash==table->rn[0]*exponent[0]);
    if(lookup_failure)return -1;
    if(invalid_found){*position=invalid_found==1?0:(hi_t)table->eld;return 1;}
    for(hi_t i=1;i<table->eld;i++)if(table->storage[i]==*exponent){*position=i;return 1;}
    *position=999; /* Deliberately not a usable stable entry ID. */
    return 0;
}
'''
    prelude = prelude.replace('#define calloc review_calloc', lookup+'\n#define calloc review_calloc')
    postlude = previous.POSTLUDE
    call = 'switch_used_hcm_data_to_basis_hash_table(mapping,&basis,&matrix,&symbolic,0);'
    postlude = postlude.replace('        '+call,
        '        hl_t expected_capacity=basis.esz;\n'
        '        while(expected_capacity<next)expected_capacity*=2;\n'
        '        '+call+'\n        assert(basis.esz==expected_capacity);', 1)
    postlude = postlude.replace('else if(!strcmp(argv[1],"mask-allocation"))allocation_failure=1;',
        'else if(!strcmp(argv[1],"mask-allocation"))allocation_failure=1;\n'
        '    else if(!strcmp(argv[1],"lookup-error"))lookup_failure=1;\n'
        '    else if(!strcmp(argv[1],"invalid-found-zero"))invalid_found=1;\n'
        '    else if(!strcmp(argv[1],"invalid-found-high"))invalid_found=2;\n'
        '    else if(!strcmp(argv[1],"mismatched-exponent-width"))symbolic.evl=2;\n'
        '    else if(!strcmp(argv[1],"insert-count-disagreement"))suppress_insert=1;\n'
        '    else if(!strcmp(argv[1],"aliased-tables")){\n'
        '        switch_used_hcm_data_to_basis_hash_table(mapping,&basis,&matrix,&basis,0);return 0;}\n'
        '    else if(!strcmp(argv[1],"all-reused")){\n'
        '        basis.storage[1]=2;basis.eld=2;basis.esz=2;\n'
        '        '+call+'\n'
        '        assert(basis.eld==2 && basis.esz==2 && mapping[1]==1);\n'
        '        puts("ALL_REUSED_NO_GROWTH");return 0;}')
    c_path = ROOT/'experiments/exact_msolve_missing_helper_check.c'
    binary = ROOT/'experiments/exact_msolve_missing_helper_check'
    c_path.write_text(prelude+helper+postlude)
    command = ['cc', '-std=c11', '-O1', '-g', '-Wall', '-Wextra', '-Werror',
               '-fsanitize=address,undefined', str(c_path), '-o', str(binary)]
    subprocess.run(command, check=True, capture_output=True, text=True)
    for arguments, expected in (([], 'VALID_CASES=5000'), (['all-reused'], 'ALL_REUSED_NO_GROWTH')):
        run = subprocess.run([str(binary)]+arguments, capture_output=True, text=True, check=True)
        assert run.stdout.strip() == expected and not run.stderr
    failures = []
    for case in ('low-column', 'high-column', 'zero-hash', 'high-hash', 'null-row',
                 'empty-row', 'overlong-row', 'null-rows', 'bad-dimensions',
                 'bad-pivot-bound', 'bad-hash-load', 'mask-allocation', 'lookup-error',
                 'invalid-found-zero', 'invalid-found-high', 'mismatched-exponent-width',
                 'insert-count-disagreement', 'aliased-tables'):
        run = subprocess.run([str(binary), case], capture_output=True, text=True)
        assert run.returncode == 1 and 'Error:' in run.stderr and not run.stdout, (case, run)
        assert 'AddressSanitizer' not in run.stderr and 'runtime error:' not in run.stderr
        failures.append(case)
    result = dict(status='PASS', exact_extracted_helper_sha256=hashlib.sha256(helper.encode()).hexdigest(),
                  owner_hash_c_sha256=hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
                  random_support_and_minimal_capacity_cases=5000,
                  all_reused_at_full_capacity_avoids_enlargement=True,
                  failure_cases=failures, compiler_command=command,
                  sanitizers=['address', 'undefined'], actual_hash_allocator_tested=False,
                  lookup_semantics='instrumented lookup verifies basis hash and stable existing IDs; actual lookup/rehash tested by owner')
    (ROOT/'experiments/exact_msolve_missing_helper_results.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
