/* Independent boundary harness around the actual candidate kernel. */
#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef uint32_t len_t;
typedef uint32_t hm_t;
typedef uint8_t cf8_t;
#define OFFSET 6
#define LENGTH 5
#define PRELOOP 4
#define COEFFS 3
#define MULT 2
#define BINDEX 1
#define UNROLL 4
#define NO_TRACER 0
#define ERRSTREAM stderr
#define VERBSTREAM stdout
typedef struct { cf8_t **cf_8; len_t ld; } bs_t;
typedef struct {
    hm_t **rr, **tr;
    cf8_t **cf_8;
    len_t nc, ncl, ncr, nru, nrl, np, nr, sz;
} mat_t;
typedef struct {
    int fc, laopt, nthrds, trace_level, nf, in_final_reduction_step, nev, print_gb;
    int info_level;
    len_t np;
} md_t;

static hm_t **old_rows;
static size_t old_count, old_remaining;
static void *lower_container;
static size_t allocations, fail_allocation;
static int lower_container_freed;

static void *review_calloc(size_t count, size_t size)
{
    ++allocations;
    if (fail_allocation == allocations) return NULL;
    if (lower_container_freed) assert(old_remaining == 0);
    return calloc(count, size);
}

static void review_free(void *pointer)
{
    if (pointer != NULL) {
        for (size_t i = 0; i < old_count; ++i) {
            if (pointer == old_rows[i]) {
                old_rows[i] = NULL;
                assert(old_remaining > 0);
                --old_remaining;
            }
        }
        if (pointer == lower_container) {
            assert(old_remaining == 0);
            lower_container_freed = 1;
        }
    }
    free(pointer);
}

#define calloc review_calloc
#define free review_free
#include "exact_msolve_f2_bitset_tools/msolve-cc044551f8e202d00691990fd3fd0b1226a88ea2/src/neogb/la_ff_2_bitset.c"
#undef calloc
#undef free

static unsigned next_integer(void)
{
    unsigned value;
    assert(scanf("%u", &value) == 1);
    return value;
}

static hm_t *read_row(bs_t *basis, len_t slot, len_t original)
{
    const len_t length = next_integer();
    hm_t *row = calloc((size_t)length+OFFSET, sizeof(*row));
    assert(row != NULL);
    row[LENGTH] = length;
    row[PRELOOP] = length % UNROLL;
    row[COEFFS] = slot;
    row[BINDEX] = original + 100003;
    row[MULT] = original * 17 + 70001;
    basis->cf_8[slot] = calloc(length ? length : 1, sizeof(cf8_t));
    assert(basis->cf_8[slot] != NULL);
    for (len_t j = 0; j < length; ++j) {
        row[OFFSET+j] = next_integer();
        basis->cf_8[slot][j] = 1;
    }
    return row;
}

int main(int argc, char **argv)
{
    const int invalid = argc > 2 ? atoi(argv[2]) : 0;
    fail_allocation = argc > 1 ? (size_t)strtoul(argv[1], NULL, 10) : 0;
    const unsigned cases = next_integer();
    for (unsigned case_index = 0; case_index < cases; ++case_index) {
        mat_t mat = {0};
        md_t st = {.fc=2,.laopt=2,.nthrds=1,.trace_level=NO_TRACER,.print_gb=1};
        mat.nc = next_integer(); mat.ncl = next_integer(); mat.nrl = next_integer();
        mat.ncr = mat.nc-mat.ncl; mat.nru = mat.ncl; mat.nr = mat.nrl+mat.nru;
        bs_t known = {.ld=mat.ncl}, lower = {.ld=mat.nrl};
        known.cf_8 = calloc(mat.ncl ? mat.ncl : 1, sizeof(*known.cf_8));
        lower.cf_8 = calloc(mat.nrl ? mat.nrl : 1, sizeof(*lower.cf_8));
        mat.rr = calloc(mat.ncl ? mat.ncl : 1, sizeof(*mat.rr));
        mat.tr = calloc(mat.nrl ? mat.nrl : 1, sizeof(*mat.tr));
        mat.cf_8 = calloc(mat.nr ? mat.nr : 1, sizeof(*mat.cf_8));
        old_count = old_remaining = mat.ncl;
        old_rows = calloc(old_count ? old_count : 1, sizeof(*old_rows));
        size_t *known_lengths = calloc(mat.ncl ? mat.ncl : 1, sizeof(*known_lengths));
        size_t *lower_lengths = calloc(mat.nrl ? mat.nrl : 1, sizeof(*lower_lengths));
        assert(known.cf_8 && lower.cf_8 && mat.rr && mat.tr && mat.cf_8 && old_rows);
        for (len_t i = 0; i < mat.ncl; ++i) {
            const len_t slot = mat.ncl-1-i;
            old_rows[i] = mat.rr[i] = read_row(&known, slot, i);
            known_lengths[slot] = mat.rr[i][LENGTH];
        }
        for (len_t i = 0; i < mat.nrl; ++i) {
            const len_t slot = mat.nrl-1-i;
            mat.tr[i] = read_row(&lower, slot, i);
            lower_lengths[slot] = mat.tr[i][LENGTH];
        }
        /* Fail-closed entry conditions; the sample must have old/lower rows. */
        switch (invalid) {
            case 1: st.fc=3; break;
            case 2: st.nthrds=2; break;
            case 3: st.trace_level=1; break;
            case 4: st.nf=1; break;
            case 5: st.in_final_reduction_step=1; break;
            case 6: st.nev=1; break;
            case 7: st.print_gb=0; break;
            case 8: st.laopt=1; break;
            case 9: mat.nru++; break;
            case 10: mat.ncr++; break;
            case 11: mat.tr[0][COEFFS]=lower.ld; break;
            case 12: lower.cf_8[mat.tr[0][COEFFS]][0]=0; break;
            case 13: mat.tr[0][PRELOOP]=17; break;
            case 14: mat.tr[0][OFFSET+1]=mat.tr[0][OFFSET]; break;
            case 15: mat.tr[0][OFFSET+1]=mat.nc; break;
            case 16: mat.rr[0][OFFSET]=1; break;
        }
        lower_container = mat.tr; lower_container_freed = 0; allocations = 0;
        exact_sparse_reduced_echelon_form_ff_2_bitset(&mat, &lower, &known, &st);
        assert(old_remaining == 0 && lower_container_freed);
        assert(mat.np == mat.nr && mat.np == mat.sz && mat.np == st.np);
        for (len_t i = 0; i < mat.ncl; ++i) {
            assert(mat.rr[i] == NULL);
            for (size_t j = 0; j < known_lengths[i]; ++j) assert(known.cf_8[i][j] == 1);
        }
        for (len_t i = 0; i < mat.nrl; ++i)
            for (size_t j = 0; j < lower_lengths[i]; ++j) assert(lower.cf_8[i][j] == 1);
        printf("CASE %u %u %zu\n", case_index, mat.np, allocations);
        for (len_t i = 0; i < mat.np; ++i) {
            hm_t *row = mat.tr[i];
            assert(row[COEFFS] < mat.nrl && row[PRELOOP] == row[LENGTH] % UNROLL);
            printf("ROW %u %u %u %u", row[COEFFS], row[BINDEX], row[MULT], row[LENGTH]);
            for (len_t j = 0; j < row[LENGTH]; ++j) {
                assert(mat.cf_8[row[COEFFS]][j] == 1);
                printf(" %u", row[OFFSET+j]);
            }
            printf("\n");
            free(mat.cf_8[row[COEFFS]]);
            free(row);
        }
        for (len_t i = 0; i < mat.ncl; ++i) free(known.cf_8[i]);
        for (len_t i = 0; i < mat.nrl; ++i) free(lower.cf_8[i]);
        free(known.cf_8); free(lower.cf_8); free(mat.rr); free(mat.tr); free(mat.cf_8);
        free(old_rows); free(known_lengths); free(lower_lengths);
        old_rows = NULL; old_count = old_remaining = 0; lower_container = NULL;
    }
    return 0;
}
