
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
static inline void switch_used_hcm_data_to_basis_hash_table(
    hi_t *hcm,
    ht_t *bht,
    const mat_t *mat,
    const ht_t * const sht,
    const int info_level
    )
{
    if (mat->ncl > mat->nc || mat->ncr != mat->nc-mat->ncl ||
            (mat->np > 0 && mat->tr == NULL) || bht->eld > bht->esz) {
        fprintf(ERRSTREAM, "Error: invalid retained-column promotion dimensions.\n");
        exit(EXIT_FAILURE);
    }
    uint8_t *used = calloc((size_t)mat->ncr, sizeof(uint8_t));
    if (mat->ncr > 0 && used == NULL) {
        fprintf(ERRSTREAM, "Error: cannot allocate retained-column support mask.\n");
        exit(EXIT_FAILURE);
    }
    len_t needed = 0;
    for (len_t i = 0; i < mat->np; ++i) {
        const hm_t *row = mat->tr[i];
        if (row == NULL || row[LENGTH] == 0 || row[LENGTH] > mat->ncr) {
            fprintf(ERRSTREAM, "Error: invalid retained row in column promotion.\n");
            exit(EXIT_FAILURE);
        }
        for (len_t j = 0; j < row[LENGTH]; ++j) {
            const hi_t column = row[(size_t)OFFSET+j];
            if (column < mat->ncl || column >= mat->nc) {
                fprintf(ERRSTREAM, "Error: retained column is outside the nonpivot block.\n");
                exit(EXIT_FAILURE);
            }
            if (used[column-mat->ncl] == 0) {
                used[column-mat->ncl] = 1;
                ++needed;
            }
        }
    }
    const hl_t before = bht->eld;
    while (bht->esz - bht->eld < needed) {
        enlarge_hash_table(bht);
    }
    /* Ascending column order preserves the order of retained insertions. */
    for (len_t column = mat->ncl; column < mat->nc; ++column) {
        if (used[column-mat->ncl]) {
            const hi_t symbolic_hash = hcm[column];
            if (symbolic_hash == 0 || symbolic_hash >= sht->eld) {
                fprintf(ERRSTREAM, "Error: invalid symbolic hash in column promotion.\n");
                exit(EXIT_FAILURE);
            }
            hcm[column] = insert_in_hash_table(sht->ev[symbolic_hash], bht);
        }
    }
    free(used);
    if (info_level > 1) {
        fprintf(VERBSTREAM, "\nMSOLVE_PROMOTION_COLUMNS nonpivot=%u referenced=%u inserted=%lu basis_capacity=%lu\n",
                mat->ncr, needed, (unsigned long)(bht->eld-before),
                (unsigned long)bht->esz);
        fflush(VERBSTREAM);
    }
}
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
