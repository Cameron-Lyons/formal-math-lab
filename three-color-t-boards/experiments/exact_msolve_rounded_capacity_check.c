
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
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wtype-limits"
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wtautological-constant-out-of-range-compare"
#endif
static void reserve_basis_hash_table_for_promotion(
    ht_t *ht,
    const hl_t additional,
    const int info_level
    )
{
    const hl_t quantum = (hl_t)1 << 16;
    /* Avoid the legacy reset path's uint32_t narrowing at hsz == 2^32. */
    const hl_t max_entries = (hl_t)1 << 30;
    const hl_t max_buckets = (hl_t)1 << 31;
    if (ht == NULL || ht->esz == 0 || ht->esz > max_entries ||
            ht->eld == 0 || ht->eld > ht->esz || ht->evl == 0 ||
            ht->hsz == 0 || ht->hsz > max_buckets ||
            (ht->hsz & (ht->hsz-1)) != 0 || ht->esz > ht->hsz/2 ||
            ht->ev == NULL || ht->ev[0] == NULL || ht->hd == NULL ||
            ht->hmap == NULL) {
        fprintf(ERRSTREAM, "Error: unsupported hash layout in promotion reserve.\n");
        exit(EXIT_FAILURE);
    }
    /* Keep one spare entry for legacy callers that test eld == esz-1. */
    if (ht->eld >= max_entries || additional > max_entries-1-ht->eld) {
        fprintf(ERRSTREAM, "Error: promotion reserve exceeds supported entry limit.\n");
        exit(EXIT_FAILURE);
    }
    const hl_t required = ht->eld + additional + 1;
    if (required <= ht->esz) {
        return;
    }
    const hl_t new_esz = ((required+quantum-1)/quantum)*quantum;
    hl_t new_hsz = ht->hsz;
    while (new_hsz/2 < new_esz) {
        if (new_hsz >= max_buckets) {
            fprintf(ERRSTREAM, "Error: promotion reserve exceeds supported bucket limit.\n");
            exit(EXIT_FAILURE);
        }
        new_hsz *= 2;
    }
    if (new_esz > max_entries ||
            new_esz > SIZE_MAX/sizeof(hd_t) ||
            new_esz > SIZE_MAX/sizeof(exp_t *) ||
            ht->evl > SIZE_MAX/sizeof(exp_t) ||
            new_esz > SIZE_MAX/((size_t)ht->evl*sizeof(exp_t)) ||
            new_hsz > SIZE_MAX/sizeof(hi_t)) {
        fprintf(ERRSTREAM, "Error: promotion reserve allocation size overflow.\n");
        exit(EXIT_FAILURE);
    }
    if (info_level > 1) {
        fprintf(VERBSTREAM, "\nMSOLVE_PROMOTION_CAPACITY_REQUEST required_with_spare=%lu exponent_old=%lu exponent_new=%lu buckets_old=%lu buckets_new=%lu\n",
                (unsigned long)required, (unsigned long)ht->esz,
                (unsigned long)new_esz, (unsigned long)ht->hsz,
                (unsigned long)new_hsz);
        fflush(VERBSTREAM);
    }

    hd_t *new_hd = realloc(ht->hd, (size_t)new_esz*sizeof(hd_t));
    if (new_hd == NULL) {
        fprintf(ERRSTREAM, "Error: cannot allocate promotion hash metadata.\n");
        exit(EXIT_FAILURE);
    }
    ht->hd = new_hd;
    memset(ht->hd+ht->eld, 0, (size_t)(new_esz-ht->eld)*sizeof(hd_t));
    exp_t *old_block = ht->ev[0];
    exp_t **new_ev = realloc(ht->ev, (size_t)new_esz*sizeof(exp_t *));
    if (new_ev == NULL) {
        fprintf(ERRSTREAM, "Error: cannot allocate promotion exponent pointers.\n");
        exit(EXIT_FAILURE);
    }
    ht->ev = new_ev;
    exp_t *new_block = realloc(old_block,
            (size_t)new_esz*(size_t)ht->evl*sizeof(exp_t));
    if (new_block == NULL) {
        fprintf(ERRSTREAM, "Error: cannot allocate promotion exponent data.\n");
        exit(EXIT_FAILURE);
    }
    /* No exponent-data pointer survives realloc, including slot zero. */
    for (hl_t i = 0; i < new_esz; ++i) {
        ht->ev[i] = new_block + i*ht->evl;
    }

    if (new_hsz != ht->hsz) {
        hi_t *new_hmap = realloc(ht->hmap, (size_t)new_hsz*sizeof(hi_t));
        if (new_hmap == NULL) {
            fprintf(ERRSTREAM, "Error: cannot allocate promotion hash buckets.\n");
            exit(EXIT_FAILURE);
        }
        ht->hmap = new_hmap;
        memset(ht->hmap, 0, (size_t)new_hsz*sizeof(hi_t));
        const hi_t mask = (hi_t)(new_hsz-1);
        for (hl_t i = 1; i < ht->eld; ++i) {
            hi_t bucket = ht->hd[i].val;
            int placed = 0;
            for (hl_t j = 0; j < new_hsz; ++j) {
                bucket = (hi_t)((bucket+j) & mask);
                if (ht->hmap[bucket] == 0) {
                    ht->hmap[bucket] = (hi_t)i;
                    placed = 1;
                    break;
                }
            }
            if (!placed) {
                fprintf(ERRSTREAM, "Error: promotion rehash could not place an entry.\n");
                exit(EXIT_FAILURE);
            }
        }
    }
    ht->esz = new_esz;
    ht->hsz = new_hsz;
}
#pragma GCC diagnostic pop

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
