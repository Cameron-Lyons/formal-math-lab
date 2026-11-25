
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
                hd_t *hd; hi_t *hmap; val_t *rn; len_t nv,ndv,bpv,*dv; int32_t mo; sdm_t *dm;} ht_t;
typedef struct {len_t ncl,ncr,nc,np; hm_t **tr;} mat_t;
#define OFFSET 6
#define LENGTH 5
#define ERRSTREAM stderr
#define VERBSTREAM stdout
static sdm_t generate_short_divmask(const exp_t *a,const ht_t *ht) {
    (void)a;(void)ht;return 0;
}

typedef len_t bl_t;
typedef struct {bl_t ld; uint8_t *red; hm_t **hm;} bs_t;
typedef struct {hi_t lcm;} spair_t;
typedef struct {len_t ld; spair_t *p;} ps_t;
typedef struct {double rht_ctime,rht_rtime; int32_t init_hts;} md_t;
static double cputime(void){return 0;}
static double realtime(void){return 0;}

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
ht_t *copy_hash_table(
    const ht_t *bht
    )
{
    hl_t j;

    ht_t *ht  = (ht_t *)malloc(sizeof(ht_t));

    ht->nv    = bht->nv;
    ht->mo    = bht->mo;
    ht->evl   = bht->evl;
    ht->ebl   = bht->ebl;
    ht->hsz   = bht->hsz;
    ht->esz   = bht->esz;

    ht->hmap  = calloc(ht->hsz, sizeof(hi_t));
    memcpy(ht->hmap, bht->hmap, (unsigned long)ht->hsz * sizeof(hi_t));

    ht->ndv = bht->ndv;
    ht->bpv = bht->bpv;
    ht->dm  = bht->dm;
    ht->rn  = bht->rn;
    ht->dv  = bht->dv;

    /* generate exponent vector */
    /* keep first entry empty for faster divisibility checks */
    ht->hd  = (hd_t *)calloc(ht->esz, sizeof(hd_t));

    memcpy(ht->hd, bht->hd, (unsigned long)ht->esz * sizeof(hd_t));
    ht->ev  = (exp_t **)malloc(ht->esz * sizeof(exp_t *));
    if (ht->ev == NULL) {
        fprintf(ERRSTREAM, "Computation needs too much memory on this machine,\n");
        fprintf(ERRSTREAM, "could not initialize exponent vector for hash table,\n");
        fprintf(ERRSTREAM, "esz = %lu, segmentation fault will follow.\n", (unsigned long)ht->esz);
    }
    exp_t *tmp  = (exp_t *)malloc(
            (unsigned long)ht->evl * ht->esz * sizeof(exp_t));
    if (tmp == NULL) {
        fprintf(ERRSTREAM, "Exponent storage needs too much memory on this machine,\n");
        fprintf(ERRSTREAM, "initialization failed, esz = %lu,\n", (unsigned long)ht->esz);
        fprintf(ERRSTREAM, "segmentation fault will follow.\n");
    }
    memcpy(tmp, bht->ev[0], (unsigned long)ht->evl * ht->esz * sizeof(exp_t));
    ht->eld = bht->eld;
    const hl_t esz  = ht->esz;
    for (j = 0; j < esz; ++j) {
        ht->ev[j]  = tmp + (j*ht->evl);
    }
    return ht;
}



ht_t *initialize_secondary_hash_table(
    const ht_t * const bht,
    const md_t * const md
    )
{
    hl_t j;

    ht_t *ht  = (ht_t *)malloc(sizeof(ht_t));
    ht->nv    = bht->nv;
    ht->mo    = bht->mo;
    ht->evl   = bht->evl;
    ht->ebl   = bht->ebl;

    /* generate map */
    int32_t min = 3 > md->init_hts-5 ? 3 : md->init_hts-5;
    ht->hsz   = (hl_t)pow(2, min);
    ht->esz   = ht->hsz / 2;
    ht->hmap  = calloc(ht->hsz, sizeof(hi_t));

    /* divisor mask and random number seeds from basis hash table */
    ht->ndv = bht->ndv;
    ht->bpv = bht->bpv;
    ht->dm  = bht->dm;
    ht->rn  = bht->rn;
    ht->dv  = bht->dv;

    /* generate exponent vector */
    /* keep first entry empty for faster divisibility checks */
    ht->eld = 1;
    ht->hd  = (hd_t *)calloc(ht->esz, sizeof(hd_t));
    ht->ev  = (exp_t **)malloc(ht->esz * sizeof(exp_t *));
    if (ht->ev == NULL) {
        fprintf(ERRSTREAM, "Computation needs too much memory on this machine,\n");
        fprintf(ERRSTREAM, "could not initialize exponent vector for hash table,\n");
        fprintf(ERRSTREAM, "esz = %lu, segmentation fault will follow.\n", (unsigned long)ht->esz);
    }
    exp_t *tmp  = (exp_t *)malloc(
            (unsigned long)ht->evl * ht->esz * sizeof(exp_t));
    if (tmp == NULL) {
        fprintf(ERRSTREAM, "Exponent storage needs too much memory on this machine,\n");
        fprintf(ERRSTREAM, "initialization failed, esz = %lu,\n", (unsigned long)ht->esz);
        fprintf(ERRSTREAM, "segmentation fault will follow.\n");
    }
    const hl_t esz  = ht->esz;
    for (j = 0; j < esz; ++j) {
        ht->ev[j]  = tmp + (j*ht->evl);
    }
    return ht;
}


static void enlarge_hash_table(
    ht_t *ht
    )
{
    hl_t i, j;
    val_t h, k;

    ht->esz = 2 * ht->esz;
    const hl_t esz  = ht->esz;
    const hi_t eld  = ht->eld;

    ht->hd    = realloc(ht->hd, esz * sizeof(hd_t));
    memset(ht->hd+eld, 0, (esz-eld) * sizeof(hd_t));
    ht->ev    = realloc(ht->ev, esz * sizeof(exp_t *));
    if (ht->ev == NULL) {
        fprintf(ERRSTREAM, "Enlarging hash table failed for esz = %lu,\n", (unsigned long)esz);
        fprintf(ERRSTREAM, "segmentation fault will follow.\n");
    }
    /* note: memory is allocated as one big block, so reallocating
     *       memory from ev[0] is enough    */
    ht->ev[0] = realloc(ht->ev[0],
            esz * (unsigned long)ht->evl * sizeof(exp_t));
    if (ht->ev[0] == NULL) {
        fprintf(ERRSTREAM, "Enlarging exponent vector for hash table failed\n");
        fprintf(ERRSTREAM, "for esz = %lu, segmentation fault will follow.\n", (unsigned long)esz);
    }
    /* due to realloc we have to reset ALL ev entries,
     * memory might have been moved */
    for (i = 1; i < esz; ++i) {
        ht->ev[i] = ht->ev[0] + (i*ht->evl);
    }

    /* The hash table should be double the size of the exponent space in
     * order to never get a fill in over 50%. If the exponent size is now
     * enlarge to 2^31 elements that's the limit we can go. Thus we cannot
     * enlarge the hash table size any further and have to live with more
     * than 50% fill in. */
    if (ht->hsz < (hl_t)pow(2,32)) {
        ht->hsz = 2 * ht->hsz;
        const hl_t hsz  = ht->hsz;
        ht->hmap  = realloc(ht->hmap, hsz * sizeof(hi_t));
        if (ht->hmap == NULL) {
            fprintf(ERRSTREAM, "Enlarging hash table failed for hsz = %lu,\n", (unsigned long)hsz);
            fprintf(ERRSTREAM, "segmentation fault will follow.\n");
        }
        memset(ht->hmap, 0, hsz * sizeof(hi_t));
        const hi_t mod =  (hi_t )(hsz-1);

        /* reinsert known elements */
        for (i = 1; i < eld; ++i) {
            h = ht->hd[i].val;

            /* probing */
            k = h;
            for (j = 0; j < hsz; ++j) {
                k = (k+j) & mod;
                if (ht->hmap[k]) {
                    continue;
                }
                ht->hmap[k] = i;
                break;
            }
        }
    } else {
        if (ht->hsz == (hl_t)pow(2,32)) {
          fprintf(ERRSTREAM, "Exponent space is now 2^32 elements wide, we cannot\n");
          fprintf(ERRSTREAM, "enlarge the hash table any further, thus fill in gets\n");
          fprintf(ERRSTREAM, "over 50%% and performance of hashing may get worse.\n");
        } else {
          fprintf(ERRSTREAM, "Hash table is full, we can no longer enlarge\n");
          fprintf(ERRSTREAM, "Segmentation fault will follow.\n");
          free(ht->hmap);
          ht->hmap  = NULL;
        }
    }
}


static inline int32_t is_contained_in_hash_table(
        const exp_t *a,
        const ht_t * const ht,
        const val_t h,
        hi_t *kp
        )
{
    hl_t i;
    hi_t k;
    len_t j;
    /* const len_t evl = ht->evl;
     * const hl_t hsz = ht->hsz; */
    /* ht->hsz <= 2^32 => mod is always uint32_t */
    const hi_t mod = (hi_t)(ht->hsz - 1);

    /* probing */
    k = h;
    i = 0;
restart:
    for (; i < ht->hsz; ++i) {
        k = (hi_t)((k+i) & mod);
        const hi_t hm = ht->hmap[k];
        if (!hm) {
            *kp = k;
            return 0;
        }
        if (ht->hd[hm].val != h) {
            continue;
        }
        const exp_t * const ehm = ht->ev[hm];
        for (j = 0; j < ht->evl-1; j += 2) {
            if (a[j] != ehm[j] || a[j+1] != ehm[j+1]) {
                i++;
                goto restart;
            }
        }
        if (a[ht->evl-1] != ehm[ht->evl-1]) {
            i++;
            goto restart;
        }
        *kp = hm;
        return 1;
    }
    return -1;
}


static inline hi_t insert_in_hash_table(
    const exp_t *a,
    ht_t *ht
    )
{
    hl_t i;
    hi_t k, pos;
    len_t j;
    exp_t *e;
    hd_t *d;
    val_t h = 0;
    const len_t evl = ht->evl;
    const hl_t hsz = ht->hsz;
    /* ht->hsz <= 2^32 => mod is always uint32_t */
    const hi_t mod = (hi_t)(ht->hsz - 1);

    /* generate hash value */
    for (j = 0; j < evl; ++j) {
        h +=  ht->rn[j] * a[j];
    }
    /* probing */
    k = h;
    i = 0;
restart:
    for (; i < hsz; ++i) {
        k = (hi_t)((k+i) & mod);
        const hi_t hm = ht->hmap[k];
        if (!hm) {
            break;
        }
        if (ht->hd[hm].val != h) {
            continue;
        }
        const exp_t * const ehm = ht->ev[hm];
        for (j = 0; j < evl-1; j += 2) {
            if (a[j] != ehm[j] || a[j+1] != ehm[j+1]) {
                i++;
                goto restart;
            }
        }
        if (a[evl-1] != ehm[evl-1]) {
            i++;
            goto restart;
        }
        return hm;
    }

    /* add element to hash table */
    ht->hmap[k]  = pos = (hi_t)ht->eld;
    e   = ht->ev[pos];
    d   = ht->hd + pos;
    memcpy(e, a, (unsigned long)evl * sizeof(exp_t));
    d->sdm  =   generate_short_divmask(e, ht);
    d->deg  =   e[0];
    d->deg  +=  ht->ebl > 0 ? e[ht->ebl] : 0;
    d->val  =   h;

    ht->eld++;

    return pos;
}


static inline void reinitialize_hash_table(
    ht_t *ht,
    const hl_t size
    )
{
    hl_t i;
    /* is there still enough space in the local table? */
    if (size >= (ht->esz)) {
        while (size >= ht->esz) {
            ht->esz = 2 * ht->esz;
            ht->hsz = 2 * ht->hsz;
        }
        const hl_t esz  = ht->esz;
        const hl_t hsz  = ht->hsz;
        const len_t evl = ht->evl;
        ht->hd  = realloc(ht->hd, esz * sizeof(hd_t));
        ht->ev  = realloc(ht->ev, esz * sizeof(exp_t *));
        if (ht->ev == NULL) {
            fprintf(ERRSTREAM, "Computation needs too much memory on this machine,\n");
            fprintf(ERRSTREAM, "could not reinitialize exponent vector for hash table,\n");
            fprintf(ERRSTREAM, "esz = %lu, segmentation fault will follow.\n", (unsigned long)esz);
        }
        /* note: memory is allocated as one big block, so reallocating
         *       memory from evl[0] is enough    */
        ht->ev[0]  = realloc(ht->ev[0],
                esz * (unsigned long)evl * sizeof(exp_t));
        if (ht->ev[0] == NULL) {
            fprintf(ERRSTREAM, "Exponent storage needs too much memory on this machine,\n");
            fprintf(ERRSTREAM, "reinitialization failed, esz = %lu\n", (unsigned long)esz);
            fprintf(ERRSTREAM, "segmentation fault will follow.\n");
        }
        /* due to realloc we have to reset ALL evl entries, memory might be moved */
        for (i = 1; i < esz; ++i) {
            ht->ev[i] = ht->ev[0] + (i*evl);
        }
        ht->hmap  = realloc(ht->hmap, hsz * sizeof(hi_t));
    }
    memset(ht->hd, 0, ht->esz * sizeof(hd_t));
    memset(ht->hmap, 0, ht->hsz * sizeof(hi_t));

    ht->eld  = 1;
}

static inline void clean_hash_table(
        ht_t *ht
    )
{
    memset(ht->hd, 0, ht->esz * sizeof(hd_t));
    memset(ht->hmap, 0, ht->hsz * sizeof(hi_t));

    ht->eld  = 1;
}


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

/* Private allocations only: rn/dv/dm remain borrowed from the basis table. */
static void *symbolic_stage_calloc(const size_t count, const size_t width)
{
    if (count == 0 || width == 0 || count > SIZE_MAX/width) {
        fprintf(ERRSTREAM, "Error: invalid staged symbolic allocation size.\n");
        exit(EXIT_FAILURE);
    }
    void *result = calloc(count, width);
    if (result == NULL) {
        fprintf(ERRSTREAM, "Error: cannot allocate restored symbolic storage.\n");
        exit(EXIT_FAILURE);
    }
    return result;
}

/* Consume the completed symbolic table, keeping only genuinely new vectors.
 * hcm still maps missing columns to OLD symbolic IDs on entry.  For an
 * ascending old ID i, packed rank k is <=i; copying slot i to k cannot
 * overwrite any unread slot.  Column order is deliberately NOT used for
 * this packing step.  hcm records the new packed positions so the caller
 * can retain its original ascending-column insertion order afterwards. */
static exp_t *stage_missing_symbolic_exponents(
        hi_t *hcm, const uint8_t *used, const mat_t *mat,
        ht_t *sht, const len_t missing, const int info_level)
{
    if (sht == NULL || sht->evl == 0 || sht->esz < 2 ||
            (sht->esz & (sht->esz-1)) != 0 ||
            sht->eld != (hl_t)mat->nc+1 || sht->eld > sht->esz ||
            sht->eld > UINT32_MAX || missing > mat->ncr ||
            sht->hsz < sht->eld || sht->hsz > SIZE_MAX/sizeof(hi_t) ||
            mat->ncl > mat->nc || mat->ncr != mat->nc-mat->ncl ||
            sht->ev == NULL || sht->ev[0] == NULL ||
            sht->hd == NULL || sht->hmap == NULL || hcm == NULL ||
            (mat->ncr > 0 && used == NULL) ||
            (size_t)sht->evl > SIZE_MAX/sizeof(exp_t)) {
        fprintf(ERRSTREAM, "Error: invalid symbolic staging layout.\n");
        exit(EXIT_FAILURE);
    }
    const hl_t old_capacity = sht->esz, old_load = sht->eld;
    const size_t vector_bytes = (size_t)sht->evl*sizeof(exp_t);
    const hl_t slots = (hl_t)missing+1;
    if (old_capacity > SIZE_MAX/vector_bytes || slots > SIZE_MAX/vector_bytes) {
        fprintf(ERRSTREAM, "Error: symbolic staging byte count overflows.\n");
        exit(EXIT_FAILURE);
    }
    exp_t *block = sht->ev[0];

    /* Symbolic bucket lookup is finished. Reuse a small prefix of its
     * PRIVATE bucket storage to verify the entire inverse-map bijection,
     * avoiding another column-sized allocation. */
    const size_t seen_bytes = ((size_t)mat->nc+7)/8;
    if (seen_bytes > (size_t)sht->hsz*sizeof(hi_t)) {
        fprintf(ERRSTREAM, "Error: insufficient symbolic validation storage.\n");
        exit(EXIT_FAILURE);
    }
    uint8_t *seen = (uint8_t *)sht->hmap;
    memset(seen, 0, seen_bytes);
    for (len_t i = 0; i < mat->ncr; ++i) {
        if (used[i] > 2) {
            fprintf(ERRSTREAM, "Error: invalid staged symbolic support mask.\n");
            exit(EXIT_FAILURE);
        }
    }

    /* Validate the inverse map and all selected source pointers before
     * mutating hcm or overwriting the slab.  Existing-basis hcm entries
     * have already changed, so inverse equality is required only for new
     * entries.  No lookup into sht occurs after this function returns. */
    hl_t found = 0;
    for (hl_t id = 1; id < old_load; ++id) {
        const hi_t column = sht->hd[id].idx;
        if (column >= mat->nc || (seen[column/8] & (1U << (column%8)))) {
            fprintf(ERRSTREAM, "Error: invalid symbolic inverse column.\n");
            exit(EXIT_FAILURE);
        }
        seen[column/8] |= 1U << (column%8);
        if (column >= mat->ncl && used[column-mat->ncl] == 1) {
            if (hcm[column] != id || sht->ev[id] != block+id*sht->evl) {
                fprintf(ERRSTREAM, "Error: inconsistent staged symbolic mapping.\n");
                exit(EXIT_FAILURE);
            }
            ++found;
        }
    }
    if (found != missing) {
        fprintf(ERRSTREAM, "Error: staged symbolic missing count disagrees.\n");
        exit(EXIT_FAILURE);
    }
    hl_t packed = 0;
    for (hl_t id = 1; id < old_load; ++id) {
        const hi_t column = sht->hd[id].idx;
        if (column >= mat->ncl && used[column-mat->ncl] == 1) {
            ++packed;
            if (packed > id) {
                fprintf(ERRSTREAM, "Error: unsafe symbolic compaction direction.\n");
                exit(EXIT_FAILURE);
            }
            if (packed != id)
                memmove(block+packed*sht->evl, block+id*sht->evl, vector_bytes);
            hcm[column] = (hi_t)packed;
        }
    }
    if (packed != missing) {
        fprintf(ERRSTREAM, "Error: symbolic packed count disagrees.\n");
        exit(EXIT_FAILURE);
    }

    /* Retire only this table's private arrays.  In particular do not call
     * full_free_hash_table or free_shared_hash_data here.  Keep the same
     * ht_t object so the caller's local sht and md->ht remain identical. */
    free(sht->hd); sht->hd = NULL;
    free(sht->hmap); sht->hmap = NULL;
    free(sht->ev); sht->ev = NULL;
    exp_t *staged = realloc(block, (size_t)slots*vector_bytes);
    if (staged == NULL) {
        fprintf(ERRSTREAM, "Error: cannot shrink staged symbolic exponent data.\n");
        exit(EXIT_FAILURE);
    }

    /* Restore a fully usable empty secondary table BEFORE basis reserve.
     * Starting with at most 2048 slots avoids keeping the former high-water
     * allocation; future ordinary secondary growth is unchanged. */
    const hl_t reset_capacity = old_capacity < 2048 ? old_capacity : 2048;
    sht->hd = symbolic_stage_calloc((size_t)reset_capacity, sizeof(hd_t));
    sht->hmap = symbolic_stage_calloc((size_t)(2*reset_capacity), sizeof(hi_t));
    sht->ev = symbolic_stage_calloc((size_t)reset_capacity, sizeof(exp_t *));
    exp_t *fresh = symbolic_stage_calloc((size_t)reset_capacity, vector_bytes);
    for (hl_t id = 0; id < reset_capacity; ++id)
        sht->ev[id] = fresh+id*sht->evl;
    sht->esz = reset_capacity;
    sht->hsz = 2*reset_capacity;
    sht->eld = 1;
    if (info_level > 1) {
        fprintf(VERBSTREAM, "\nMSOLVE_SYMBOLIC_STAGING old_load=%lu old_capacity=%lu missing=%u old_exponent_bytes=%zu staged_exponent_bytes=%zu reset_capacity=%lu\n",
                (unsigned long)old_load, (unsigned long)old_capacity, missing,
                (size_t)old_capacity*vector_bytes, (size_t)slots*vector_bytes,
                (unsigned long)reset_capacity);
        fflush(VERBSTREAM);
    }
    return staged;
}

/* Used only by exact, non-tracing ordinary F4 export computations. */
static inline void switch_used_hcm_data_to_basis_hash_table(
    hi_t *hcm,
    ht_t *bht,
    const mat_t *mat,
    const ht_t * const sht,
    ht_t *consumable_sht,
    const int info_level
    )
{
    if (mat->ncl > mat->nc || mat->ncr != mat->nc-mat->ncl ||
            (mat->np > 0 && mat->tr == NULL) || bht->eld > bht->esz ||
            bht == sht || bht->evl != sht->evl ||
            (consumable_sht != NULL && consumable_sht != sht)) {
        fprintf(ERRSTREAM, "Error: invalid retained-column promotion dimensions.\n");
        exit(EXIT_FAILURE);
    }
    uint8_t *used = calloc((size_t)mat->ncr, sizeof(uint8_t));
    if (mat->ncr > 0 && used == NULL) {
        fprintf(ERRSTREAM, "Error: cannot allocate retained-column support mask.\n");
        exit(EXIT_FAILURE);
    }
    len_t referenced = 0;
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
                ++referenced;
            }
        }
    }
    const hl_t before = bht->eld;
    len_t missing = 0;
    for (len_t column = mat->ncl; column < mat->nc; ++column) {
        if (used[column-mat->ncl]) {
            const hi_t symbolic_hash = hcm[column];
            if (symbolic_hash == 0 || symbolic_hash >= sht->eld) {
                fprintf(ERRSTREAM, "Error: invalid symbolic hash in column promotion.\n");
                exit(EXIT_FAILURE);
            }
            const exp_t * const exponent = sht->ev[symbolic_hash];
            val_t hash = 0;
            for (len_t j = 0; j < bht->evl; ++j) {
                hash += bht->rn[j] * exponent[j];
            }
            hi_t position = 0;
            const int32_t contained = is_contained_in_hash_table(
                    exponent, bht, hash, &position);
            if (contained == 1) {
                if (position == 0 || position >= bht->eld) {
                    fprintf(ERRSTREAM, "Error: invalid existing hash in column promotion.\n");
                    exit(EXIT_FAILURE);
                }
                /* Existing entry IDs survive enlargement; bucket indices do not. */
                hcm[column] = position;
                used[column-mat->ncl] = 2;
            } else if (contained == 0) {
                ++missing;
            } else {
                fprintf(ERRSTREAM, "Error: basis hash lookup failed in column promotion.\n");
                exit(EXIT_FAILURE);
            }
        }
    }
    if (info_level > 1) {
        fprintf(VERBSTREAM, "\nMSOLVE_PROMOTION_RESERVATION nonpivot=%u referenced=%u missing=%u basis_load=%lu basis_capacity=%lu\n",
                mat->ncr, referenced, missing, (unsigned long)bht->eld,
                (unsigned long)bht->esz);
        fflush(VERBSTREAM);
    }
    exp_t *staged = NULL;
    /* Only consume the symbolic table when basis storage must grow. */
    if (consumable_sht != NULL &&
            (bht->eld >= bht->esz || missing >= bht->esz-bht->eld)) {
        staged = stage_missing_symbolic_exponents(hcm, used, mat,
                consumable_sht, missing, info_level);
    }
    reserve_basis_hash_table_for_promotion(bht, missing, info_level);
    /* Ascending column order preserves the order of retained insertions. */
    for (len_t column = mat->ncl; column < mat->nc; ++column) {
        if (used[column-mat->ncl] == 1) {
            const hi_t symbolic_hash = hcm[column];
            if (bht->eld >= bht->esz) {
                fprintf(ERRSTREAM, "Error: insufficient reserved capacity in column promotion.\n");
                exit(EXIT_FAILURE);
            }
            const exp_t *exponent;
            if (staged != NULL) {
                if (symbolic_hash == 0 || symbolic_hash > missing) {
                    fprintf(ERRSTREAM, "Error: invalid staged symbolic position.\n");
                    exit(EXIT_FAILURE);
                }
                exponent = staged+(size_t)symbolic_hash*bht->evl;
            } else {
                exponent = sht->ev[symbolic_hash];
            }
            hcm[column] = insert_in_hash_table(exponent, bht);
        }
    }
    if (bht->eld-before != missing) {
        fprintf(ERRSTREAM, "Error: missing-column count disagrees with hash insertions.\n");
        exit(EXIT_FAILURE);
    }
    free(staged);
    free(used);
    if (info_level > 1) {
        fprintf(VERBSTREAM, "\nMSOLVE_PROMOTION_COLUMNS nonpivot=%u referenced=%u inserted=%lu basis_capacity=%lu\n",
                mat->ncr, referenced, (unsigned long)(bht->eld-before),
                (unsigned long)bht->esz);
        fflush(VERBSTREAM);
    }
}


static inline void reinsert_in_hash_table(
    hm_t *row,
    exp_t * const *oev,
    ht_t *ht
    )
{
    hl_t i;
    hi_t k, pos;
    len_t j, l;
    exp_t *e;
    hd_t *d;
    val_t h;

    const len_t len = row[LENGTH]+OFFSET;
    const len_t evl = ht->evl;
    const hi_t hsz  = ht->hsz;
    /* ht->hsz <= 2^32 => mod is always uint32_t */
    const hi_t mod  = (hi_t)(hsz - 1);
    l = OFFSET;
letsgo:
    for (; l < len; ++l) {
        const exp_t * const n = oev[row[l]];
        /* generate hash value */
        h = 0;
        for (j = 0; j < evl; ++j) {
            h +=  ht->rn[j] * n[j];
        }
        k = h;
        i = 0;
restart:
        for (; i < hsz; ++i) {
            k = (hi_t)(k+i) & mod;
            const hi_t hm  = ht->hmap[k];
            if (!hm) {
                break;
            }
            if (ht->hd[hm].val != h) {
                continue;
            }
            const exp_t * const ehm = ht->ev[hm];
            for (j = 0; j < evl-1; j += 2) {
                if (n[j] != ehm[j] || n[j+1] != ehm[j+1]) {
                    i++;
                    goto restart;
                }
            }
            if (n[evl-1] != ehm[evl-1]) {
                i++;
                goto restart;
            }
            row[l] = hm;
            l++;
            goto letsgo;
        }

        /* add element to hash table */
        ht->hmap[k] = pos = (hi_t)ht->eld;
        e = ht->ev[ht->eld];
        d = ht->hd + ht->eld;
        memcpy(e, n, (unsigned long)evl * sizeof(exp_t));
        d->sdm  =   generate_short_divmask(e, ht);
        d->deg  =   e[0];
        d->deg  +=  ht->ebl > 0 ? e[ht->ebl] : 0;
        d->val  =   h;

        ht->eld++;
        row[l] =  pos;
    }
}


static void reset_hash_table(
    ht_t *ht,
    bs_t *bs,
    ps_t *psl,
    md_t *st
    )
{
    /* timings */
    double ct0, ct1, rt0, rt1;
    ct0 = cputime();
    rt0 = realtime();

    len_t i;
    hi_t k;
    exp_t *e;

    spair_t *ps = psl->p;
    exp_t **oev  = ht->ev;

    const len_t evl = ht->evl;
    const hl_t esz  = ht->esz;
    const bl_t bld  = bs->ld;
    const len_t pld = psl->ld;

    ht->ev  = calloc(esz, sizeof(exp_t *));
    if (ht->ev == NULL) {
        fprintf(ERRSTREAM, "Computation needs too much memory on this machine,\n");
        fprintf(ERRSTREAM, "cannot reset ht->ev, esz = %lu\n", (unsigned long)esz);
        fprintf(ERRSTREAM, "segmentation fault will follow.\n");
    }
    exp_t *tmp  = (exp_t *)malloc(
            (unsigned long)evl * esz * sizeof(exp_t));
    if (tmp == NULL) {
        fprintf(ERRSTREAM, "Computation needs too much memory on this machine,\n");
        fprintf(ERRSTREAM, "resetting table failed, esz = %lu\n", (unsigned long)esz);
        fprintf(ERRSTREAM, "segmentation fault will follow.\n");
    }
    for (k = 0; k < esz; ++k) {
        ht->ev[k]  = tmp + k*evl;
    }
    ht->eld = 1;
    memset(ht->hmap, 0, ht->hsz * sizeof(hi_t));
    memset(ht->hd, 0, esz * sizeof(hd_t));

    /* reinsert known elements */
    for (i = 0; i < bld; ++i) {
      if (bs->red[i] < 2) {
        reinsert_in_hash_table(bs->hm[i], oev, ht);
      }
    }
    for (i = 0; i < pld; ++i) {
        e = oev[ps[i].lcm];
#if PARALLEL_HASHING
        ps[i].lcm = check_insert_in_hash_table(e, 0, ht);
#else
        ps[i].lcm = insert_in_hash_table(e, ht);
#endif
    }
    /* note: all memory is allocated as a big block, so it is
     *       enough to free oev[0].       */
    free(oev[0]);
    free(oev);

    /* timings */
    ct1 = cputime();
    rt1 = realtime();
    st->rht_ctime  +=  ct1 - ct0;
    st->rht_rtime  +=  rt1 - rt0;
}


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
