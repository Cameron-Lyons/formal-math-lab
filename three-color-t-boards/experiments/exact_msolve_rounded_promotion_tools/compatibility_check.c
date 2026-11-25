
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

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wtype-limits"
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wtautological-constant-out-of-range-compare"
#endif
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


#pragma GCC diagnostic pop

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
