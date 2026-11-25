
#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef uint64_t hl_t;
typedef uint32_t hi_t;
typedef uint32_t hm_t;
typedef uint32_t len_t;
typedef uint32_t val_t;
typedef uint16_t exp_t;
typedef struct {uint32_t val,deg,sdm,idx;} hd_t;
typedef struct {
 exp_t **ev; hd_t *hd; hi_t *hmap; len_t elo; hl_t eld,esz,hsz;
 len_t ebl; int32_t mo; len_t nv,evl; uint32_t *dm,*dv,ndv,bpv,*rn,rsd;
} ht_t;
typedef struct {len_t ncl,ncr,nc,np; hm_t **tr;} mat_t;
typedef struct {ht_t *ht;int fc,laopt,nthrds,trace_level,nf,in_final_reduction_step,nev,print_gb,info_level;} md_t;
#define NO_TRACER 0
#define OFFSET 6
#define LENGTH 5
#define ERRSTREAM stderr
#define VERBSTREAM stdout
static void *allocations[256];
static size_t allocation_sizes[256];
static int allocation_calls=0, fail_call=0, count_calls=0;
static uint32_t borrowed_rn[128],borrowed_dv[128],borrowed_dm[128];
static int find_allocation(void *p) {
 for(int i=0;i<256;i++)if(allocations[i]==p)return i;
 assert(!"untracked pointer");return -1;
}
static void remember(void *p,size_t n) {
 assert(p);for(int i=0;i<256;i++)if(!allocations[i]){
  allocations[i]=p;allocation_sizes[i]=n;return;
 }assert(!"too many tracked allocations");
}
static int should_fail(void) {
 if(!count_calls)return 0;
 allocation_calls++;return allocation_calls==fail_call;
}
static void *review_calloc(size_t n,size_t width) {
 if(should_fail())return NULL;
 void *p=calloc(n?n:1,width?width:1);assert(p);remember(p,(n?n:1)*(width?width:1));return p;
}
static void *review_realloc(void *p,size_t n) {
 assert(n>0);if(should_fail())return NULL;
 int i=find_allocation(p);void *q=realloc(p,n);assert(q);
 allocations[i]=q;allocation_sizes[i]=n;return q;
}
static void review_free(void *p) {
 if(!p)return;
 assert(p!=borrowed_rn && p!=borrowed_dv && p!=borrowed_dm);
 int i=find_allocation(p);allocations[i]=NULL;allocation_sizes[i]=0;free(p);
}
static void cleanup(void) {
 for(int i=0;i<256;i++)if(allocations[i]){free(allocations[i]);allocations[i]=NULL;}
}
#define calloc review_calloc
#define realloc review_realloc
#define free review_free
static ht_t table(hl_t capacity,len_t width) {
 ht_t t={0};t.esz=capacity;t.hsz=2;while(t.hsz<2*capacity)t.hsz*=2;t.eld=1;t.evl=width;
 t.nv=width-1;t.elo=37;t.ebl=0;t.mo=0;t.ndv=5;t.bpv=6;t.rsd=123;
 t.rn=borrowed_rn;t.dv=borrowed_dv;t.dm=borrowed_dm;
 t.hd=calloc(capacity,sizeof(hd_t));t.hmap=calloc(t.hsz,sizeof(hi_t));
 t.ev=calloc(capacity,sizeof(exp_t*));exp_t *block=calloc(capacity*width,sizeof(exp_t));
 for(hl_t i=0;i<capacity;i++)t.ev[i]=block+i*width;
 return t;
}
static val_t hash_vector(const ht_t *t,const exp_t *v) {
 val_t h=0;for(len_t j=0;j<t->evl;j++)h+=t->rn[j]*v[j];return h;
}
static int32_t is_contained_in_hash_table(const exp_t *v,const ht_t *t,
                                         val_t hash,hi_t *position) {
 assert(hash==hash_vector(t,v));
 for(hi_t i=1;i<t->eld;i++)if(!memcmp(v,t->ev[i],t->evl*sizeof(exp_t))){*position=i;return 1;}
 *position=UINT32_MAX;return 0;
}
static hi_t insert_in_hash_table(const exp_t *v,ht_t *t) {
 hi_t pos=0;val_t h=hash_vector(t,v);
 if(is_contained_in_hash_table(v,t,h,&pos))return pos;
 assert(t->eld<t->esz);pos=(hi_t)t->eld++;
 memcpy(t->ev[pos],v,t->evl*sizeof(exp_t));
 t->hd[pos]=(hd_t){h,v[0],pos+3,pos+7};
 hi_t bucket=h;
 for(hl_t step=0;step<t->hsz;step++){
  bucket=(hi_t)((bucket+step)&(t->hsz-1));
  if(!t->hmap[bucket]){t->hmap[bucket]=pos;return pos;}
 }assert(!"reference probe exhausted");return 0;
}
static void destroy(ht_t *t) {free(t->ev[0]);free(t->ev);free(t->hd);free(t->hmap);}
static uint32_t rng=0x4192ae75;
static uint32_t next_random(void){rng^=rng<<13;rng^=rng>>17;rng^=rng<<5;return rng;}

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wtype-limits"
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wtautological-constant-out-of-range-compare"
#endif
static void reserve_hash_table_checked(
    ht_t *ht,
    const hl_t additional,
    const hl_t quantum,
    const int info_level,
    const char *context
    )
{
    /* Avoid the legacy reset path's uint32_t narrowing at hsz == 2^32. */
    const hl_t max_entries = (hl_t)1 << 30;
    const hl_t max_buckets = (hl_t)1 << 31;
    if (quantum == 0 || quantum > ((hl_t)1 << 16) ||
            (quantum & (quantum-1)) != 0 || context == NULL ||
            ht == NULL || ht->esz == 0 || ht->esz > max_entries ||
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
        fprintf(VERBSTREAM, "\nMSOLVE_%s_CAPACITY_REQUEST required_with_spare=%lu exponent_old=%lu exponent_new=%lu buckets_old=%lu buckets_new=%lu\n",
                context, (unsigned long)required, (unsigned long)ht->esz,
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

static void reserve_basis_hash_table_for_promotion(
        ht_t *ht, const hl_t additional, const int info_level)
{
    reserve_hash_table_checked(ht, additional, (hl_t)1 << 16,
            info_level, "PROMOTION");
}

static void reserve_symbolic_row_capacity(
        ht_t *sht, const hm_t *poly, const md_t *md)
{
    if (md == NULL) {
        fprintf(ERRSTREAM, "Error: missing metadata in symbolic row reserve.\n");
        exit(EXIT_FAILURE);
    }
    if (!((md->fc == 2 || md->fc == 3) && md->laopt == 2 &&
            md->nthrds == 1 && md->trace_level == NO_TRACER &&
            md->nf == 0 && md->in_final_reduction_step == 0 &&
            md->nev == 0 && md->print_gb > 0)) {
        return;
    }
    const hl_t max_entries = (hl_t)1 << 30;
    if (sht == NULL || md->ht != sht || poly == NULL ||
            sht->eld == 0 || sht->eld >= max_entries ||
            (hl_t)poly[LENGTH] > max_entries-1-sht->eld) {
        fprintf(ERRSTREAM, "Error: invalid symbolic row reservation.\n");
        exit(EXIT_FAILURE);
    }
    const hl_t required = sht->eld+(hl_t)poly[LENGTH]+1;
    if (required <= sht->esz) {
        return;
    }
    /* Geometric growth for small tables; 64K rounding above that scale. */
    hl_t quantum = 2;
    while (quantum < required && quantum < ((hl_t)1 << 16)) {
        quantum *= 2;
    }
    const hl_t requested = ((required+quantum-1)/quantum)*quantum;
    if (md->info_level > 1) {
        fprintf(VERBSTREAM, "\nMSOLVE_SYMBOLIC_ROW_RESERVE old_load=%lu row_length=%lu required_with_spare=%lu requested_capacity=%lu\n",
                (unsigned long)sht->eld, (unsigned long)poly[LENGTH],
                (unsigned long)required, (unsigned long)requested);
        fflush(VERBSTREAM);
    }
    reserve_hash_table_checked(sht, (hl_t)poly[LENGTH], quantum,
            md->info_level, "SYMBOLIC");
}

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

static exp_t *stage_missing_symbolic_exponents(
        hi_t *hcm, const uint8_t *used, const mat_t *mat,
        ht_t *sht, const len_t missing, const int info_level)
{
    if (sht == NULL || sht->evl == 0 || sht->esz < 2 ||
            /* Large non-power capacities restore to power-of-two 2048. */
            (sht->esz < 2048 && (sht->esz & (sht->esz-1)) != 0) ||
            sht->eld != (hl_t)mat->nc+1 || sht->eld > sht->esz ||
            sht->eld > UINT32_MAX || missing > mat->ncr ||
            sht->hsz < sht->eld || sht->hsz > SIZE_MAX/sizeof(hi_t) ||
            sht->hsz == 0 || (sht->hsz & (sht->hsz-1)) != 0 ||
            sht->esz > sht->hsz/2 ||
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
#pragma GCC diagnostic pop

static int staged_cases=0,unchanged_cases=0,large_resets=0,zero_missing_cases=0,nonpower_stages=0;
static void verify_scalars(const ht_t *s,const ht_t *old) {
 assert(s->nv==old->nv && s->mo==old->mo && s->evl==old->evl && s->ebl==old->ebl);
 assert(s->rn==old->rn && s->dm==old->dm && s->dv==old->dv);
 assert(s->ndv==old->ndv && s->bpv==old->bpv && s->elo==old->elo && s->rsd==old->rsd);
}
static void one_case(unsigned iteration,int fault) {
 count_calls=0;
 len_t nc=iteration%31==0?2053:8+next_random()%113;
 len_t ncl=next_random()%(nc/3+1),width=1+next_random()%97;
 if(fault){nc=8;ncl=2;width=7;}
 hl_t cap=4;while(cap<=nc)cap*=2;
 if(iteration%31==0&&!fault)cap=6144;
 if(iteration%379==0&&!fault){cap=196608;width=3;}
 ht_t symbolic=table(cap,width),basis=table(fault?4:cap,width);
 for(hi_t id=1;id<=nc;id++){
  for(len_t j=0;j<width;j++)symbolic.ev[id][j]=(exp_t)(id*17+j*53);
  symbolic.hd[id]=(hd_t){id+19,id+23,id+29,0};
 }symbolic.eld=nc+1;
 hi_t *mapping=calloc(nc,sizeof(hi_t));
 for(len_t c=0;c<nc;c++)mapping[c]=c+1;
 for(len_t c=nc-1;c;c--){len_t d=next_random()%(c+1);hi_t tmp=mapping[c];mapping[c]=mapping[d];mapping[d]=tmp;}
 if(iteration%7==0)for(len_t c=0;c<nc;c++)mapping[c]=nc-c;
 for(len_t c=0;c<nc;c++)symbolic.hd[mapping[c]].idx=c;
 uint8_t *selected=calloc(nc,1);
 for(len_t c=ncl;c<nc;c++)selected[c]=(uint8_t)(next_random()%3!=0);
 if(fault)for(len_t c=ncl;c<nc;c++)selected[c]=1;
 if(iteration%13==0&&!fault)memset(selected+ncl,1,nc-ncl);
 if(iteration%17==0&&!fault)memset(selected+ncl,0,nc-ncl);
 /* Existing basis monomials overlap symbolic columns in arbitrary order. */
 for(len_t c=0;c<nc;c++)if((!fault && next_random()%3==0)||(fault&&c==2))
  insert_in_hash_table(symbolic.ev[mapping[c]],&basis);
 hi_t *expected_ids=calloc(nc,sizeof(hi_t));
 exp_t *expected=calloc((size_t)(basis.eld+nc)*width,sizeof(exp_t));
 hl_t before=basis.eld,next_id=before;
 memcpy(expected,basis.ev[0],(size_t)before*width*sizeof(exp_t));
 len_t missing=0,referenced=0;
 for(len_t c=ncl;c<nc;c++)if(selected[c]){
  referenced++;hi_t old_id=0;const exp_t *v=symbolic.ev[mapping[c]];
  if(!is_contained_in_hash_table(v,&basis,hash_vector(&basis,v),&old_id)){
   old_id=(hi_t)next_id++;missing++;memcpy(expected+(size_t)old_id*width,v,width*sizeof(exp_t));
  }expected_ids[c]=old_id;
 }
 /* Some cases force basis growth (including exact boundary), others do not. */
 if((iteration%2==0||fault)&&missing>0){
  hl_t bcap=2;while(bcap<before)bcap*=2;
  if(bcap==before+missing+1)bcap*=2;
  if(before+missing+1>bcap){
   basis.esz=bcap; /* Backing allocation remains larger; real reserve shrinks/grows correctly. */
  }
 }
 if(iteration%19==0&&!fault){
  /* A valid full table of existing terms still needs the requested spare. */
  if(before>1){basis.esz=before;}
 }
 mat_t mat={ncl,nc-ncl,nc,referenced?2:0,NULL};
 if(mat.np){
  mat.tr=calloc(2,sizeof(hm_t*));
  for(len_t i=0;i<2;i++){
   mat.tr[i]=calloc(OFFSET+referenced,sizeof(hm_t));mat.tr[i][LENGTH]=referenced;
   len_t k=0;for(len_t c=nc;c-->ncl;)if(selected[c])mat.tr[i][OFFSET+k++]=c;
  }
 }
 ht_t original_symbolic=symbolic;
 int consume=fault||iteration%5!=1;
 int should_stage=consume && (before>=basis.esz||missing>=basis.esz-before);
 allocation_calls=0;count_calls=1;
 switch_used_hcm_data_to_basis_hash_table(mapping,&basis,&mat,&symbolic,consume?&symbolic:NULL,0);
 count_calls=0;
 assert(basis.eld==next_id && basis.eld<basis.esz);
 for(hl_t id=0;id<next_id;id++)assert(!memcmp(basis.ev[id],expected+(size_t)id*width,width*sizeof(exp_t)));
 for(len_t c=ncl;c<nc;c++)if(selected[c])assert(mapping[c]==expected_ids[c]);
 verify_scalars(&symbolic,&original_symbolic);
 if(should_stage){
  staged_cases++;nonpower_stages+=!!(cap&(cap-1));if(!missing)zero_missing_cases++;
  hl_t reset=cap<2048?cap:2048;large_resets+=cap>2048;
  assert(symbolic.eld==1&&symbolic.esz==reset&&symbolic.hsz==2*reset);
  for(hl_t i=0;i<reset;i++){
   assert(symbolic.ev[i]==symbolic.ev[0]+i*width);
   hd_t zero={0};assert(!memcmp(&symbolic.hd[i],&zero,sizeof(zero)));
   for(len_t j=0;j<width;j++)assert(symbolic.ev[i][j]==0);
  }
  for(hl_t i=0;i<2*reset;i++)assert(symbolic.hmap[i]==0);
 }else{
  unchanged_cases++;assert(symbolic.eld==original_symbolic.eld&&symbolic.esz==cap);
  assert(symbolic.ev==original_symbolic.ev&&symbolic.hd==original_symbolic.hd&&symbolic.hmap==original_symbolic.hmap);
 }
 for(len_t i=0;i<mat.np;i++)free(mat.tr[i]);
 free(mat.tr);
 free(mapping);free(selected);free(expected_ids);free(expected);destroy(&symbolic);destroy(&basis);
 if(fault)printf("ALLOCATION_CALLS=%d\n",allocation_calls);
}
static void invalid_case(const char *which) {
 ht_t s=table(16,3);s.eld=9;
 hi_t hcm[8];uint8_t used[6]={1,0,1,0,1,0};
 for(hi_t i=1;i<9;i++){s.hd[i].idx=i-1;hcm[i-1]=i;}
 mat_t m={2,6,8,0,NULL};len_t missing=3;
 if(!strcmp(which,"nonpower"))s.esz=15;
 else if(!strcmp(which,"bad-load"))s.eld=8;
 else if(!strcmp(which,"bad-mask"))used[1]=3;
 else if(!strcmp(which,"duplicate-inverse"))s.hd[8].idx=1;
 else if(!strcmp(which,"out-of-range-inverse"))s.hd[8].idx=8;
 else if(!strcmp(which,"wrong-missing"))missing=4;
 else if(!strcmp(which,"wrong-new-map"))hcm[2]=7;
 else if(!strcmp(which,"nonflat-pointer"))s.ev[3]=s.ev[4];
 else if(!strcmp(which,"zero-width"))s.evl=0;
 else if(!strcmp(which,"overflow")){s.esz=UINT64_C(1)<<63;s.hsz=UINT64_C(1)<<63;}
 else if(!strcmp(which,"null-private"))s.hmap=NULL;
 else if(!strcmp(which,"nonpower-buckets"))s.hsz=31;
 else if(!strcmp(which,"undersized-buckets"))s.hsz=16;
 else assert(!"unknown invalid case");
 stage_missing_symbolic_exponents(hcm,used,&m,&s,missing,0);
 assert(!"invalid input accepted");
}

static md_t metadata(ht_t *t){md_t md={0};md.ht=t;md.fc=3;md.laopt=2;md.nthrds=1;md.print_gb=1;return md;}
static void row_case(hl_t capacity,hl_t load,len_t length,hl_t wanted) {
 count_calls=0;ht_t t=table(capacity,3);t.eld=load;ht_t original=t;
 for(hl_t id=1;id<load;id++){
  t.hd[id]=(hd_t){(uint32_t)id,(uint32_t)id+3,(uint32_t)id+5,(uint32_t)id+7};
  t.ev[id][0]=(exp_t)id;t.ev[id][1]=(exp_t)(id>>16);t.ev[id][2]=37;
  t.hmap[id]=(hi_t)id;
 }
 hm_t poly[OFFSET]={0};poly[LENGTH]=length;md_t md=metadata(&t);
 allocation_calls=0;count_calls=1;reserve_symbolic_row_capacity(&t,poly,&md);count_calls=0;
 assert(t.esz==wanted&&t.eld==load&&t.eld+(hl_t)length<t.esz);
 assert(t.hsz>=2*t.esz&&!(t.hsz&(t.hsz-1)));verify_scalars(&t,&original);
 for(hl_t id=1;id<load;id++){
  assert(t.hd[id].val==id&&t.hd[id].deg==id+3&&t.hd[id].sdm==id+5&&t.hd[id].idx==id+7);
  assert(t.ev[id][0]==(exp_t)id&&t.ev[id][1]==(exp_t)(id>>16)&&t.ev[id][2]==37);
  assert(t.hmap[id]==id);
 }
 for(hl_t id=0;id<t.esz;id++)assert(t.ev[id]==t.ev[0]+id*3);
 if(capacity==wanted)assert(allocation_calls==0);else assert(allocation_calls==3||allocation_calls==4);
 destroy(&t);
}
static void check_row_reserve(void) {
 row_case(8,6,1,8);row_case(8,6,2,16);row_case(32768,32760,7,32768);
 row_case(32768,32760,8,65536);row_case(65536,65530,5,65536);
 row_case(65536,65530,6,131072);row_case(131072,131060,12,196608);
 row_case(196608,196600,8,262144);
 ht_t t=table(8,3);t.eld=6;hm_t poly[OFFSET]={0};poly[LENGTH]=8;
 for(int mode=0;mode<8;mode++){
  md_t md=metadata(&t);
  if(mode==0)md.fc=5;
  if(mode==1)md.laopt=1;
  if(mode==2)md.nthrds=2;
  if(mode==3)md.trace_level=1;
  if(mode==4)md.nf=1;
  if(mode==5)md.in_final_reduction_step=1;
  if(mode==6)md.nev=1;
  if(mode==7)md.print_gb=0;
  ht_t old=t;allocation_calls=0;count_calls=1;
  reserve_symbolic_row_capacity(&t,poly,&md);count_calls=0;
  assert(!memcmp(&t,&old,sizeof(t))&&allocation_calls==0);
 }destroy(&t);
}
static void row_failure(const char *which,int number) {
 count_calls=0;ht_t t=table(8,3);t.eld=6;hm_t poly[OFFSET]={0};poly[LENGTH]=5;
 md_t md=metadata(&t);allocation_calls=0;count_calls=1;fail_call=number;
 if(!strcmp(which,"allocate")){
  reserve_symbolic_row_capacity(&t,poly,&md);printf("ROW_ALLOCATIONS=%d\n",allocation_calls);return;
 }
 if(!strcmp(which,"null-metadata"))reserve_symbolic_row_capacity(&t,poly,NULL);
 else if(!strcmp(which,"wrong-owner")){md.ht=NULL;reserve_symbolic_row_capacity(&t,poly,&md);}
 else if(!strcmp(which,"null-poly"))reserve_symbolic_row_capacity(&t,NULL,&md);
 else if(!strcmp(which,"oversized-row")){poly[LENGTH]=UINT32_MAX;reserve_symbolic_row_capacity(&t,poly,&md);}
 else if(!strcmp(which,"zero-load")){t.eld=0;reserve_symbolic_row_capacity(&t,poly,&md);}
 else if(!strcmp(which,"zero-quantum"))reserve_hash_table_checked(&t,3,0,0,"TEST");
 else if(!strcmp(which,"nonpower-quantum"))reserve_hash_table_checked(&t,3,3,0,"TEST");
 else if(!strcmp(which,"large-quantum"))reserve_hash_table_checked(&t,3,131072,0,"TEST");
 else if(!strcmp(which,"null-context"))reserve_hash_table_checked(&t,3,65536,0,NULL);
 else assert(!"unknown row failure");
 assert(!"invalid row reserve accepted");
}
static void plan(hl_t capacity,hl_t load,len_t length) {
 ht_t t=table(8,3);t.esz=capacity;t.eld=load;t.hsz=2;
 while(t.hsz<2*capacity)t.hsz*=2;
 hm_t poly[OFFSET]={0};poly[LENGTH]=length;md_t md=metadata(&t);md.info_level=2;
 allocation_calls=0;count_calls=1;fail_call=1;
 reserve_symbolic_row_capacity(&t,poly,&md);assert(!"plan expected first allocation failure");
}

int main(int argc,char **argv) {
 atexit(cleanup);for(int i=0;i<128;i++){borrowed_rn[i]=31+2*i;borrowed_dm[i]=i+51;borrowed_dv[i]=i+71;}
 if(argc>=3&&!strcmp(argv[1],"row")){row_failure(argv[2],argc>3?atoi(argv[3]):0);return 0;}
 if(argc==5&&!strcmp(argv[1],"plan")){plan(strtoull(argv[2],NULL,10),strtoull(argv[3],NULL,10),(len_t)strtoul(argv[4],NULL,10));return 0;}
 if(argc==3&&!strcmp(argv[1],"fail")){fail_call=atoi(argv[2]);one_case(2,1);return 0;}
 if(argc==3&&!strcmp(argv[1],"invalid")){invalid_case(argv[2]);return 0;}
 check_row_reserve();
 for(unsigned i=0;i<1200;i++)one_case(i,0);
 assert(nonpower_stages>0);
 assert(staged_cases>100&&unchanged_cases>100&&large_resets>0&&zero_missing_cases>0);
 printf("CASES=1200 STAGED=%d UNCHANGED=%d LARGE_RESET=%d ZERO_MISSING=%d NONPOWER=%d\n",staged_cases,unchanged_cases,large_resets,zero_missing_cases,nonpower_stages);
 return 0;
}
