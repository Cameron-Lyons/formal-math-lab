
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


static inline void switch_used_hcm_data_to_basis_hash_table(
    hi_t *hcm,
    ht_t *bht,
    const mat_t *mat,
    const ht_t * const sht,
    const int info_level
    )
{
    if (mat->ncl > mat->nc || mat->ncr != mat->nc-mat->ncl ||
            (mat->np > 0 && mat->tr == NULL) || bht->eld > bht->esz ||
            bht == sht || bht->evl != sht->evl) {
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
    while (bht->esz - bht->eld < missing) {
        enlarge_hash_table(bht);
    }
    /* Ascending column order preserves the order of retained insertions. */
    for (len_t column = mat->ncl; column < mat->nc; ++column) {
        if (used[column-mat->ncl] == 1) {
            const hi_t symbolic_hash = hcm[column];
            if (bht->eld >= bht->esz) {
                fprintf(ERRSTREAM, "Error: insufficient reserved capacity in column promotion.\n");
                exit(EXIT_FAILURE);
            }
            hcm[column] = insert_in_hash_table(sht->ev[symbolic_hash], bht);
        }
    }
    if (bht->eld-before != missing) {
        fprintf(ERRSTREAM, "Error: missing-column count disagrees with hash insertions.\n");
        exit(EXIT_FAILURE);
    }
    free(used);
    if (info_level > 1) {
        fprintf(VERBSTREAM, "\nMSOLVE_PROMOTION_COLUMNS nonpivot=%u referenced=%u inserted=%lu basis_capacity=%lu\n",
                mat->ncr, referenced, (unsigned long)(bht->eld-before),
                (unsigned long)bht->esz);
        fflush(VERBSTREAM);
    }
}


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
