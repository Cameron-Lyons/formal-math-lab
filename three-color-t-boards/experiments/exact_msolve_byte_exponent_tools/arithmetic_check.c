
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <limits.h>
typedef uint8_t exp_t;
static inline exp_t checked_exp_value(const int64_t value)
{
    if (value < 0 || value > UINT8_MAX) {
        fprintf(stderr, "Error: byte exponent/degree overflow.\n");
        exit(EXIT_FAILURE);
    }
    return (exp_t)value;
}
static inline exp_t checked_exp_add(const exp_t a, const exp_t b)
{
    return checked_exp_value((uint32_t)a+(uint32_t)b);
}
static inline exp_t checked_exp_sub(const exp_t a, const exp_t b)
{
    return checked_exp_value((int32_t)a-(int32_t)b);
}

typedef uint32_t len_t,hi_t,hm_t,val_t;
typedef struct {len_t nv,evl,ebl,eld;exp_t **ev;} ht_t;
typedef struct {len_t nev;} md_t;
#define OFFSET 6
#define LENGTH 5
#define PARALLEL_HASHING 0
static exp_t captured[129];
static hi_t insert_in_hash_table(const exp_t *e,ht_t *h){memcpy(captured,e,h->evl*sizeof(exp_t));return 1;}

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wunused-parameter"
static inline void set_exponent_vector(
        exp_t *ev,
        const int32_t *iev,  /* input exponent vectors */
        const int64_t idx,
        const ht_t *ht,
        const md_t *st
        )
{
    len_t i;

    const len_t nv  = ht->nv;
    const len_t ebl = ht->ebl;
    const len_t nev = st->nev;
    const len_t off = ebl - nev + 1;

    ev[0]   = 0;
    ev[ebl] = 0;

    for (i = 0; i < nev; ++i) {
        ev[i+1] = checked_exp_value((iev+((int64_t)nv * idx))[i]);
        /* degree */
        ev[0] = checked_exp_add(ev[0], ev[i+1]);
    }
    for (i = nev; i < nv; ++i) {
        ev[i+off] = checked_exp_value((iev+((int64_t)nv * idx))[i]);
        /* degree */
        ev[ebl] = checked_exp_add(ev[ebl], ev[i+off]);
    }
}

static inline hi_t get_lcm(
    const hi_t a,
    const hi_t b,
    const ht_t *ht1,
    ht_t *ht2
    )
{
    len_t i;

    /* exponents of basis elements, thus from basis hash table */
    const exp_t * const ea = ht1->ev[a];
    const exp_t * const eb = ht1->ev[b];
    exp_t etmp[ht1->evl];
    const len_t evl = ht1->evl;
    const len_t ebl = ht1->ebl;

    /* set degree(s), if ebl == 0, i.e. we do not have an elimination block
     * order then the second for loop is just not executed and the third one
     * computes correctly the full degree of the lcm. */
    for (i = 1; i < evl; ++i) {
        etmp[i]  = ea[i] < eb[i] ? eb[i] : ea[i];
    }
    /* reset degree entries */
    etmp[0]   = 0;
    etmp[ebl] = 0;
    for (i = 1; i < ebl; ++i) {
        etmp[0] = checked_exp_add(etmp[0], etmp[i]);
    }
    for (i = ebl+1; i < evl; ++i) {
        etmp[ebl] = checked_exp_add(etmp[ebl], etmp[i]);
    }
    /* printf("lcm -> ");
     * for (int ii = 0; ii < evl; ++ii) {
     *     printf("%d ", etmp[ii]);
     * }
     * printf("\n"); */
#if PARALLEL_HASHING
    return check_insert_in_hash_table(etmp, 0, ht2);
#else
    return insert_in_hash_table(etmp, ht2);
#endif
}

static inline void insert_multiplied_poly_in_hash_table(
    hm_t *row,
    const val_t h1,
    const exp_t * const ea,
    const hm_t * const b,
    const ht_t * const ht1,
    ht_t *ht2
    )
{
    len_t j, l;
    exp_t *n;

    const len_t len = b[LENGTH]+OFFSET;
    const len_t evl = ht1->evl;

    exp_t * const *ev1      = ht1->ev;
    /* const hd_t * const hd1  = ht1->hd; */

    exp_t **ev2     = ht2->ev;

    l = OFFSET;

    for (; l < len; ++l) {
        const exp_t * const eb = ev1[b[l]];

        n = ev2[ht2->eld];
        for (j = 0; j < evl; ++j) {
            n[j] = checked_exp_add(ea[j], eb[j]);
        }

#if PARALLEL_HASHING
        const val_t h   = h1 + hd1[b[l]].val;
        row[l] = check_insert_in_hash_table(n, h, ht2);
#else
        row[l] = insert_in_hash_table(n, ht2);
#endif
    }
}


#pragma GCC diagnostic pop

static void product(int overflow) {
 exp_t a[4]={8,2,3,3},b[4]={9,3,4,2},out[4]={0};
 if(overflow==1){a[0]=255;b[0]=1;}
 if(overflow==2){a[0]=1;b[0]=1;a[1]=255;b[1]=1;}
 exp_t *src[1]={b},*dst[1]={out};ht_t ht1={3,4,0,0,src},ht2={3,4,0,0,dst};
 hm_t poly[OFFSET+1]={0},row[OFFSET+1]={0};poly[LENGTH]=1;poly[OFFSET]=0;
 insert_multiplied_poly_in_hash_table(row,0,a,poly,&ht1,&ht2);
 for(int i=0;i<4;i++)assert(captured[i]==(unsigned)a[i]+b[i]);
}
static void lcmbound(int overflow) {
 exp_t a[128]={0},b[128]={0};
 len_t n=overflow?3:127;
 if(overflow){a[0]=200;a[1]=100;a[2]=100;b[0]=200;b[2]=100;b[3]=100;}
 else {a[0]=3;a[1]=3;b[0]=254;for(unsigned i=1;i<=n;i++)b[i]=2;}
 exp_t *ev[2]={a,b};ht_t ht={n,n+1,0,0,ev};get_lcm(0,1,&ht,&ht);
 assert(captured[0]==255&&captured[1]==3);for(unsigned i=2;i<=n;i++)assert(captured[i]==2);
}
int main(int argc,char **argv) {
 if(argc>1){
  int id=atoi(argv[1]);
  switch(id){
   case 1:checked_exp_value(-1);break;case 2:checked_exp_value(256);break;
   case 3:checked_exp_value(INT64_MAX);break;case 4:checked_exp_add(255,1);break;
   case 5:checked_exp_sub(0,1);break;case 6:lcmbound(1);break;
   case 7:product(1);break;case 8:product(2);break;
   case 9:case 10:case 11:{int32_t in[2]={1,1};exp_t out[3];ht_t ht={2,3,0,0,NULL};md_t md={0};
     if(id==9)in[0]=-1;
     if(id==10)in[0]=256;
     if(id==11){in[0]=200;in[1]=100;}
     set_exponent_vector(out,in,0,&ht,&md);break;}
  }
  fputs("expected failure did not occur\n",stderr);return 3;
 }
 assert(sizeof(exp_t)==1);
 unsigned count=0;
 for(unsigned a=0;a<256;a++){
  assert(checked_exp_value(a)==a);
  for(unsigned b=0;b<256;b++){
   if(a+b<=255){assert(checked_exp_add(a,b)==a+b);count++;}
   if(a>=b){assert(checked_exp_sub(a,b)==a-b);count++;}
  }
 }
 int32_t input[127];for(unsigned i=0;i<127;i++)input[i]=2;
 exp_t output[128];ht_t ht={127,128,0,0,NULL};md_t md={0};
 set_exponent_vector(output,input,0,&ht,&md);assert(output[0]==254);
 input[0]=3;set_exponent_vector(output,input,0,&ht,&md);assert(output[0]==255);
 lcmbound(0);product(0);
 printf("PASS valid_add_sub=%u values=256 boundary_input_degrees=254,255 lcm_degree=255 multiplied_rows=1\n",count);
}
