
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
static exp_t capture[8][128];
static unsigned captures;
/* Capture the conventional vector before the native insertion boundary.
 * Hash allocation/probing is covered by complete native fixtures, not here. */
static hi_t insert_in_hash_table(const exp_t *e,ht_t *h) {
 assert(captures<8);memcpy(capture[captures],e,h->evl*sizeof(exp_t));return ++captures;
}
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


static uint32_t state=0x63e52125u;
static unsigned next(void){state^=state<<13;state^=state>>17;state^=state<<5;return state;}
static void vector(exp_t *e,unsigned n,unsigned budget){
 memset(e,0,128);for(unsigned k=0;k<budget;k++){unsigned i=1+next()%n;e[i]++;e[0]++;}
}
static void matrix_tests(void){
 for(unsigned trial=0;trial<1200;trial++){
  unsigned n=1+next()%127;exp_t a[128],b[128],c[128],scratch[128];
  unsigned total=next()%256,budget=next()%(total+1);
  vector(a,n,budget);vector(b,n,total-budget);vector(c,n,total-budget);
  exp_t *source[]={b,c},*dest[]={scratch};ht_t src={n,n+1,0,0,source},dst={n,n+1,0,0,dest};
  hm_t poly[OFFSET+2]={0},row[OFFSET+2]={0};poly[LENGTH]=2;poly[OFFSET]=0;poly[OFFSET+1]=1;
  captures=0;insert_multiplied_poly_in_hash_table(row,0,a,poly,&src,&dst);
  assert(captures==2&&row[OFFSET]==1&&row[OFFSET+1]==2);
  for(unsigned j=0;j<=n;j++){assert(capture[0][j]==(unsigned)a[j]+b[j]);assert(capture[1][j]==(unsigned)a[j]+c[j]);}
  exp_t *pair[]={a,b};ht_t ht={n,n+1,0,0,pair};captures=0;get_lcm(0,1,&ht,&dst);
  unsigned degree=0;for(unsigned j=1;j<=n;j++){unsigned x=a[j]>b[j]?a[j]:b[j];assert(capture[0][j]==x);degree+=x;}
  assert(capture[0][0]==degree);
  int32_t input[3*127]={0};for(unsigned j=0;j<n;j++)input[2*n+j]=a[j+1];
  exp_t converted[128];md_t md={0};set_exponent_vector(converted,input,2,&ht,&md);
  assert(!memcmp(converted,a,n+1));
 }
 /* Reach the proved maximum for127 variables and the n=2 pure-cube edge. */
 exp_t a[128]={3,3},b[128]={254},out[128];for(unsigned j=1;j<128;j++)b[j]=2;
 exp_t *pair[]={a,b},*dest[]={out};ht_t src={127,128,0,0,pair},dst={127,128,0,0,dest};
 captures=0;get_lcm(0,1,&src,&dst);assert(capture[0][0]==255);
 memset(a,0,128);memset(b,0,128);a[0]=a[1]=3;b[0]=b[2]=3;src.nv=dst.nv=2;src.evl=dst.evl=3;
 captures=0;get_lcm(0,1,&src,&dst);assert(capture[0][0]==6);
}
static void fault(unsigned k){
 switch(k){
  case 0:checked_exp_value(INT64_MIN);return;
  case 1:checked_exp_value(INT64_MAX);return;
  case 2:checked_exp_value(-1);return;
  case 3:checked_exp_value(256);return;
  case 4:checked_exp_add(128,128);return;
  case 5:checked_exp_add(255,255);return;
  case 6:checked_exp_sub(254,255);return;
  case 7:checked_exp_sub(0,255);return;
 }
 exp_t a[128]={0},b[128]={0},work[128];exp_t *pair[]={a,b},*dest[]={work};
 ht_t src={2,3,0,0,pair},dst={2,3,0,0,dest};md_t md={0};int32_t input[2]={0};
 if(k==8){input[0]=-256;set_exponent_vector(work,input,0,&src,&md);}
 if(k==9){input[0]=65537;set_exponent_vector(work,input,0,&src,&md);}
 if(k==10){input[0]=200;input[1]=56;set_exponent_vector(work,input,0,&src,&md);}
 if(k==11){a[0]=a[1]=128;b[0]=b[2]=128;captures=0;get_lcm(0,1,&src,&dst);}
 if(k==12||k==13){
  hm_t poly[OFFSET+1]={0},row[OFFSET+1]={0};poly[LENGTH]=1;poly[OFFSET]=1;
  if(k==12){a[0]=200;b[0]=56;}
  else{a[0]=b[0]=0;a[1]=255;b[1]=1;}
  captures=0;insert_multiplied_poly_in_hash_table(row,0,a,poly,&src,&dst);
 }
}
int main(int argc,char **argv){
 if(argc>1){fault((unsigned)strtoul(argv[1],0,10));fprintf(stderr,"FAIL: missing overflow exit\n");return 2;}
 unsigned good=0;for(unsigned a=0;a<=255;a++){
  assert(checked_exp_value(a)==a);
  for(unsigned b=0;b<=255;b++){
   if(a+b<=255){assert(checked_exp_add(a,b)==a+b);good++;}
   if(a>=b){assert(checked_exp_sub(a,b)==a-b);good++;}
  }
 }
 assert(good==65792&&sizeof(exp_t)==1);matrix_tests();
 puts("PASS:65792 integer operations;1200 input-index/LCM/two-term products;degree255 and degree6");return 0;
}
