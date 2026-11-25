#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include "msolve-cc044551f8e202d00691990fd3fd0b1226a88ea2/src/neogb/data.h"
static double cputime(void){return 0;}
static double realtime(void){return 0;}
static unsigned fail_at=0,allocation_calls=0;
static void *test_calloc(size_t n,size_t s){if(fail_at&&++allocation_calls==fail_at)return NULL;return calloc(n,s);}
static void *test_realloc(void *p,size_t s){if(fail_at&&++allocation_calls==fail_at)return NULL;return realloc(p,s);}
#define calloc test_calloc
#define realloc test_realloc
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wsign-compare"
#pragma GCC diagnostic ignored "-Wunknown-pragmas"
#pragma GCC diagnostic ignored "-Wunused-variable"
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-function"
#pragma GCC diagnostic ignored "-Wtype-limits"
#include "msolve-cc044551f8e202d00691990fd3fd0b1226a88ea2/src/neogb/hash.c"
#include "msolve-cc044551f8e202d00691990fd3fd0b1226a88ea2/src/neogb/sort_r.h"
#include "msolve-cc044551f8e202d00691990fd3fd0b1226a88ea2/src/neogb/order.c"
#pragma GCC diagnostic pop
#undef calloc
#undef realloc

static unsigned rng_state=0x91a03u;
static unsigned random_word(void){rng_state^=rng_state<<13;rng_state^=rng_state>>17;rng_state^=rng_state<<5;return rng_state;}
static ht_t *fresh(unsigned n,unsigned logsize,int collide){
    md_t md={0};md.nvars=n;md.init_hts=logsize;
    ht_t *h=initialize_basis_hash_table(&md);
    if(collide)memset(h->rn,0,h->evl*sizeof(val_t));
    assert(h->evbytes==h->evl&&h->evbytes==stored_exp_bytes(n+1));return h;
}
static void dense_code(exp_t *v,unsigned n,unsigned code){
    memset(v,0,(n+1)*sizeof(exp_t));
    for(unsigned i=1;i<=n;i++){v[i]=code%4;code/=4;v[0]=checked_exp_add(v[0],v[i]);}
    assert(!code);
}
static hi_t add_code(ht_t *h,unsigned code){
    exp_t v[h->evl];dense_code(v,h->nv,code);
    if(h->eld>=h->esz-1)enlarge_hash_table(h);
    return insert_in_hash_table(v,h);
}
static void verify(ht_t *h){
    assert(h->evbytes==h->evl&&h->eld<=h->esz&&h->esz<=h->hsz/2);
    for(hl_t i=0;i<h->esz;i++)assert(h->ev[i]==h->ev[0]+i*h->evbytes);
    for(hi_t id=1;id<h->eld;id++){
        exp_t v[h->evl];stored_exp_export(v,h->evl,h->ev[id],h->evbytes);
        unsigned sum=0;val_t hash=0;
        for(unsigned i=0;i<h->evl;i++){if(i)sum+=v[i];hash+=h->rn[i]*v[i];}
        assert(sum==v[0]&&hash==h->hd[id].val);
        hi_t got=0;assert(is_contained_in_hash_table(v,h,hash,&got)==1&&got==id);
        got=0;assert(is_contained_in_hash_table(h->ev[id],h,hash,&got)==1&&got==id);
    }
}
static int signum(int v){return (v>0)-(v<0);}
static void api_checks(void){
    for(unsigned n=1;n<=127;n++)for(unsigned round=0;round<16;round++){
        exp_t dense[128]={0},out[128]={0};stored_exp_t stored[128],copy[128];
        unsigned budget=255;
        for(unsigned i=1;i<=n;i++){dense[i]=random_word()%(budget+1);budget-=dense[i];dense[0]=checked_exp_add(dense[0],dense[i]);}
        stored_exp_import(stored,dense,n+1,n+1);
        assert(memcmp(stored,dense,n+1)==0); /* exact unchanged byte representation */
        stored_exp_copy(copy,stored,n+1,n+1);stored_exp_export(out,n+1,copy,n+1);
        assert(memcmp(out,dense,n+1)==0);
        for(unsigned i=0;i<=n;i++)assert(stored_exp_read(stored,i,n+1)==dense[i]);
    }
    stored_exp_t slab[16];
    for(unsigned i=0;i<16;i++)stored_exp_write(slab,i,i,16);
    stored_exp_copy_vectors(slab+4,slab,4,4,3);
    for(unsigned i=0;i<12;i++)assert(stored_exp_read(slab+4,i,16)==i);
    for(unsigned x=0;x<=255;x++){
        exp_t dense[2]={(exp_t)x,(exp_t)x};stored_exp_t s[2];
        stored_exp_import(s,dense,2,2);assert(stored_exp_read(s,1,2)==x);
    }
}
static void hash_checks(unsigned n,int collision){
    ht_t *h=fresh(n,4,collision);unsigned count=collision?200:700;
    for(unsigned code=1;code<=count;code++)assert(add_code(h,code)==code);
    calculate_divmask(h);verify(h);
    for(unsigned i=0;i<700;i++){
        hi_t a=1+random_word()%count,b=1+random_word()%count;
        exp_t aa[h->evl],bb[h->evl];stored_exp_export(aa,h->evl,h->ev[a],h->evbytes);stored_exp_export(bb,h->evl,h->ev[b],h->evbytes);
        int div=1,order=(int)aa[0]-(int)bb[0];
        for(unsigned j=1;j<h->evl;j++)if(aa[j]<bb[j])div=0;
        if(!order)for(unsigned j=h->evl-1;j>0;j--)if(aa[j]!=bb[j]){order=(int)bb[j]-(int)aa[j];break;}
        assert((int)check_monomial_division(a,b,h)==div);
        assert(signum(monomial_cmp_drl(a,b,h))==signum(order));
        if(h->eld>=h->esz-1)enlarge_hash_table(h);
        hi_t l=get_lcm(a,b,h,h);unsigned degree=0;
        for(unsigned j=1;j<h->evl;j++){unsigned e=aa[j]>bb[j]?aa[j]:bb[j];assert(stored_exp_read(h->ev[l],j,h->evl)==e);degree+=e;}
        assert(stored_exp_read(h->ev[l],0,h->evl)==degree);
    }
    ht_t *copy=copy_hash_table(h);verify(copy);
    assert(copy->evbytes==h->evbytes&&copy->rn==h->rn&&copy->dv==h->dv&&copy->dm==h->dm);
    for(hi_t id=1;id<h->eld;id++)assert(memcmp(h->ev[id],copy->ev[id],h->evbytes)==0);
    free_hash_table(&copy);full_free_hash_table(&h);
}
static void stage_case(unsigned rotation,int collide,int zero_missing,int injected){
    ht_t *b=fresh(5,4,collide);
    for(unsigned i=1;i<=5;i++)assert(add_code(b,i)==i);
    md_t initial={0};initial.init_hts=15;ht_t *s=initialize_secondary_hash_table(b,&initial);
    for(unsigned i=1;i<=23;i++)assert(add_code(s,i)==i);
    hi_t hcm[23];hm_t out[OFFSET+23]={0};out[LENGTH]=23;hm_t *rows[]={out};mat_t mat={0};
    mat.ncr=mat.nc=23;mat.np=1;mat.tr=rows;
    for(unsigned c=0;c<23;c++){hi_t id=1+(22-c+rotation)%23;hcm[c]=id;s->hd[id].idx=c;out[OFFSET+c]=c;}
    val_t *rn=s->rn;len_t *dv=s->dv;sdm_t *dm=s->dm;
    if(zero_missing){uint8_t used[23];memset(used,2,23);stored_exp_t *p=stage_missing_symbolic_exponents(hcm,used,&mat,s,0,0);free(p);}
    else{
        if(injected){allocation_calls=0;fail_at=injected;}
        switch_used_hcm_data_to_basis_hash_table(hcm,b,&mat,s,s,0);
        if(injected){fputs("fault not reached\n",stderr);exit(3);}
        assert(b->eld==24);
        hi_t next=6;
        for(unsigned c=0;c<23;c++){
            unsigned code=1+(22-c+rotation)%23;hi_t expected=code<=5?code:next++;
            assert(hcm[c]==expected);exp_t v[b->evl];dense_code(v,b->nv,code);
            exp_t got[b->evl];stored_exp_export(got,b->evl,b->ev[hcm[c]],b->evbytes);assert(memcmp(got,v,b->evl)==0);
        }
        verify(b);
    }
    assert(s->eld==1&&s->rn==rn&&s->dv==dv&&s->dm==dm);
    clean_hash_table(s);for(unsigned i=1;i<=900;i++)add_code(s,i);verify(s);
    ht_t *copy=copy_hash_table(s);verify(copy);free_hash_table(&copy);
    reinitialize_hash_table(s,s->esz);assert(s->eld==1);add_code(s,4);add_code(s,8);add_code(s,12);
    hm_t r0[OFFSET+2]={0},r1[OFFSET+1]={0};r0[LENGTH]=2;r0[OFFSET]=1;r0[OFFSET+1]=3;r1[LENGTH]=1;r1[OFFSET]=3;
    hm_t *rs[]={r0,r1};int8_t red[]={0,0};bs_t bs={0};bs.ld=2;bs.hm=rs;bs.red=red;
    spair_t pair={0};pair.lcm=2;ps_t ps={0};ps.ld=1;ps.p=&pair;md_t md={0};
    reset_hash_table(s,&bs,&ps,&md);verify(s);assert(s->eld==4&&r0[OFFSET+1]==r1[OFFSET]);
    free_hash_table(&s);full_free_hash_table(&b);
}
static void nonpower_row_case(void){
    ht_t *b=fresh(10,16,0);const unsigned length=30000;
    hm_t *poly=calloc(OFFSET+length,sizeof(hm_t));poly[LENGTH]=length;poly[COEFFS]=13;poly[PRELOOP]=length%4;
    for(unsigned i=1;i<=length;i++)poly[OFFSET+i-1]=add_code(b,i);
    md_t init={0};init.init_hts=23;ht_t *s=initialize_secondary_hash_table(b,&init);
    for(unsigned i=1;i<=120000;i++)assert(add_code(s,i)==i);
    ht_t *legacy=copy_hash_table(s);md_t md={0};md.fc=3;md.laopt=2;md.nthrds=1;md.print_gb=1;md.ht=s;
    reserve_symbolic_row_capacity(s,poly,&md);assert(s->esz==196608);
    exp_t multiplier[11]={0};multiplier[0]=multiplier[10]=1;
    hm_t *r=multiplied_poly_to_matrix_row(s,b,0,multiplier,poly);
    hm_t *old=multiplied_poly_to_matrix_row(legacy,b,0,multiplier,poly);
    assert(legacy->esz==262144&&s->eld==legacy->eld&&s->eld==150001);
    assert(memcmp(r,old,(OFFSET+length)*sizeof(hm_t))==0);
    for(hi_t i=1;i<s->eld;i++)assert(memcmp(s->ev[i],legacy->ev[i],s->evbytes)==0);
    verify(s);verify(legacy);
    free(r);free(old);free(poly);free_hash_table(&s);free_hash_table(&legacy);full_free_hash_table(&b);
}
static void invalid(unsigned kind){
    stored_exp_t s[4]={0};exp_t dense[4]={0};
    switch(kind){
    case 1:stored_exp_bytes(0);break;
    case 2:stored_exp_bytes(129);break;
    case 3:stored_exp_read(NULL,0,4);break;
    case 4:stored_exp_read(s,4,4);break;
    case 5:stored_exp_write(s,1,256,4);break;
    case 6:stored_exp_write(s,1,-1,4);break;
    case 7:stored_exp_import(s,dense,4,3);break;
    case 8:dense[1]=1;stored_exp_import(s,dense,4,4);break;
    case 9:dense[1]=dense[2]=255;stored_exp_import(s,dense,4,4);break;
    case 10:stored_exp_export(dense,4,s,5);break;
    case 11:stored_exp_copy(s,NULL,4,4);break;
    case 12:stored_exp_write(s,4,1,4);break;
    case 13:stored_exp_read(s,0,1);break;
    case 14:stored_exp_write(s,0,0,1);break;
    case 15:stored_exp_copy_vectors(s,s,4,4,SIZE_MAX/4+1);break;
    case 16:stored_exp_copy_vectors(s,s,4,3,1);break;
    case 17:stored_exp_copy_vectors(NULL,s,4,4,1);break;
    default:exit(4);
    }
    fputs("expected rejection missing\n",stderr);exit(3);
}
int main(int argc,char **argv){
    if(argc==3){if(strcmp(argv[1],"invalid")==0)invalid(atoi(argv[2]));else stage_case(5,0,0,atoi(argv[2]));return 2;}
    api_checks();hash_checks(5,0);hash_checks(5,1);hash_checks(9,0);
    for(unsigned i=0;i<12;i++)stage_case(i,i%2,0,0);
    stage_case(4,0,1,0);nonpower_row_case();
    puts("PASS api_vectors=2032 coordinate_values=256 comparison_pairs=2100 stages=13 nonpower_row_pairs=1");return 0;
}
