#!/usr/bin/env python3
import hashlib,json,os,subprocess
from pathlib import Path
R=Path(__file__).resolve().parent;S=R/'msolve-cc044551f8e202d00691990fd3fd0b1226a88ea2/src/neogb'
d=(S/'data.h').read_text();io=(S/'io.c').read_text();h=(S/'hash.c').read_text()
checked=d[d.index('typedef uint8_t exp_t;'):d.index('typedef int32_t deg_t;')]
read=io[io.index('static inline void set_exponent_vector('):io.index('/* note that depending on the input data')]
lcm=h[h.index('static inline hi_t get_lcm('):h.index('static inline hm_t *poly_to_matrix_row(')]
mult=h[h.index('static inline void insert_multiplied_poly_in_hash_table('):h.index('static inline void reinsert_in_hash_table(')]
pre=r'''
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <limits.h>
'''+checked+r'''
typedef uint32_t len_t,hi_t,hm_t,val_t;
typedef struct {len_t nv,evl,ebl,eld;exp_t **ev;} ht_t;
typedef struct {len_t nev;} md_t;
#define OFFSET 6
#define LENGTH 5
#define PARALLEL_HASHING 0
static exp_t captured[129];
static hi_t insert_in_hash_table(const exp_t *e,ht_t *h){memcpy(captured,e,h->evl*sizeof(exp_t));return 1;}
'''
post=r'''
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
     if(id==9)in[0]=-1;if(id==10)in[0]=256;if(id==11){in[0]=200;in[1]=100;}
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
'''
source=pre+read+lcm+mult+post
(R/'arithmetic_check.c').write_text(source)
cmd=['cc','-std=c11','-O1','-g','-Wall','-Wextra','-Wno-unused-parameter','-fsanitize=address,undefined',str(R/'arithmetic_check.c'),'-o',str(R/'arithmetic_check')]
subprocess.run(cmd,check=True)
q=subprocess.run([str(R/'arithmetic_check')],capture_output=True,text=True,timeout=15);(R/'arithmetic_check.log').write_text(q.stdout+q.stderr);assert q.returncode==0 and not q.stderr,q
faults=[]
for i in range(1,12):
 q=subprocess.run([str(R/'arithmetic_check'),str(i)],capture_output=True,text=True,timeout=10,env=dict(os.environ,ASAN_OPTIONS='detect_leaks=0'))
 assert q.returncode==1 and 'Error: byte exponent/degree overflow.' in q.stderr and 'Sanitizer' not in q.stderr,(i,q)
 faults.append(dict(id=i,returncode=q.returncode,diagnostic=q.stderr.strip()))
report=dict(status='PASS',source_sha256=hashlib.sha256(source.encode()).hexdigest(),compiler_command=cmd,valid_add_sub_cases=65792,value_cases=256,overflow_rejections=faults,actual_functions=['checked_exp_value','checked_exp_add','checked_exp_sub','set_exponent_vector','get_lcm','insert_multiplied_poly_in_hash_table'],stubs=['insert_in_hash_table captures vector; does not test lookup/allocation'],sanitizers='ASan+UBSan')
(R/'arithmetic_check.json').write_text(json.dumps(report,indent=2)+'\n');print('PASS arithmetic and11 pre-narrowing failures')
