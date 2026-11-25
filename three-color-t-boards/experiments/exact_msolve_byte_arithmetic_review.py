#!/usr/bin/env python3
"""Independent sanitizer tests of the exact byte source's arithmetic routines."""

import hashlib
import json
import os
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
SOURCE = (
    HERE
    / "exact_msolve_byte_exponent_tools/msolve-cc044551f8e202d00691990fd3fd0b1226a88ea2/src/neogb"
)


def extract(text, start, end):
    return text[text.index(start) : text.index(end, text.index(start))]


def main():
    data = (SOURCE / "data.h").read_text()
    io = (SOURCE / "io.c").read_text()
    hash_source = (SOURCE / "hash.c").read_text()
    snippets = [
        extract(data, "typedef uint8_t exp_t;", "typedef int32_t deg_t;"),
        extract(
            io,
            "static inline void set_exponent_vector(",
            "/* note that depending on the input data",
        ),
        extract(
            hash_source,
            "static inline hi_t get_lcm(",
            "static inline hm_t *poly_to_matrix_row(",
        ),
        extract(
            hash_source,
            "static inline void insert_multiplied_poly_in_hash_table(",
            "static inline void reinsert_in_hash_table(",
        ),
    ]
    prefix = r"""
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <limits.h>
"""
    types = r"""
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
"""
    tests = r"""
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
"""
    content = (
        prefix
        + snippets[0]
        + types
        + '\n#pragma GCC diagnostic push\n#pragma GCC diagnostic ignored "-Wunused-parameter"\n'
        + "".join(snippets[1:])
        + "\n#pragma GCC diagnostic pop\n"
        + tests
    )
    source = HERE / "exact_msolve_byte_arithmetic_review.c"
    binary = HERE / "exact_msolve_byte_arithmetic_review.bin"
    source.write_text(content)
    command = [
        "cc",
        "-std=c23",
        "-O1",
        "-g",
        "-Wall",
        "-Wextra",
        "-Wpedantic",
        "-Werror",
        "-fsanitize=address,undefined",
        str(source),
        "-o",
        str(binary),
    ]
    subprocess.run(command, check=True)
    good = subprocess.run(
        [str(binary)], capture_output=True, text=True, timeout=20, check=False
    )
    (HERE / "exact_msolve_byte_arithmetic_review.log").write_text(
        good.stdout + good.stderr
    )
    assert good.returncode == 0 and not good.stderr, good
    failures = []
    for case in range(14):
        result = subprocess.run(
            [str(binary), str(case)],
            capture_output=True,
            text=True,
            timeout=5,
            env=dict(os.environ, ASAN_OPTIONS="detect_leaks=0"),
            check=False,
        )
        assert (
            result.returncode == 1
            and result.stderr == "Error: byte exponent/degree overflow.\n"
        ), (case, result)
        failures.append(
            {
                "case": case,
                "returncode": result.returncode,
                "diagnostic": result.stderr.strip(),
            }
        )
    report = {
        "status": "PASS",
        "compiler_command": command,
        "sanitizers": "ASan+UBSan",
        "C_source_sha256": hashlib.sha256(content.encode()).hexdigest(),
        "extracted_source_files_sha256": {
            p: hashlib.sha256((SOURCE / p).read_bytes()).hexdigest()
            for p in ("data.h", "io.c", "hash.c")
        },
        "valid_arithmetic_cases": 65792,
        "random_three_function_cases": 1200,
        "boundary_LCM_degrees": [6, 255],
        "overflow_and_underflow_failures": failures,
        "insertion_stub": "Captures vectors only; no allocator/probing claim",
        "full_board_solver_runs": 0,
    }
    (HERE / "exact_msolve_byte_arithmetic_review_results.json").write_text(
        json.dumps(report, indent=2) + "\n"
    )
    print(good.stdout.strip(), ";14 explicit pre-narrowing failures")


if __name__ == "__main__":
    main()
