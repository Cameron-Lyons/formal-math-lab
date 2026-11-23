// Exact fixed-point counts for reflection and reflected transposition.
// Intended only for small caps (at most five rows), independent of full census.
#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <string>
using Bits=__uint128_t;
int q,h,perm[3],a[5][9];
uint64_t total;
void row(int r,Bits used);
void cells(int r,int j,Bits used){
 if(j>r){
  if(r>0)for(int k=0;k<2*r-1;++k){
   int code=((a[r-1][k]*q+a[r][k])*q+a[r][k+1])*q+a[r][k+2];
   Bits bit=Bits(1)<<code;if(used&bit)return;used|=bit;
  }
  if(r+1==h)++total;else row(r+1,used);
  return;
 }
 for(int c=0;c<q;++c){
  if(j==r&&c!=perm[c])continue;
  a[r][j]=c;a[r][2*r-j]=perm[c];cells(r,j+1,used);
 }
}
void row(int r,Bits used){cells(r,0,used);}
int main(int argc,char**argv){
 q=argc>1?std::stoi(argv[1]):3;h=argc>2?std::stoi(argv[2]):5;
 if(q<2||q>3||h<1||h>5)return 2;
 for(int kind=0;kind<2;++kind){
  for(int c=0;c<q;++c)perm[c]=c;
  if(kind)std::swap(perm[q-1],perm[q-2]);
  total=0;row(0,0);
  std::cout<<"colors="<<q<<" rows="<<h<<" transform="<<(kind?"transposition_reflection":"reflection")<<" fixed="<<total<<"\n";
 }
}
