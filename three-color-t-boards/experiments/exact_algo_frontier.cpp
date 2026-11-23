// Exact prefix transfer-state census: all labeled prefixes with apex 0.
// A state consists of last row and set of already used ordered T patterns.
#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <iostream>
#include <vector>
using u128=__uint128_t;
int q=3, h=4, a[100], wt[100];
uint64_t nodes=0, completions=0;
std::vector<u128> states;
void dfs(int p, u128 used){
 ++nodes;
 if(p==h*h){
  ++completions;
  uint32_t w=0;for(int i=(h-1)*(h-1);i<p;++i)w=q*w+a[i];
  states.push_back((used<<32)|w);
  return;
 }
 bool window=p>=3&&wt[p]>=0;
 int base=window?((a[wt[p]]*q+a[p-2])*q+a[p-1])*q:0;
 for(int c=0;c<q;++c){
  u128 bit=window?u128(1)<<(base+c):0;
  if(used&bit)continue;
  a[p]=c;dfs(p+1,used|bit);
 }
}
int main(int argc,char**argv){
 if(argc>1)q=std::stoi(argv[1]);
 if(argc>2)h=std::stoi(argv[2]);
 if(q<2||q>3||h<1||h>(q==3?4:5)){std::cerr<<"Supported census sizes: binary at most 5 rows; ternary at most 4 rows.\n";return 2;}
 std::fill(wt,wt+100,-1);
 for(int r=1;r<h;++r)for(int j=0;j<2*r-1;++j)wt[r*r+j+2]=(r-1)*(r-1)+j;
 auto t=std::chrono::steady_clock::now();dfs(1,0);
 std::sort(states.begin(),states.end());
 uint64_t unique=0,maxmult=0,merged=0;std::array<uint64_t,100> hist{};
 for(size_t i=0;i<states.size();){size_t j=i+1;while(j<states.size()&&states[j]==states[i])++j;
 ++unique;maxmult=std::max(maxmult,uint64_t(j-i));merged+=j-i>1;hist[std::min(size_t(99),j-i)]++;i=j;}
 std::cout<<"q="<<q<<" rows="<<h<<" apex=0 nodes="<<nodes<<" prefixes="<<completions<<" states="<<unique<<" max_multiplicity="<<maxmult<<" repeated_states="<<merged<<" elapsed="<<std::chrono::duration<double>(std::chrono::steady_clock::now()-t).count()<<"\n";
 for(size_t i=1;i<hist.size();++i)if(hist[i])std::cout<<"multiplicity "<<i<<" states "<<hist[i]<<"\n";
}
