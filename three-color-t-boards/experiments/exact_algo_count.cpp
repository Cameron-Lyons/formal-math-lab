// Reproducible exact bounded-prefix search, independent of earlier searches.
// Compile: g++ -O3 -std=c++23 -Wall -Wextra -Wpedantic -Werror experiments/exact_algo_count.cpp -o /tmp/tboard-count
// Full count: tboard-count --colors 2 --rows 5
// Prefix interval: --split-cells K --begin B --end E (base-q codes [B,E)).
// Any timeout is explicitly INCOMPLETE; counts are never extrapolated.
#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <string>
using U128=__uint128_t;
struct Config {int q=3,h=4,split=0;uint64_t begin=0,end=1;double seconds=0;std::string prefix;};
std::string dec(U128 x){std::string s;do{s.push_back('0'+x%10);x/=10;}while(x);std::reverse(s.begin(),s.end());return s;}
uint64_t number(const std::string &s){size_t n=0;auto x=std::stoull(s,&n);if(n!=s.size())throw std::runtime_error("invalid integer");return x;}
struct Count {
 Config c;std::array<int,100> a{},wt{},roles{};std::array<std::array<int,3>,4> hist{};
 uint64_t nodes=0;U128 answers=0;bool timeout=false,full=false;std::chrono::steady_clock::time_point started;
 Count(Config x):c(x),full(x.h==x.q*x.q+1){
  wt.fill(-1);
  for(int r=1;r<c.h;++r)for(int j=0;j<2*r-1;++j){
   int v[4]={(r-1)*(r-1)+j,r*r+j,r*r+j+1,r*r+j+2};wt[v[3]]=v[0];
   for(int k=0;k<4;++k)roles[v[k]]|=1<<k;
  }
  started=std::chrono::steady_clock::now();
 }
 bool fits(int p,int color) const {
  if(!full)return true;
  for(int k=0;k<4;++k)if((roles[p]>>k&1)&&hist[k][color]>=c.q*c.q*c.q)return false;
  return true;
 }
 void add(int p,int color,int step){if(full)for(int k=0;k<4;++k)if(roles[p]>>k&1)hist[k][color]+=step;}
 void dfs(int p,U128 used){
  if((++nodes&0xfffff)==0&&c.seconds>0&&std::chrono::duration<double>(std::chrono::steady_clock::now()-started).count()>=c.seconds){timeout=true;return;}
  if(p==c.h*c.h){++answers;return;}
  int base=wt[p]<0?0:((a[wt[p]]*c.q+a[p-2])*c.q+a[p-1])*c.q;
  for(int color=0;color<c.q;++color){
   U128 bit=wt[p]<0?0:U128(1)<<(base+color);
   if((used&bit)||!fits(p,color))continue;
   a[p]=color;add(p,color,1);dfs(p+1,used|bit);add(p,color,-1);
   if(timeout)return;
  }
 }
 bool load(uint64_t code){
  for(auto &row:hist)row.fill(0);
  if(c.prefix.empty()){
   for(int p=c.split-1;p>=0;--p){a[p]=code%c.q;code/=c.q;}
  }else{
   for(int p=0;p<c.split;++p)a[p]=c.prefix[p]-'0';
  }
  U128 used=0;
  for(int p=0;p<c.split;++p){
   if(!fits(p,a[p]))return false;
   add(p,a[p],1);
   if(wt[p]>=0){int v=((a[wt[p]]*c.q+a[p-2])*c.q+a[p-1])*c.q+a[p];U128 bit=U128(1)<<v;if(used&bit)return false;used|=bit;}
  }
  dfs(c.split,used);return true;
 }
};
int main(int argc,char**argv){try{
 Config c;bool end_set=false;
 for(int i=1;i<argc;i+=2){if(i+1==argc)throw std::runtime_error("options need values");std::string k=argv[i],v=argv[i+1];
  if(k=="--colors")c.q=number(v);else if(k=="--rows")c.h=number(v);else if(k=="--split-cells")c.split=number(v);
  else if(k=="--begin")c.begin=number(v);else if(k=="--end"){c.end=number(v);end_set=true;}
  else if(k=="--seconds")c.seconds=std::stod(v);else if(k=="--prefix")c.prefix=v;else throw std::runtime_error("unknown option: "+k);
 }
 if(c.q<2||c.q>3||c.h<1||c.h>c.q*c.q+1||c.split<0||c.split>c.h*c.h||c.seconds<0)throw std::runtime_error("invalid dimensions or time budget");
 if(!c.prefix.empty()){
  if(c.split||c.begin||end_set)throw std::runtime_error("prefix cannot be combined with interval options");
  c.split=c.prefix.size();if(c.split>c.h*c.h)throw std::runtime_error("prefix too long");
  for(char x:c.prefix)if(x<'0'||x>='0'+c.q)throw std::runtime_error("invalid prefix digit");
  c.begin=0;c.end=1;end_set=true;
 }
 uint64_t extent=1;
 if(c.prefix.empty())for(int p=0;p<c.split;++p){if(extent>std::numeric_limits<uint64_t>::max()/c.q)throw std::runtime_error("split exceeds 64-bit prefix encoding");extent*=c.q;}
 if(!end_set)c.end=extent;
 if(c.begin>c.end||c.end>extent)throw std::runtime_error("invalid prefix interval");
 Count s(c);uint64_t next=c.begin,valid=0;U128 complete=0;
 for(;next<c.end;++next){auto previous=s.answers;if(s.load(next))++valid;if(s.timeout){s.answers=previous;break;}complete=s.answers;}
 std::cout<<"status="<<(s.timeout?"INCOMPLETE":"COMPLETE")<<" colors="<<c.q<<" rows="<<c.h<<" split_cells="<<c.split
  <<" begin="<<c.begin<<" requested_end="<<c.end<<" completed_end="<<next<<" exact_count_completed_interval="<<dec(complete)
  <<" prefix="<<(c.prefix.empty()?"none":c.prefix)
  <<" nodes="<<s.nodes<<" valid_prefixes_visited="<<valid<<" elapsed="<<std::chrono::duration<double>(std::chrono::steady_clock::now()-s.started).count()<<"\n";
 return s.timeout?1:0;
 }catch(const std::exception&e){std::cerr<<e.what()<<"\n";return 2;}}
